#!/usr/bin/env python3
"""Toy index calculus for ECDLP on E(F_p) of ARBITRARY group structure (m = 2).
Brute-force decomposition oracle in place of the engine.  Implements the algorithm of PROOF.md Part A:
  - dilation u (random isomorphic model), factor base F_u = {P != O : u^2 x(P) mod p <= X}, X = ceil(sqrt p)-1
  - sample a in (Z/N)^4 uniform, R = a1 B1 + a2 B2 + a3 P + a4 Q   (B1,B2 random points; R uniform on <B1,B2,P,Q>)
  - oracle D(R) = first ordered generic pair (P1,P2) in F_u^2, x1 != x2, P1+P2 = R (deterministic in R)
  - rows e_i (columns = points of F_u), a_i in (Z/N)^4;  rows = f' + 12
  - for each prime l | N, v = v_l(N): Smith-type elimination of E over Z/l^v keeping the transformation;
    non-pivot rows of the transformation = surjective set of s >= 12 kernel vectors; mu_j = Lambda_j A (mod l^v)
    are iid uniform on the relation lattice K_l of (B1,B2,P,Q);   Howell form to find (0,0,d',-1) in K_l
  - CRT over l | N, verify d''P == Q.
Only N and its factorisation are used (no group structure).
"""
import sys, random, math
import numpy as np

# ---------------- curve arithmetic ----------------
class Curve:
    def __init__(s, p, A, B):
        s.p, s.A, s.B = p, A % p, B % p
    def add(s, P, Q):
        p = s.p
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1 + s.A) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    def neg(s, P):
        return None if P is None else (P[0], (-P[1]) % s.p)
    def mul(s, k, P):
        R = None
        if k < 0: k, P = -k, s.neg(P)
        while k:
            if k & 1: R = s.add(R, P)
            P = s.add(P, P); k >>= 1
        return R
    def points(s):
        if hasattr(s, '_pts'): return s._pts
        s._pts = s._points()
        return s._pts
    def _points(s):
        p = s.p
        sq = {}
        for y in range(p): sq.setdefault(y * y % p, []).append(y)
        pts = []
        for x in range(p):
            for y in sq.get((x ** 3 + s.A * x + s.B) % p, []): pts.append((x, y))
        return pts

def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def order(C, P, N, fN):
    o = N
    for l in fN:
        while o % l == 0 and C.mul(o // l, P) is None: o //= l
    return o

def structure(C, N, fN, rng, samples=60):
    pts = C.points()
    e = 1
    for _ in range(samples):
        P = rng.choice(pts)
        e = e * order(C, P, N, fN) // math.gcd(e, order(C, P, N, fN))
    return e  # exponent (w.h.p.); G ~ Z/(N/e) x Z/e  after reorder: n1 = e, n2 = N/e

# ---------------- local-ring linear algebra ----------------
def val(x, l, v):
    if x % (l ** v) == 0: return v
    k = 0
    while x % l == 0: x //= l; k += 1
    return k

def kernel_free_rows(E, l, v):
    """E: (Nr x f) int array mod l^v.  Returns Lambda (s x Nr): rows of the unimodular transformation
    belonging to non-pivot rows (each satisfies Lambda_j E == 0 mod l^v), and the number of pivots."""
    M = l ** v
    Nr, f = E.shape
    W = np.concatenate([E % M, np.eye(Nr, dtype=np.int64)], axis=1)  # [E | U]
    active_r = np.ones(Nr, bool); active_c = np.ones(f, bool)
    pivots = 0
    while True:
        sub = W[np.ix_(active_r, active_c)] if active_r.any() and active_c.any() else None
        if sub is None or not sub.any(): break
        k0 = None
        for k in range(v):
            if (sub % (l ** (k + 1)) != 0).any(): k0 = k; break
        lk = l ** k0
        mask = (sub % (l ** (k0 + 1)) != 0) & (sub % lk == 0)
        ri, ci = np.argwhere(mask)[0]
        rr = np.where(active_r)[0][ri]; cc = np.where(active_c)[0][ci]
        pv = int(W[rr, cc]); w = pv // lk
        winv = pow(w, -1, M)
        others = np.where(active_r)[0]; others = others[others != rr]
        q = ((W[others, cc] // lk) * winv) % M
        W[others] = (W[others] - np.outer(q, W[rr])) % M
        active_r[rr] = False; active_c[cc] = False; pivots += 1
    nonp = np.where(active_r)[0]
    return W[nonp, f:], pivots

def howell_solve(mus, l, v):
    """mus: list of 4-vectors over Z/l^v generating K.  Return d' with (0,0,d',-1) in span, or None."""
    M = l ** v
    rows = [list(r) for r in mus]
    for col in (0, 1):
        best = None
        for i, r in enumerate(rows):
            if r[col] % M and (best is None or val(r[col], l, v) < val(rows[best][col], l, v)): best = i
        if best is None: continue
        pr = rows.pop(best); k = val(pr[col], l, v); lk = l ** k
        winv = pow(pr[col] // lk, -1, M)
        new = []
        for r in rows:
            q = (r[col] // lk) * winv % M if r[col] % M else 0
            new.append([(r[t] - q * pr[t]) % M for t in range(4)])
        ann = [(pr[t] * l ** (v - k)) % M for t in range(4)]
        new.append(ann)  # Howell annihilator row (zero in col)
        rows = new
    for r in rows:
        if r[0] % M or r[1] % M: raise AssertionError("howell stage-1 failure")
        if r[3] % l:  # unit in last coordinate
            s = (-pow(r[3], -1, M)) % M
            return (s * r[2]) % M
    return None

def crt(res, mods):
    x, m = 0, 1
    for r, q in zip(res, mods):
        t = ((r - x) * pow(m, -1, q)) % q
        x += m * t; m *= q
    return x % m, m

# ---------------- the algorithm ----------------
def run(C, P, Q, N, fN, rng, extra=12, minimal_mod=False, verbose=False, max_restarts=50, B_given=None):
    p = C.p
    X = math.isqrt(p - 1) + 1 - 1  # ceil(sqrt p) - 1  (p prime non-square: = isqrt(p))
    X = math.isqrt(p)
    allpts = C.points()
    stats = {"restarts": 0, "samples": 0, "accepted": 0}
    for rs in range(max_restarts):
        stats["restarts"] += 1
        u = rng.randrange(1, p); u2 = u * u % p
        F = [P_ for P_ in allpts if (u2 * P_[0]) % p <= X]
        idx = {P_: i for i, P_ in enumerate(F)}
        D = {}
        for i, P1 in enumerate(F):
            for j, P2 in enumerate(F):
                if P1[0] != P2[0]:
                    R = C.add(P1, P2)
                    if R not in D: D[R] = (i, j)
        f = len(F); Nr = f + extra
        B = B_given if B_given else (rng.choice(allpts), rng.choice(allpts))
        Xs = [B[0], B[1], P, Q]
        rows_e, rows_a = [], []
        cap = 400 * Nr; tries = 0
        while len(rows_e) < Nr and tries < cap:
            tries += 1
            a = [rng.randrange(N) for _ in range(4)]
            R = None
            for t in range(4): R = C.add(R, C.mul(a[t], Xs[t]))
            stats["samples"] += 1
            if R in D:
                i, j = D[R]; e = np.zeros(f, np.int64); e[i] += 1; e[j] += 1
                rows_e.append(e); rows_a.append(a); stats["accepted"] += 1
        if len(rows_e) < Nr: continue  # cap hit: restart with new u, B
        E = np.array(rows_e); A = np.array(rows_a, dtype=np.int64)
        res, mods = [], []
        ok = True
        for l, v in fN.items():
            M = l ** v
            Lam, piv = kernel_free_rows(E, l, v)
            if Lam.shape[0] < extra: ok = False; break
            Al = A % M
            mus = (Lam @ Al) % M
            # sanity (toy only): every mu is a relation of (B1,B2,P,Q) at l
            cof = N // M
            for mu in mus:
                S = None
                for t in range(4): S = C.add(S, C.mul(int(mu[t]), Xs[t]))
                assert C.mul(cof, S) is None, "mu not a relation"
            dl = howell_solve([list(map(int, r)) for r in mus], l, v)
            if dl is None: ok = False; break
            res.append(dl); mods.append(M)
        if not ok: continue
        d2, _ = crt(res, mods)
        if C.mul(d2, P) == Q:
            stats["f"] = f; stats["Nr"] = Nr; stats["cover"] = len(D) / N
            return d2, stats
    return None, stats

# ---------------- instance search ----------------
def classify(N, e):
    n1, n2 = e, N // e
    return n1, n2

PRIMES = [q for q in range(1000, 5000) if all(q % r for r in range(2, int(q ** .5) + 1))]

def find_instances(rng):
    inst = {}
    want = ["prime", "cyc_sqfree", "cyc_pp", "noncyc_sqfreeexp", "noncyc_pp"]
    tries = 0
    while len(inst) < len(want) and tries < 4000:
        tries += 1
        p = rng.choice(PRIMES)
        A, B = rng.randrange(p), rng.randrange(p)
        if (4 * A ** 3 + 27 * B * B) % p == 0: continue
        C = Curve(p, A, B)
        N = len(C.points()) + 1
        fN = factor(N)
        e = structure(C, N, fN, rng, 30)
        n1, n2 = classify(N, e)
        sq = lambda n: all(x == 1 for x in factor(n).values())
        if N == e:
            cat = "prime" if len(fN) == 1 and list(fN.values())[0] == 1 else ("cyc_sqfree" if sq(N) and len(fN) > 1 else ("cyc_pp" if not sq(N) else None))
        else:
            cat = "noncyc_sqfreeexp" if sq(n1) else "noncyc_pp"
        if cat in want and cat not in inst and (cat != "cyc_sqfree" or len(fN) >= 2):
            inst[cat] = (p, A, B, N, n1, n2)
    return inst

def pick_points(C, N, fN, e, rng, kind):
    pts = C.points()
    for _ in range(400):
        P = rng.choice(pts); o = order(C, P, N, fN)
        if kind == "gen" and o == e: return P, o
        if kind == "small" and o != e and o > 1 and o <= max(e // 2, 1): 
            if o == min(factor(e)) or o <= 6: return P, o
        if kind == "any": return P, o
    raise ValueError("no such point")

def main():
    global PRIMES
    lo, hi, seed = (int(a) for a in sys.argv[1:4]) if len(sys.argv) > 3 else (1000, 5000, 4747)
    PRIMES = [q for q in range(lo, hi) if all(q % r for r in range(2, int(q ** .5) + 1))]
    rng = random.Random(seed)
    inst = find_instances(rng)
    print("INSTANCES FOUND:")
    for k, v in inst.items(): print(f"  {k}: p={v[0]} A={v[1]} B={v[2]} N={v[3]}={factor(v[3])} exp={v[4]} (G ~ Z/{v[4]} x Z/{v[5]})")
    total = 0; good = 0
    for cat, (p, A, B, N, n1, n2) in inst.items():
        C = Curve(p, A, B); fN = factor(N)
        for kind in ("gen", "small", "any"):
            try: P, o = pick_points(C, N, fN, n1, rng, kind)
            except Exception as ex: continue
            if o == 1: continue
            for trial in range(2):
                d = rng.randrange(o)
                Q = C.mul(d, P)
                d2, st = run(C, P, Q, N, fN, rng)
                total += 1
                okk = d2 is not None and (d2 - d) % o == 0 and C.mul(d2, P) == Q
                good += okk
                # negative control: sampling only R = aP + bQ (inside H=<P>), coverage of H by the oracle at one dilation
                u = rng.randrange(1, p); u2 = u * u % p; X = math.isqrt(p)
                F = [P_ for P_ in C.points() if (u2 * P_[0]) % p <= X]
                Dk = {}
                for P1 in F:
                    for P2 in F:
                        if P1[0] != P2[0]: Dk[C.add(P1, P2)] = 1
                H = {None}; S = P
                while S is not None: H.add(S); S = C.add(S, P)
                covH = sum(1 for R in H if R in Dk) / len(H)
                print(f"[{cat}] p={p} N={N} G=Z/{n1}xZ/{n2} ord(P)={o}({kind}) d={d} -> d''={d2} mod ord: {None if d2 is None else d2 % o} "
                      f"{'OK' if okk else 'FAIL'}  restarts={st['restarts']} samples={st['samples']} acc={st['accepted']} "
                      f"cover(G)~{st.get('cover',0):.2f} cover(H=<P>) at one u={covH:.2f} |H|={len(H)}")
    print(f"SUMMARY: {good}/{total} instances recovered d correctly")
    print("PASS toy_ic" if good == total else "FAIL toy_ic")

if __name__ == "__main__":
    main()
