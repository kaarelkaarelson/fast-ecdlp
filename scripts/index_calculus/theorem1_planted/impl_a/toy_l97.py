#!/usr/bin/env python3
"""Toy: planted-diagonal index calculus for the exceptional prime (l^2 | N, l larger than f).
Brute-force oracle (all m-multiset sums of the factor base), deterministic first-found tuple.
Variant PLANT:  row i (i=1..f): R_i = a_i.X + M*F_i, row = e_{D(R_i)} - M e_i ; 12 extra ordinary rows.
                B = top f x f block; lambda_k = (-r_k B^{-1}, e_k) mod l^v;  mu_k = lambda_k . a.
Variant VANILLA: f+12 rows R = a.X (no planting); report delta = rank_Q(E) - rank_l(E).
Everything mod l^v is done with python ints (exact).
"""
import sys, random, math, itertools
from l47_base import Curve, factor, order, howell_solve, val

def mat_inv_mod_prime(B, l):
    n = len(B); A = [[B[i][j] % l for j in range(n)] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] % l), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]
        iv = pow(A[c][c], -1, l); A[c] = [x * iv % l for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] % l:
                t = A[r][c]; A[r] = [(x - t * y) % l for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]

def matmul(A, B, mod):
    Bt = list(zip(*B))
    return [[sum(x * y for x, y in zip(r, c)) % mod for c in Bt] for r in A]

def inv_mod_lv(B, l, v):
    """Newton/Hensel lift of the inverse mod l to mod l^v (exact)."""
    n = len(B); Y = mat_inv_mod_prime(B, l)
    if Y is None: return None
    mod = l
    for _ in range(v):  # at most v doublings suffice (generously)
        mod = min(mod * mod, l ** v)
        BY = matmul(B, Y, mod)
        T = [[(2 * (1 if i == j else 0) - BY[i][j]) % mod for j in range(n)] for i in range(n)]
        Y = matmul(Y, T, mod)
        if mod == l ** v: break
    chk = matmul(B, Y, l ** v)
    assert all(chk[i][j] == (1 if i == j else 0) for i in range(n) for j in range(n))
    return Y

def rank_mod_prime(rows, q):
    A = [[x % q for x in r] for r in rows]; rk = 0; ncol = len(A[0]) if A else 0
    for c in range(ncol):
        piv = next((r for r in range(rk, len(A)) if A[r][c]), None)
        if piv is None: continue
        A[rk], A[piv] = A[piv], A[rk]; iv = pow(A[rk][c], -1, q); A[rk] = [x * iv % q for x in A[rk]]
        for r in range(len(A)):
            if r != rk and A[r][c]:
                t = A[r][c]; A[r] = [(x - t * y) % q for x, y in zip(A[r], A[rk])]
        rk += 1
    return rk

BIGQ = (1 << 61) - 1

class Inst:
    def __init__(s, p, A, B, m, f_target, rng):
        s.C = Curve(p, A, B); s.p = p; s.m = m; s.rng = rng
        pts = s.C.points(); s.N = len(pts) + 1; s.fN = factor(s.N)
        # factor base: random negation-closed-free subset of f points (algebra only)
        s.fb = rng.sample(pts, f_target); s.f = f_target
        s.idx = {P: i for i, P in enumerate(s.fb)}
        # oracle: first multiset found for each sum
        s.D = {}
        for t in itertools.combinations_with_replacement(range(s.f), m):
            R = None
            for j in t: R = s.C.add(R, s.fb[j])
            s.D.setdefault(R, t)
        s.cover = len(s.D) / s.N

def gen_ok(inst, B1, B2):
    C = inst.C; seen = {None}; frontier = [None]
    # subgroup generated: BFS (group small)
    S = {None}; todo = [None]
    while todo:
        x = todo.pop()
        for g in (B1, B2):
            y = C.add(x, g)
            if y not in S: S.add(y); todo.append(y)
    return len(S) == inst.N

def sample_row(inst, X, M, i, Nmod):
    C = inst.C; rng = inst.rng
    Fi = C.mul(M, inst.fb[i]) if i is not None else None
    for _ in range(100000):
        a = [rng.randrange(Nmod) for _ in range(4)]
        R = Fi
        for aj, Xj in zip(a, X): R = C.add(R, C.mul(aj, Xj))
        if R in inst.D:
            return a, inst.D[R]
    raise RuntimeError("no decomposable R found")

def run_plant(inst, l, d, P, Q, M0, rng_M=None, verbose=False):
    C = inst.C; N = inst.N; v = inst.fN[l]; mod = l ** v; f = inst.f; m = inst.m; rng = inst.rng
    while True:
        B1, B2 = rng.choice(C.points()), rng.choice(C.points())
        if gen_ok(inst, B1, B2): break
    X = (B1, B2, P, Q)
    M = rng.randrange(M0)
    rows, tags = [], []
    for i in range(f + 12):
        a, t = sample_row(inst, X, M if i < f else 0, i if i < f else None, N)
        r = [0] * f
        for j in t: r[j] += 1
        if i < f: r[i] -= M
        rows.append(r); tags.append([x % mod for x in a])
    Bblk = [rows[i] for i in range(f)]
    Binv = inv_mod_lv(Bblk, l, v)
    if Binv is None: return ("singular", M, None)
    mus = []
    for k in range(12):
        rk = rows[f + k]
        top = [(-sum(rk[j] * Binv[j][i] for j in range(f))) % mod for i in range(f)]  # -r B^{-1}
        lam = top + [1 if q == k else 0 for q in range(12)]
        # sanity: lam . E == 0 mod l^v
        for col in range(f):
            assert sum(lam[i] * rows[i][col] for i in range(f + 12)) % mod == 0
        mu = [sum(lam[i] * tags[i][c] for i in range(f + 12)) % mod for c in range(4)]
        mus.append(mu)
    # Lemma 1 check: mu . X == 0 in the l-part
    cof = N // mod
    for mu in mus:
        R = None
        for aj, Xj in zip(mu, X): R = C.add(R, C.mul(aj * cof, Xj))
        assert R is None, "Lemma 1 violated"
    dd = howell_solve(mus, l, v)
    return ("ok", M, dd)

def delta_vanilla(inst, P, Q, l, rng, B12=None):
    C = inst.C; N = inst.N; f = inst.f
    while True:
        B1, B2 = rng.choice(C.points()), rng.choice(C.points())
        if gen_ok(inst, B1, B2): break
    X = (B1, B2, P, Q)
    rows = []
    for i in range(f + 12):
        a, t = sample_row(inst, X, 0, None, N)
        r = [0] * f
        for j in t: r[j] += 1
        rows.append(r)
    rQ = rank_mod_prime(rows, BIGQ); rl = rank_mod_prime(rows, l)
    return rQ, rl

def main(seed=97, trials=40):
    rng = random.Random(seed)
    cases = [(5107, 1730, 2656, 71), (5303, 1724, 2234, 73), (5303, 895, 4253, 73), (5309, 4807, 761, 73),
             (5483, 2826, 4260, 53), (5021, 880, 4274, 41)]
    tot = ok = sing = wrong = 0
    van_def = []
    for (p, A, B, l) in cases:
        for m, ft in ((4, 26),):
            inst = Inst(p, A, B, m, ft, rng)
            N = inst.N; fN = inst.fN; v = fN[l]
            # P of l-part order l^v (take random point, multiply by cofactor of non-l part to keep order l^v if possible)
            pts = inst.C.points()
            for _ in range(200):
                P = rng.choice(pts); o = order(inst.C, P, N, fN)
                if o % (l ** v) == 0: break
            else:
                print("no P with full l-part", p, l); continue
            d = rng.randrange(1, o)
            Q = inst.C.mul(d, P)
            cof = N // (l ** v)
            Pl, Ql = inst.C.mul(cof, P), inst.C.mul(cof, Q)
            ordl = l ** v
            M0 = max(2 * ft, 1)  # M uniform in [0, M0): M0 <= l required for distinct residues
            M0 = min(M0, l)
            nok = 0; nsing = 0; nbad = 0
            for tr in range(trials):
                res = run_plant(inst, l, d, P, Q, M0)
                tot += 1
                if res[0] == "singular": sing += 1; nsing += 1; continue
                dd = res[2]
                good = dd is not None and inst.C.mul(dd, Pl) == Ql
                if good: ok += 1; nok += 1
                else: wrong += 1; nbad += 1
            dl = [delta_vanilla(inst, P, Q, l, rng) for _ in range(trials)]
            defects = [a - b for a, b in dl]
            van_def += defects
            print(f"p={p} N={N}={fN} l={l} f={ft} m={m} cover={inst.cover:.2f} M0={M0}: PLANT ok {nok}/{trials} singular {nsing} wrong {nbad};"
                  f" VANILLA delta_l (rankQ-rank_l) hist {sorted(set(defects))} rankQ range {min(a for a,_ in dl)}-{max(a for a,_ in dl)}", flush=True)
    print(f"TOTAL planted: ok {ok}, singular-B {sing}, wrong {wrong} of {tot}")
    print("PASS toy_l97" if wrong == 0 and ok > 0 else "FAIL toy_l97")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 97, int(sys.argv[2]) if len(sys.argv) > 2 else 30)
