# Independent toy index calculus, m=2, brute-force oracle.
import random, sys, math
import numpy as np
from linalg import elim, val, elim_transform, span_size_log
STATS = []
SPARE = 12
from math import gcd

O = None
def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True
def factor(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d,0)+1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n,0)+1
    return f

class Curve:
    def __init__(s, p, A, B):
        s.p, s.A, s.B = p, A, B
        s.sq = {}
        for y in range(p): s.sq.setdefault(y*y % p, []).append(y)
        s.pts = [(x, y) for x in range(p) for y in s.sq.get((x**3 + A*x + B) % p, [])]
        s.N = len(s.pts) + 1
    def add(s, P, Q):
        if P is O: return Q
        if Q is O: return P
        p = s.p
        (x1,y1),(x2,y2) = P,Q
        if x1 == x2:
            if (y1 + y2) % p == 0: return O
            lam = (3*x1*x1 + s.A) * pow(2*y1, -1, p) % p
        else:
            lam = (y2-y1) * pow(x2-x1, -1, p) % p
        x3 = (lam*lam - x1 - x2) % p
        return (x3, (lam*(x1-x3) - y1) % p)
    def neg(s, P): return O if P is O else (P[0], (-P[1]) % s.p)
    def mul(s, k, P):
        R = O
        Q = P
        while k:
            if k & 1: R = s.add(R, Q)
            Q = s.add(Q, Q); k >>= 1
        return R
    def rand_pt(s, rng):
        while True:
            x = rng.randrange(s.p)
            ys = s.sq.get((x**3 + s.A*x + s.B) % s.p)
            if ys and (ys[0] != 0 or rng.random() < .5): return (x, rng.choice(ys))
    def order(s, P, fN):
        o = s.N
        for l in fN:
            while o % l == 0 and s.mul(o//l, P) is O: o //= l
        return o

def subgroup_size(C, gens):
    S = {O}; fr = [O]
    gens = [g for g in gens if g is not O]
    while fr:
        nf = []
        for a in fr:
            for g in gens:
                b = C.add(a, g)
                if b not in S: S.add(b); nf.append(b)
        fr = nf
    return len(S)

def run_instance(C, P, Q, rng, fN, verbose=False, maxrounds=40):
    p, N = C.p, C.N
    X = math.isqrt(p)
    rounds = 0
    while rounds < maxrounds:
        rounds += 1
        u = rng.randrange(1, p)
        u2 = u*u % p
        Fu = [Pt for Pt in C.pts if (u2*Pt[0]) % p <= X]
        f = len(Fu)
        if f < 6: continue
        idx = {Pt: i for i, Pt in enumerate(Fu)}
        B1, B2 = C.rand_pt(rng), C.rand_pt(rng)
        Xs = [B1, B2, P, Q]
        Nr = f + 12
        rows = []; avec = []; tries = 0
        while len(rows) < Nr and tries < 60*Nr:
            tries += 1
            a = [rng.randrange(N) for _ in range(4)]
            R = O
            for aj, Xj in zip(a, Xs): R = C.add(R, C.mul(aj, Xj))
            if R is O: continue
            dec = None
            for P1 in Fu:                      # deterministic oracle: first generic pair
                P2 = C.add(R, C.neg(P1))
                if P2 in idx and P2[0] != P1[0]:
                    dec = (P1, P2); break
            if dec is None: continue
            e = [0]*f
            e[idx[dec[0]]] += 1; e[idx[dec[1]]] += 1
            rows.append(e + a); avec.append(a)
        if len(rows) < Nr: continue
        # linear algebra per prime power; row layout [E | a1 a2 | a3 a4]
        dl = {}; ok = True; diag = []
        for l, v in fN.items():
            q = l**v
            M = np.array(rows, dtype=np.int64) % q
            # first stage: kill E-columns -> generators of projected relation lattice (4 cols)
            Gt, _ = elim(M, f, l, v)
            G4 = Gt[:, f:]
            # size check against true K_l
            cl = N // q
            cinv = pow(cl, -1, q)
            pis = [C.mul(cl*cinv, Xj) for Xj in Xs]
            Hl = subgroup_size(C, pis)
            logK = 4*v - round(math.log(Hl, l))
            _, ks = elim(G4, 4, l, v)
            logS = sum(v-k for k in ks)
            full = (logS == logK)
            # second stage: kill cols 0,1 then find unit in col 3
            G2, _ = elim(G4, 2, l, v)
            found = None
            for r in G2.tolist():
                if r[3] % l != 0:
                    found = (-r[2] * pow(r[3], -1, q)) % q; break
            Lam = elim_transform(M[:, :f], l, v)          # Lemma 3 literal: 12 rows of Lambda
            mu12 = (Lam[:SPARE] @ M[:, f:]) % q
            _, ks12 = elim(mu12, 4, l, v)
            STATS.append((l, v, sum(v-k for k in ks12) == logK, Lam.shape[0]))
            diag.append((q, full, found is not None))
            if found is None: ok = False; break
            dl[q] = found
        if not ok:
            if verbose: print("   round", rounds, "fail", diag)
            continue
        # CRT
        d = 0
        for l, v in fN.items():
            q = l**v; Mq = N // q
            d = (d + dl[q] * Mq * pow(Mq, -1, q)) % N
        if C.mul(d, P) == Q: return d, rounds, diag
        if verbose: print("   round", rounds, "CRT verify failed")
    return None, rounds, None
