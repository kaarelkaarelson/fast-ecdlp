#!/usr/bin/env python3
"""Sparse nonsingular solve mod l^v by Wiedemann (Berlekamp-Massey) + Dixon lifting; counts matvecs.
Solves  x B = r  (B f x f sparse integer, det B != 0 mod l) i.e. B^T x^T = r^T.   Used for the cost check of Theorem 1."""
import random, sys, time

def bm(seq, l):
    """Berlekamp-Massey over F_l.  Returns connection poly C (list, C[0]=1) of minimal length L."""
    C = [1]; Bp = [1]; L = 0; m = 1; b = 1
    for n in range(len(seq)):
        dlt = seq[n]
        for i in range(1, L + 1):
            if i < len(C): dlt = (dlt + C[i] * seq[n - i]) % l
        if dlt % l == 0: m += 1; continue
        T = C[:]; coef = dlt * pow(b, -1, l) % l
        if len(C) < len(Bp) + m: C += [0] * (len(Bp) + m - len(C))
        for i, x in enumerate(Bp): C[i + m] = (C[i + m] - coef * x) % l
        if 2 * L <= n: L = n + 1 - L; Bp = T; b = dlt; m = 1
        else: m += 1
    return C[:L + 1], L

class Sparse:
    def __init__(s, rows, f):  # rows: list of dict col->val (integers); we store A = B^T acting on column vectors: (A y)_j = sum_i B[i][j] y_i
        s.f = f; s.cols = [[] for _ in range(f)]
        for i, r in enumerate(rows):
            for j, x in r.items(): s.cols[j].append((i, x))   # A[j][i] = B[i][j]
        s.matvecs = 0
    def apply(s, y, mod):   # A y mod 'mod'
        s.matvecs += 1
        return [sum(x * y[i] for i, x in s.cols[j]) % mod if mod else sum(x * y[i] for i, x in s.cols[j]) for j in range(s.f)]

def wiedemann_solve_modl(A, b, l, rng):
    """Solve A y = b over F_l, A nonsingular.  Returns y or None."""
    f = A.f
    u = [rng.randrange(l) for _ in range(f)]
    vecs = [b[:]]; cur = b[:]; seq = [sum(x * y for x, y in zip(u, cur)) % l]
    for i in range(1, 2 * f):
        cur = A.apply(cur, l); seq.append(sum(x * y for x, y in zip(u, cur)) % l)
        if i <= f: vecs.append(cur)
    C, L = bm(seq, l)            # C(z) = 1 + c1 z + ... ; sum_{i=0}^L C[i] s_{n-i} = 0  => polynomial in A annihilates b: sum C[i] A^{L-i} b = 0 w.h.p.
    # min poly g(z) = sum_{i} C[i] z^{L-i}; constant term of g is C[L]
    if C[L] % l == 0: return None
    # y = -(1/C[L]) * sum_{i<L} C[i] A^{L-1-i} b
    y = [0] * f
    for i in range(L):
        c = C[i]
        v = vecs[L - 1 - i]
        y = [(yy + c * vv) % l for yy, vv in zip(y, v)]
    inv = pow(C[L], -1, l)
    return [(-inv * yy) % l for yy in y]

def dixon_solve(rows, f, r, l, v, rng):
    """Solve x B = r mod l^v.  Returns x (list) and matvec count."""
    A = Sparse(rows, f); mod = l ** v
    res = [x % mod for x in r]; sol = [0] * f; pw = 1
    for k in range(v):
        rhs = [(x // pw) % l for x in res] if k else [x % l for x in res]
        y = None
        for _ in range(5):
            y = wiedemann_solve_modl(A, rhs, l, rng)
            if y is not None and A.apply(y, l) == rhs: break   # Las Vegas check (one extra matvec)
            y = None
        if y is None: return None, A.matvecs
        sol = [(s + pw * yy) % mod for s, yy in zip(sol, y)]
        Ay = A.apply(y, None)  # exact integer matvec
        res = [(rr - pw * a) % mod for rr, a in zip(res, Ay)]
        # res is divisible by l^{k+1}
        assert all(x % (l ** (k + 1)) == 0 for x in res)  # residual divisible by l^{k+1}
        pw *= l
    return sol, A.matvecs

def primes_above(n):
    def isp(q):
        i = 2
        while i * i <= q:
            if q % i == 0: return False
            i += 1
        return True
    while not isp(n): n += 1
    return n

if __name__ == "__main__":
    rng = random.Random(7); allok = True
    for f in (100, 200, 400, 800):
        mwt = 5
        l = primes_above(4 * f * f + 10); v = 2
        # B = T' - M I with T' random sparse row weight m (entries counts), M random
        M = rng.randrange(1, 4 * f)
        rows = []
        for i in range(f):
            r = {}
            for _ in range(mwt - 1): j = rng.randrange(f); r[j] = r.get(j, 0) + 1
            r[i] = r.get(i, 0) - M
            rows.append(r)
        rhs = [rng.randrange(l ** v) for _ in range(f)]
        t = time.time(); sol, mv = dixon_solve(rows, f, rhs, l, v, rng); dt = time.time() - t
        if sol is None: print(f, "singular/failed"); allok = False; continue
        # verify x B = r
        chk = [0] * f
        for i, r in enumerate(rows):
            for j, x in r.items(): chk[j] = (chk[j] + sol[i] * x) % (l ** v)
        good = chk == [x % (l ** v) for x in rhs]
        allok &= good
        print(f"f={f} l={l} v={v}: verified={good}; matvecs={mv} = {mv/f:.2f} f; time {dt:.1f}s")
    print("PASS wied_dixon" if allok else "FAIL wied_dixon")
