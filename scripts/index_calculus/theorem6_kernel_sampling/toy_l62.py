#!/usr/bin/env python3
"""Toy: kernel-SAMPLING procedure (no full dense Smith elimination of the relation matrix) for the
all-orders index calculus of l47_base.py (m = 2, brute-force oracle).  Own code except Curve/factor/order/howell_solve/crt
(from l47_base.py).

Paths per prime l | N, with v = v_l(e_B), e_B = lcm(ord B1, ord B2, ord P, ord Q):
  v == 1 (squarefree l-part of the exponent): FIELD path.  Vectors of the left kernel of E mod l.
        mode 'zsigma' : z = y - sigma(E^T y), y uniform, sigma = deterministic particular solver   (PROOF.md Lemma S2)
        mode 'rref'   : the raw structured (non-uniform) RREF kernel basis, in order                (tests "rank is enough", Lemma S1)
        mode 'unif'   : uniform combination of a kernel basis
  v >= 2: SCHUR path.  Recursive Schur complement: free kernel vectors of E over Z/l^v from a unit block B (invertible mod l),
        J = E22 - E21 B^{-1} E12 = l J', recurse on J' over Z/l^{v-1}   (PROOF.md Lemma S4).  Records the defect d_k per level.
  mode 'raw' (rows of Lambda) or 'mix' (random Z/l^v combinations of the rows).
Output per instance: recovered d, and the minimal number s* of kernel vectors (prefix of the stream) with which Howell finds d_l.
"""
import sys, math, random, collections
import numpy as np
from l47_base import Curve, factor, order, structure, howell_solve, crt, val

# ---------------------------------------------------------------- linear algebra over F_l
def rref_with_transform(E, l):
    """U E = R (RREF mod l); returns U (n x n), R, pivot columns."""
    n, f = E.shape
    W = np.concatenate([E % l, np.eye(n, dtype=np.int64)], axis=1)
    piv = []; r = 0
    for c in range(f):
        rows = np.nonzero(W[r:, c])[0]
        if len(rows) == 0: continue
        k = r + rows[0]
        if k != r: W[[r, k]] = W[[k, r]]
        W[r] = (W[r] * pow(int(W[r, c]), -1, l)) % l
        for i in range(n):
            if i != r and W[i, c]:
                W[i] = (W[i] - W[i, c] * W[r]) % l
        piv.append(c); r += 1
        if r == n: break
    return W[:, f:], W[:, :f], piv

class FieldKernel:
    def __init__(s, E, l):
        s.l = l; s.n, s.f = E.shape
        s.U, s.R, s.piv = rref_with_transform(E, l)
        s.r = len(s.piv)
        s.basis = s.U[s.r:]          # left kernel basis: rows with R-part 0  (dimension n - r)
    def sigma(s, b):
        """deterministic particular solution x of  x^T E = b^T  (b in rowspace), as a function of b only"""
        c = np.array([b[j] for j in s.piv], dtype=np.int64)
        x = (c @ s.U[:s.r]) % s.l
        return x
    def zsigma(s, rng, E):
        y = np.array([rng.randrange(s.l) for _ in range(s.n)], dtype=np.int64)
        b = (y @ E) % s.l
        x = s.sigma(b)
        z = (y - x) % s.l
        assert not ((z @ E) % s.l).any()
        return z
    def unif(s, rng):
        c = np.array([rng.randrange(s.l) for _ in range(s.basis.shape[0])], dtype=np.int64)
        return (c @ s.basis) % s.l

# ---------------------------------------------------------------- Schur recursion over Z/l^v
def rank_profile(Em, l):
    """complete pivoting mod l; returns pivot rows, pivot cols (the block E[rows][:,cols] is invertible mod l)."""
    A = Em % l; n, c = A.shape
    act_r = np.ones(n, bool); act_c = np.ones(c, bool); pr, pc = [], []
    while True:
        sub = A[np.ix_(act_r, act_c)] if act_r.any() and act_c.any() else None
        if sub is None or not sub.any(): break
        ri, ci = np.argwhere(sub)[0]
        rr = np.nonzero(act_r)[0][ri]; cc = np.nonzero(act_c)[0][ci]
        inv = pow(int(A[rr, cc]), -1, l)
        others = np.nonzero(act_r)[0]; others = others[others != rr]
        q = (A[others, cc] * inv) % l
        A[others] = (A[others] - np.outer(q, A[rr])) % l
        act_r[rr] = False; act_c[cc] = False; pr.append(rr); pc.append(cc)
    return pr, pc

def inv_mod(B, l, v):
    M = l ** v; r = B.shape[0]
    W = np.concatenate([B % M, np.eye(r, dtype=np.int64)], axis=1)
    for c in range(r):
        cand = [i for i in range(c, r) if W[i, c] % l]
        k = cand[0]
        if k != c: W[[c, k]] = W[[k, c]]
        W[c] = (W[c] * pow(int(W[c, c]), -1, M)) % M
        for i in range(r):
            if i != c and W[i, c]: W[i] = (W[i] - W[i, c] * W[c]) % M
    return W[:, r:]

def schur_free(E, l, v, levels=None, depth=0):
    """Rows Lambda (s x n) over Z/l^v with Lambda E == 0 and Lambda mod l of full row rank s = n - sum_k r_k.
    levels: list of (depth, n, c, r, defect) appended."""
    n, c = E.shape; M = l ** v
    if levels is None: levels = []
    if v == 0 or c == 0 or n == 0:
        levels.append((depth, n, c, 0, c))
        return np.eye(n, dtype=np.int64), levels
    pr, pc = rank_profile(E, l)
    r = len(pr)
    levels.append((depth, n, c, r, c - r))
    rr = [i for i in range(n) if i not in set(pr)]; cr = [j for j in range(c) if j not in set(pc)]
    if r == 0:
        J = E[np.ix_(rr, cr)] % M
        D = np.zeros((len(rr), 0), np.int64); Binv = np.zeros((0, 0), np.int64)
    else:
        B = E[np.ix_(pr, pc)] % M
        Binv = inv_mod(B, l, v)
        D = E[np.ix_(rr, pc)] % M
        Cm = E[np.ix_(pr, cr)] % M
        J = (E[np.ix_(rr, cr)] - D @ ((Binv @ Cm) % M)) % M
    assert not (J % l).any(), "Schur complement not divisible by l"
    Jp = J // l
    Lam2, _ = schur_free(Jp, l, v - 1, levels, depth + 1)       # over Z/l^{v-1}, lifted as integers
    s = Lam2.shape[0]
    Lam = np.zeros((s, n), np.int64)
    Lam[:, rr] = Lam2 % M
    if r: Lam[:, pr] = (-(Lam2 @ D) @ Binv) % M
    return Lam, levels

# ---------------------------------------------------------------- defect statistics
def rank_mod(E, l):
    return len(rank_profile(E, l)[0])

def peel(E):
    """remove empty columns and iteratively (column of weight 1, entry 1) with its row.  returns core matrix."""
    A = (E != 0).astype(np.int64)
    rows = np.ones(E.shape[0], bool); cols = np.ones(E.shape[1], bool)
    ch = True
    while ch:
        ch = False
        for j in np.nonzero(cols)[0]:
            wj = int((A[:, j] & rows).sum())
            if wj == 0: cols[j] = False; ch = True
            elif wj == 1:
                i = np.nonzero(A[:, j] & rows)[0][0]
                if E[i, j] == 1: rows[i] = False; cols[j] = False; ch = True
    return E[rows][:, cols]


def ph_dlog(C, P, Q, N, l, vN, ordP):
    """Pohlig-Hellman in the cyclic group <P_l>: d mod l^a, a = v_l(ord P).  Uses only P, Q, N, ord P (no group structure).
    Returns (d mod l^a, l^a, number of group operations spent in the order-l brute-force stage)."""
    a = 0; o = ordP
    while o % l == 0: o //= l; a += 1
    if a == 0: return 0, 1, 0
    cof = N // l ** vN
    Pl, Ql = C.mul(cof, P), C.mul(cof, Q)
    gamma = C.mul(l ** (a - 1), Pl)
    d = 0; ops = 0
    for k in range(a):
        Qk = C.add(Ql, C.neg(C.mul(d, Pl)))
        h = C.mul(l ** (a - 1 - k), Qk)
        t = None; T = None; found = None
        for j in range(l):
            ops += 1
            if T == h: found = j; break
            T = C.add(T, gamma)
        assert found is not None, "PH digit not found"
        d += found * l ** k
    return d % l ** a, l ** a, ops

# ---------------------------------------------------------------- one round
def build_rows(C, Xs, N, rng, extra, X, maxc=400):
    p = C.p; allpts = C.points()
    for _ in range(60):
        u = rng.randrange(1, p); u2 = u * u % p
        F = [Q for Q in allpts if (u2 * Q[0]) % p <= X]
        D = {}
        for i, P1 in enumerate(F):
            for j, P2 in enumerate(F):
                if P1[0] != P2[0]:
                    R = C.add(P1, P2)
                    if R not in D: D[R] = (i, j)
        f = len(F); Nr = f + extra
        rows_e, rows_a = [], []; tries = 0
        while len(rows_e) < Nr and tries < maxc * Nr:
            tries += 1
            a = [rng.randrange(N) for _ in range(4)]
            R = None
            for t in range(4): R = C.add(R, C.mul(a[t], Xs[t]))
            if R in D:
                i, j = D[R]; e = np.zeros(f, np.int64); e[i] += 1; e[j] += 1
                rows_e.append(e); rows_a.append(a)
        if len(rows_e) == Nr:
            return np.array(rows_e), np.array(rows_a, dtype=np.int64), f
    return None

def mus_stream(E, A, l, v, mode, rng, S, info):
    M = l ** v
    if v == 1:
        fk = FieldKernel(E, l)
        info['rank'] = fk.r; info['kerdim'] = E.shape[0] - fk.r; info['defect'] = E.shape[1] - fk.r
        if mode == 'rref': vecs = [fk.basis[i] for i in range(min(S, fk.basis.shape[0]))]
        elif mode == 'unif': vecs = [fk.unif(rng) for _ in range(S)]
        else: vecs = [fk.zsigma(rng, E) for _ in range(S)]
        Lam = np.array(vecs)
    else:
        Lam, levels = schur_free(E, l, v)
        info['levels'] = [(d, n, c, r, dd) for (d, n, c, r, dd) in levels]
        info['defect'] = levels[0][4]; info['kerdim_free'] = Lam.shape[0]
        assert not ((Lam @ E) % M).any(), "Lambda E != 0"
        rk = rank_mod(Lam, l); assert rk == Lam.shape[0], "Lambda not full rank mod l"
        if mode == 'mix':
            Lam = np.array([(np.array([rng.randrange(M) for _ in range(Lam.shape[0])], dtype=np.int64) @ Lam) % M for _ in range(S)])
        else:
            Lam = Lam[:S]
    mus = (Lam @ (A % M)) % M
    return mus

def smin(mus, l, v):
    for s in range(1, len(mus) + 1):
        if howell_solve([list(map(int, r)) for r in mus[:s]], l, v) is not None: return s
    return None

def run_instance(C, P, Q, N, fN, rng, fmode, pmode, S=24, extra=12, expG=None):
    p = C.p; X = math.isqrt(p); pts = C.points()
    for rs in range(30):
        B = (rng.choice(pts), rng.choice(pts)); Xs = [B[0], B[1], P, Q]
        got = build_rows(C, Xs, N, rng, extra, X)
        if got is None: continue
        E, A, f = got
        eB = 1
        for Y in Xs:
            o = order(C, Y, N, fN); eB = eB * o // math.gcd(eB, o)
        res, mods, per = [], [], {}
        ok = True
        for l in fN:
            v = val(eB, l, 99) if eB % l == 0 else 0
            if v == 0: continue
            M = l ** v; info = {}
            if v >= 2 and pmode == 'ph':
                dl, Ml, ops = ph_dlog(C, P, Q, N, l, fN[l], order(C, P, N, fN))
                res.append(dl); mods.append(Ml); per[(l, v)] = dict(info, smin=None, ph_ops=ops); continue
            mus = mus_stream(E, A, l, v, fmode if v == 1 else pmode, rng, S, info)
            cof = N // l ** fN[l]
            for mu in mus:    # toy-only sanity: Lemma 1
                T = None
                for t in range(4): T = C.add(T, C.mul(int(mu[t]), Xs[t]))
                if eB == expG: assert C.mul(cof, T) is None, 'mu is not an l-relation (Lemma 1)'
            s = smin(mus, l, v)
            dl = howell_solve([list(map(int, r)) for r in mus], l, v)
            if dl is None: ok = False; per[(l, v)] = dict(info, smin=None); break
            res.append(dl); mods.append(M); per[(l, v)] = dict(info, smin=s)
        if not ok: continue
        if not mods: return 0, dict(eB=eB, per=per, f=f, Nr=E.shape[0], E=E)
        d2, _ = crt(res, mods)
        if C.mul(d2, P) == Q:
            return d2, dict(eB=eB, per=per, f=f, Nr=E.shape[0], E=E, rs=rs)
    return None, {}

if __name__ == "__main__":
    pass
