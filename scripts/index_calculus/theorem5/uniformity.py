# Experiment for Lemma 2 (conditioned on the R-sequence, Lambda a is uniform on K_l, iid over j).
# Tiny group (|G| <= 64) so that all fibres {a in (Z/N)^4 : sum a_j X_j = R} are enumerated exactly.
import random, math, itertools, sys
import numpy as np
from myic import *
from run30 import classify

def elim_transform(E, l, v):
    """Own Smith-type row reduction: returns Lambda (rows of invertible U with zero E-part)."""
    q = l**v
    n, f = E.shape
    W = np.concatenate([E % q, np.eye(n, dtype=np.int64)], axis=1)
    active = list(range(n)); acols = list(range(f))
    while True:
        best = None
        for i in active:
            for c in acols:
                x = int(W[i, c])
                if x:
                    k = val(x, l, v)
                    if best is None or k < best[0]: best = (k, i, c)
        if best is None: break
        k, i, c = best
        lk = l**k; w = int(W[i, c]) // lk; winv = pow(w, -1, q)
        for i2 in active:
            if i2 == i: continue
            qq = (int(W[i2, c]) // lk) * winv % q
            if qq: W[i2] = (W[i2] - qq*W[i]) % q
        active.remove(i); acols.remove(c)
    Lam = W[active][:, f:]
    assert not (W[active][:, :f] % q).any()
    return Lam

def build(seed):
    rng = random.Random(seed)
    while True:
        p = rng.choice([x for x in range(30, 140) if isprime(x)])
        C = Curve(p, rng.randrange(1,p), rng.randrange(p))
        if (4*C.A**3+27*C.B**2) % p == 0: continue
        N = C.N
        if not (24 <= N <= 52): continue
        fN = factor(N)
        if max(fN.values()) < 2: continue
        return C, fN, rng

def main(seed, T):
    C, fN, rng = build(seed)
    N, p = C.N, C.p
    pts = [O] + C.pts; ix = {P: i for i, P in enumerate(pts)}
    addtab = np.array([[ix[C.add(a, b)] for b in pts] for a in pts])
    # four generators of G
    while True:
        Xs = [C.rand_pt(rng) for _ in range(4)]
        if subgroup_size(C, Xs) == N: break
    mt = [np.array([ix[C.mul(a, X)] for a in range(N)]) for X in Xs]
    A1, A2, A3, A4 = np.meshgrid(*[np.arange(N)]*4, indexing='ij')
    Ridx = addtab[addtab[mt[0][A1], mt[1][A2]], addtab[mt[2][A3], mt[3][A4]]].ravel()
    avec = np.stack([A1.ravel(), A2.ravel(), A3.ravel(), A4.ravel()], axis=1)
    order = np.argsort(Ridx, kind='stable'); Rs = Ridx[order]
    fib = {}
    for r in set(Rs.tolist()):
        lo, hi = np.searchsorted(Rs, r, 'left'), np.searchsorted(Rs, r, 'right')
        fib[r] = order[lo:hi]
    print(f"curve p={p} N={N}={fN} fibre size N^3={N**3}; all fibres equal size: {len({len(v) for v in fib.values()})==1}")
    # fixed R-sequence with decompositions
    X = math.isqrt(p); u = 1
    Fu = [P for P in C.pts if P[0] <= X + 3]   # slightly larger box for small p
    idx = {P: i for i, P in enumerate(Fu)}; f = len(Fu)
    rowsE = []; Rseq = []
    while len(rowsE) < f + 14:
        Rp = rng.choice(pts[1:])
        dec = None
        for P1 in Fu:
            P2 = C.add(Rp, C.neg(P1))
            if P2 in idx and P2[0] != P1[0]: dec = (P1, P2); break
        if dec is None: continue
        e = [0]*f; e[idx[dec[0]]] += 1; e[idx[dec[1]]] += 1
        rowsE.append(e); Rseq.append(ix[Rp])
    E = np.array(rowsE, dtype=np.int64); n = len(Rseq)
    print(f"f={f}, rows={n}")
    npr = np.random.default_rng(seed)
    results = []
    for l, v in fN.items():
        q = l**v
        Lam = elim_transform(E, l, v)
        s = Lam.shape[0]
        # onto: Lam mod l has full row rank s
        M = Lam % l; rank = 0; M = M.copy()
        for c in range(M.shape[1]):
            pr = [r for r in range(rank, s) if M[r, c] % l]
            if not pr: continue
            M[[rank, pr[0]]] = M[[pr[0], rank]]
            M[rank] = M[rank] * pow(int(M[rank, c]), -1, l) % l
            for r in range(s):
                if r != rank and M[r, c]: M[r] = (M[r] - M[r, c]*M[rank]) % l
            rank += 1
        # true K_l
        cl = N // q; cinv = pow(cl, -1, q)
        pis = [ix[C.mul(cl*cinv, X_)] for X_ in Xs]
        mtl = [np.array([ix[C.mul(a, pts[pi])] for a in range(q)]) for pi in pis]
        B1, B2, B3, B4 = np.meshgrid(*[np.arange(q)]*4, indexing='ij')
        Rl = addtab[addtab[mtl[0][B1], mtl[1][B2]], addtab[mtl[2][B3], mtl[3][B4]]]
        Kmask = (Rl == 0)
        Kl = np.stack([B1[Kmask], B2[Kmask], B3[Kmask], B4[Kmask]], axis=1)
        Kset = {tuple(r): i for i, r in enumerate(Kl.tolist())}
        # sample
        mus = np.zeros((T, s, 4), dtype=np.int64)
        for i in range(n):
            fb = fib[Rseq[i]]
            pick = avec[fb[npr.integers(0, len(fb), size=T)]]          # T x 4, uniform on fibre
            mus += Lam[:, i][None, :, None] * pick[:, None, :]
        mus %= q
        inK = all(tuple(m) in Kset for m in mus[:200].reshape(-1, 4).tolist())
        # chi-square for mu_1 on K_l
        cnt = np.zeros(len(Kl))
        for m in mus[:, 0, :].tolist(): cnt[Kset[tuple(m)]] += 1
        exp = T / len(Kl); chi = ((cnt - exp)**2 / exp).sum(); dfree = len(Kl) - 1
        z = (chi - dfree) / math.sqrt(2*dfree)
        # joint (mu_1, mu_2) reduced mod l
        pair = {}
        for a, b in zip(mus[:, 0, :].tolist(), mus[:, 1, :].tolist()):
            key = (tuple(x % l for x in a), tuple(x % l for x in b)); pair[key] = pair.get(key, 0) + 1
        imgK = {tuple(x % l for x in r) for r in Kl.tolist()}
        nb = len(imgK)**2; e2 = T / nb
        chi2 = sum((c - e2)**2 / e2 for c in pair.values()) + (nb - len(pair)) * e2
        z2 = (chi2 - (nb-1)) / math.sqrt(2*(nb-1))
        print(f"  l^v={q}: s={s} rank(Lam mod l)={rank} (onto iff =s: {rank==s}); mu in K_l (200 draws): {inK}; |K_l|={len(Kl)}; "
              f"mu_1 chi2={chi:.0f} df={dfree} z={z:+.2f}; joint(mu1,mu2 mod l) bins={nb} chi2={chi2:.0f} z={z2:+.2f}")
        results.append((rank == s, inK, abs(z) < 4, abs(z2) < 4))
        # negative control: biased sampler (a_1 forced even) should be detected for mu_1 if l=2... use fibre subset
        if l == 2 or l == 3:
            mus_b = np.zeros((T, 4), dtype=np.int64)
            for i in range(n):
                fb = fib[Rseq[i]]; fb = fb[avec[fb][:, 0] % l == 0]
                if len(fb) == 0: fb = fib[Rseq[i]]
                pick = avec[fb[npr.integers(0, len(fb), size=T)]]
                mus_b += Lam[0, i] * pick
            mus_b %= q
            cntb = np.zeros(len(Kl))
            for m in mus_b.tolist(): cntb[Kset[tuple(m)]] += 1
            chib = ((cntb - exp)**2 / exp).sum()
            print(f"     negative control (biased: a_1 = 0 mod l): chi2={chib:.0f} (df {dfree}, z={(chib-dfree)/math.sqrt(2*dfree):+.1f})")
    return all(all(r) for r in results)
if __name__ == "__main__":
    seed = int(sys.argv[1]); T = int(sys.argv[2])
    ok = main(seed, T)
    print("UNIFORMITY_EXPERIMENT", "consistent with Lemma 2" if ok else "DEVIATION")
