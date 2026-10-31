# Own linear algebra over Z/q, q = l^v.  Independent of every_order_toy/toy_ic.py.
import numpy as np
def val(x, l, v):
    if x % (l**v) == 0: return v
    k = 0
    while x % l == 0: x //= l; k += 1
    return k

def elim(rows, ncols, l, v):
    """Generating set of {r in span(rows) : r[0..ncols-1]=0} (Howell-style:
    pivot of minimal valuation, subtract, add annihilator multiple of pivot).
    Also returns pivot valuations per column (v if column empty)."""
    q = l**v
    R = np.array(rows, dtype=np.int64) % q
    ks = []
    for c in range(ncols):
        if R.shape[0] == 0: ks.append(v); continue
        col = R[:, c]
        piv = None; kbest = v
        for k in range(v):
            nz = np.nonzero(col % (l**(k+1)))[0]
            if len(nz): piv = int(nz[0]); kbest = k; break
        ks.append(kbest)
        if piv is None: continue
        k = kbest; lk = l**k
        pr = R[piv].copy()
        w = int(pr[c]) // lk
        winv = pow(w, -1, q)
        qq = ((col // lk) % q) * winv % q
        qq[piv] = 0
        R = (R - np.outer(qq, pr)) % q
        ann = (pr * (l**(v-k))) % q
        if ann.any(): R[piv] = ann
        else: R = np.delete(R, piv, axis=0)
        R = R[R.any(axis=1)]
    return R, ks

def span_size_log(rows, l, v):
    """log_l of |span(rows)| inside (Z/l^v)^w."""
    w = len(rows[0]) if len(rows) else 0
    _, ks = elim(rows, w, l, v)
    return sum(v-k for k in ks)

def elim_transform(E, l, v):
    """Own Smith-type row reduction (vectorised): rows of invertible U with zero E-part."""
    q = l**v
    n, f = E.shape
    W = np.concatenate([E % q, np.eye(n, dtype=np.int64)], axis=1)
    act = np.ones(n, bool); acol = np.ones(f, bool)
    while True:
        sub = W[:, :f] * act[:, None] * acol[None, :]
        piv = None
        for k in range(v):
            nz = np.argwhere(sub % (l**(k+1)) != 0)
            if len(nz): piv = (k, int(nz[0][0]), int(nz[0][1])); break
        if piv is None: break
        k, i, c = piv
        lk = l**k; w = int(W[i, c]) // lk; winv = pow(w, -1, q)
        qq = (W[:, c] // lk) % q * winv % q
        qq[~act] = 0; qq[i] = 0
        W = (W - np.outer(qq, W[i])) % q
        act[i] = False; acol[c] = False
    Lam = W[act][:, f:]
    assert not (W[act][:, :f] % q).any()
    return Lam
