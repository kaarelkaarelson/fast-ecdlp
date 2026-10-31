"""Full (non-generic) Semaev bounded decomposition as a sum over degeneracy patterns.

A pattern ("word") assigns to every step k = 2..m one of
   A  generic addition   S_k = S_{k-1} + P_k,  x(S_{k-1}) != x(P_k)
   D  doubling           P_k = S_{k-1} (y != 0),   S_k = 2 S_{k-1}
   C  cancellation       P_k = -S_{k-1},           S_k = O
   S  start              S_{k-1} = O,              S_k = P_k
with S iff the previous step is C, and last step C iff R = O.
Each word gives a network in the style of network/netlib.py (same SS gadgets), built from the same Gad / Sim / topology
code (netlib.py, the size_bounds/ version).  O (the offset) is 2^(L+3) here (doubling needs |E|/p up to 3p+1).
"""
import itertools, math
import netlib as nl

def cdiv(a, b): return -(-a // b)

def clean_par4(L):
    D = 4
    while 2 * D * D < L: D *= 2
    return nl.Par(L, cdiv(L + 4, D), D, 6)

def words(m, Ris_O):
    """all valid words (tuples of letters of length m-1)"""
    out = []
    for w in itertools.product('ADC', repeat=m - 1):
        # insert S after each C: build real sequence: letters for steps 2..m
        pass
    res = []
    def rec(k, prev, cur):
        if k == m:
            last = cur[-1]
            if (last == 'C') == Ris_O: res.append(''.join(cur))
            return
        if prev == 'C': rec(k + 1, 'S', cur + ['S'])
        else:
            for t in 'ADC': rec(k + 1, t, cur + [t])
    rec(1, 'start', [])
    # 'start' is not C so first step may be A, D, C
    return res

class PSpec:
    def __init__(s, p, a, b, m, R, word, prefix='', par=None):
        """R = (x,y) or None for the point at infinity"""
        s.p, s.a, s.b, s.m, s.R, s.word, s.prefix = p, a, b, m, R, word, prefix
        s.L = p.bit_length()
        lo, hi = 1, 1 << (cdiv(s.L, m) + 1)
        while lo < hi:
            mid = (lo + hi) // 2
            if mid ** m >= p: hi = mid
            else: lo = mid + 1
        s.B = lo; s.ell = max(1, (s.B - 1).bit_length())
        s.par = par or clean_par4(s.L)
        d = s.par.d; L = s.L
        s.O = 2 ** (L + 3)
        O = s.O
        nd = lambda bits: cdiv(bits, d)
        V = {}; G = []
        def var(n, bits, rng=None, pre=()): V[n] = dict(nd=nd(bits), rng=rng, pre=list(pre))
        pre_by = {i: [] for i in range(m)}
        for u, ch in enumerate(prefix):
            i, off = divmod(u, s.ell)
            pre_by[i].append((s.ell - 1 - off, int(ch)))
        for i in range(m):
            var('x%d' % i, s.ell, ('B',), pre_by[i]); var('y%d' % i, L, ('p',))
            var('u%d' % i, 2 * s.ell); var('qc%d' % i, L + 4)
            G.append(nl.Gad('sq%d' % i, [(-1, 'x%d' % i, 'x%d' % i)], [(1, 'u%d' % i, 1)], 0))
            G.append(nl.Gad('curve%d' % i, [(1, 'y%d' % i, 'y%d' % i), (-1, 'u%d' % i, 'x%d' % i)],
                            [(-1, 'x%d' % i, a), (-1, 'qc%d' % i, p)], -b + O * p))
        assert len(word) == m - 1
        A = ('x0', 'y0')      # None = O
        for k in range(1, m):
            t = word[k - 1]; last = (k == m - 1)
            bx, by = 'x%d' % k, 'y%d' % k
            w, lam = 'w%d' % k, 'lam%d' % k
            q = lambda i: 'q%d_%d' % (i, k)
            if t == 'S':
                assert A is None
                A = (bx, by)
                if last:
                    assert R is not None
                    G.append(nl.Gad('eqRx%d' % k, [], [(1, bx, 1)], -R[0]))
                    G.append(nl.Gad('eqRy%d' % k, [], [(1, by, 1)], -R[1]))
                continue
            assert A is not None
            ax, ay = A
            if t == 'C':
                assert (R is None) or not last
                var('qe%d' % k, L + 4)
                G.append(nl.Gad('eqx%d' % k, [], [(1, bx, 1), (-1, ax, 1)], 0))
                G.append(nl.Gad('eqy%d' % k, [], [(1, by, 1), (1, ay, 1), (-1, 'qe%d' % k, p)], O * p))
                A = None
                continue
            assert R is not None if last else True
            var(w, L, ('p',)); var(lam, L, ('p',))
            for i in range(4): var(q(i), L + 4)
            if last: sx = sy = None
            else:
                sx, sy = 'sx%d' % k, 'sy%d' % k
                var(sx, L, ('p',)); var(sy, L, ('p',))
            if t == 'A':
                G.append(nl.Gad('inv%d' % k, [(1, bx, w), (-1, ax, w)], [(-1, q(0), p)], -1 + O * p))
                G.append(nl.Gad('slope%d' % k, [(1, bx, lam), (-1, ax, lam)],
                                [(-1, by, 1), (1, ay, 1), (-1, q(1), p)], O * p))
                lin2 = [(-1, ax, 1), (-1, bx, 1), (-1, q(2), p)]; c2 = O * p
            elif t == 'D':
                G.append(nl.Gad('eqx%d' % k, [], [(1, bx, 1), (-1, ax, 1)], 0))
                G.append(nl.Gad('eqy%d' % k, [], [(1, by, 1), (-1, ay, 1)], 0))
                G.append(nl.Gad('inv%d' % k, [(2, ay, w)], [(-1, q(0), p)], -1 + O * p))
                bil = [(1, lam, ay)] * 2 + [(-1, ax, ax)] * 3
                G.append(nl.Gad('slope%d' % k, bil, [(-1, q(1), p)], O * p - a))
                lin2 = [(-1, ax, 2), (-1, q(2), p)]; c2 = O * p
            else: raise ValueError(t)
            if last: c2 -= R[0]
            else: lin2.append((-1, sx, 1))
            G.append(nl.Gad('xsum%d' % k, [(1, lam, lam)], lin2, c2))
            bil3 = [(1, lam, ax)]; lin3 = [(-1, ay, 1), (-1, q(3), p)]; c3 = O * p
            if last:
                c3 -= R[1]; lin3.append((-1, lam, R[0]))
            else:
                bil3.append((-1, lam, sx)); lin3.append((-1, sy, 1))
            G.append(nl.Gad('ysum%d' % k, bil3, lin3, c3))
            A = (sx, sy)
        if R is None: assert word[-1] == 'C'
        s.V, s.G = V, G
        for n, v in V.items(): assert v['nd'] <= s.par.D, n

    chains = nl.Spec.chains

    def witness(s, tup):
        """canonical integer witness following the word; None if a value is out of its digit window.
        Values that cannot satisfy the pattern are produced by 'forcing' (w=0 etc.) and fail the identities."""
        p, a, b, m, O, word = s.p, s.a, s.b, s.m, s.O, s.word
        vals = {}
        for i, (x, y) in enumerate(tup):
            vals['x%d' % i], vals['y%d' % i] = x, y
            u = x * x; vals['u%d' % i] = u
            vals['qc%d' % i] = (y * y - u * x - a * x - b) // p + O
        A = tup[0]
        for k in range(1, m):
            t = word[k - 1]; last = (k == m - 1)
            bx, by = tup[k]
            if t == 'S':
                A = tup[k]; continue
            if A is None: return None
            ax, ay = A
            if t == 'C':
                vals['qe%d' % k] = (by + ay) // p + O
                A = None; continue
            if t == 'A':
                dx = (bx - ax) % p
                w = pow(dx, -1, p) if dx else 0
                lam = (by - ay) * w % p
                vals['q0_%d' % k] = ((bx - ax) * w - 1) // p + O
                vals['q1_%d' % k] = (bx * lam - ax * lam - by + ay) // p + O
                e2 = lam * lam - ax - bx
            else:
                dy = 2 * ay % p
                w = pow(dy, -1, p) if dy else 0
                lam = (3 * ax * ax + a) * w % p
                vals['q0_%d' % k] = (2 * ay * w - 1) // p + O
                vals['q1_%d' % k] = (2 * lam * ay - 3 * ax * ax - a) // p + O
                e2 = lam * lam - 2 * ax
            vals['w%d' % k], vals['lam%d' % k] = w, lam
            sx = s.R[0] if last else e2 % p
            vals['q2_%d' % k] = (e2 - sx) // p + O
            sy = s.R[1] if last else (lam * (ax - sx) - ay) % p
            vals['q3_%d' % k] = (lam * ax - lam * sx - sy - ay) // p + O
            if not last: vals['sx%d' % k], vals['sy%d' % k] = sx, sy
            A = (sx, sy)
        for k_, v in vals.items():
            if not (0 <= v < 2 ** (s.par.d * s.V[k_]['nd'])): return None
        # variables never assigned (e.g. forced words) default to 0
        for n in s.V:
            vals.setdefault(n, 0)
        return vals

    def int_accept(s, vals):
        """integer system: all identities zero, ranges, prefix  (== Sim.accept by the gadget tests)"""
        if vals is None: return 0
        for n, v in s.V.items():
            for (bi, bit) in v['pre']:
                if (vals[n] >> bi) & 1 != bit: return 0
        for n, bound in s.chains():
            if not 0 <= vals[n] <= bound: return 0
        for g in s.G:
            if g.value(vals) != 0: return 0
        return 1
