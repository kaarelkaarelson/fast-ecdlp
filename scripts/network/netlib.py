"""Decomposition network: Schoenhage-Strassen gadgets (two transform layers) as gate networks.

Gate kinds (all settings are bit strings; a non-input gate stores exactly what it receives):
  FA(v,r)   holds digits r+A1*i1 of variable v      (input gate; shared among all gadgets using v)
  MID(g,k1) receives Y_v[r][k1] for every variable v of gadget g, r<A1
  IB(g,j0)  receives Z'[k1][j0], k1<A2
  CAR(g,j)  receives c_j (ring residue) and the incoming carry
  CH(c,j)   range chain  v + s = bound : receives digit v_j, holds slack digit s_j and carry
Edges carry fixed-width messages; Psi = [msg_sender(z_s) == msg_receiver(z_r)].
"""
import math

def bl(x): return max(1, x.bit_length())
def cdiv(a, b): return -(-a // b)

class Par:
    def __init__(s, L, d, D, nterms=6):
        s.L, s.d, s.D, s.T = L, d, D, 2 * D
        lg = int(math.log2(s.T)); assert 2 ** lg == s.T and D >= 2
        s.A1 = 2 ** cdiv(lg, 2); s.A2 = s.T // s.A1
        assert s.A1 <= D and D % s.A1 == 0
        s.h = D // s.A1
        cbound = nterms * D * (2 ** d - 1) ** 2 + 2 ** d
        s.M = D * cdiv(cbound.bit_length() + 2, D)
        s.mod = 2 ** s.M + 1; s.fw = s.M + 1; s.wexp = s.M // D
        s.cb = s.M - d + 3
        s.Tinv = pow(s.T, -1, s.mod)
        assert D * d >= L + 2
        s._om = [pow(2, s.wexp * e, s.mod) for e in range(s.T)]
        s.half = 2 ** (s.M - 1)
    def om(s, e): return s._om[e % s.T]
    def signed(s, r): return r if r < s.half else r - s.mod
    def cost(s): return s.T * s.fw

def choose_par(L, nterms=6):
    best = None
    for D in (2, 4, 8, 16, 32, 64, 128):
        d = cdiv(L + 2, D)
        if d < 1: continue
        P = Par(L, d, D, nterms)
        key = P.cost() + 3 * P.A1 * P.fw * 4
        if best is None or key < best[0]: best = (key, P)
    return best[1]

def digits(v, d, n):
    assert 0 <= v < 2 ** (d * n), (v, d, n)
    return [(v >> (d * i)) & (2 ** d - 1) for i in range(n)]

# ---------- instance spec ----------
class Gad:
    def __init__(s, name, bil, lin, const):
        s.name, s.bil, s.lin, s.const = name, bil, lin, const   # bil (sign,u,v); lin (sign,v,cnum)
        s.vars = []
        for (_, u, v) in bil:
            for z in (u, v):
                if z not in s.vars: s.vars.append(z)
        for (_, v, _c) in lin:
            if v not in s.vars: s.vars.append(v)
    def value(s, vals):
        return (sum(sg * vals[u] * vals[v] for sg, u, v in s.bil) +
                sum(sg * vals[v] * c for sg, v, c in s.lin) + s.const)

class Spec:
    """variables: name -> dict(nd=digit count, rng=None|('p',)|('B',), pre=[(bitindex, bit)])"""
    def __init__(s, p, a, b, m, R, prefix, par=None):
        s.p, s.a, s.b, s.m, s.R, s.prefix = p, a, b, m, R, prefix
        s.L = p.bit_length()
        lo, hi = 1, 1 << (cdiv(s.L, m) + 1)
        while lo < hi:
            mid = (lo + hi) // 2
            if mid ** m >= p: hi = mid
            else: lo = mid + 1
        B = lo
        s.B = B; s.ell = bl(B - 1)
        s.par = par or choose_par(s.L)
        d = s.par.d
        s.O = 2 ** (s.L + 1)
        nd = lambda bits: cdiv(bits, d)
        V = {}; G = []
        def var(n, bits, rng=None, pre=()): V[n] = dict(nd=nd(bits), rng=rng, pre=list(pre))
        # prefix: bit u (MSB first) of concatenation belongs to x_{u//ell}
        pre_by = {i: [] for i in range(m)}
        for u, ch in enumerate(prefix):
            i, off = divmod(u, s.ell)
            pre_by[i].append((s.ell - 1 - off, int(ch)))
        for i in range(m):
            var('x%d' % i, s.ell, ('B',), pre_by[i]); var('y%d' % i, s.L, ('p',))
            var('u%d' % i, 2 * s.ell); var('qc%d' % i, s.L + 2)
            G.append(Gad('sq%d' % i, [(1, 'u%d' % i, 'u%d' % i)][:0] + [(-1, 'x%d' % i, 'x%d' % i)],
                         [(1, 'u%d' % i, 1)], 0))
            G.append(Gad('curve%d' % i, [(1, 'y%d' % i, 'y%d' % i), (-1, 'u%d' % i, 'x%d' % i)],
                         [(-1, 'x%d' % i, a), (-1, 'qc%d' % i, p)], -b + s.O * p))
        A = 'P0'
        ax, ay = 'x0', 'y0'
        for k in range(1, m):
            bx, by = 'x%d' % k, 'y%d' % k
            w, lam = 'w%d' % k, 'lam%d' % k
            var(w, s.L, ('p',)); var(lam, s.L, ('p',))
            for t in range(4): var('q%d_%d' % (t, k), s.L + 2)
            last = (k == m - 1)
            if last: sx, sy = None, None
            else:
                sx, sy = 'sx%d' % k, 'sy%d' % k
                var(sx, s.L, ('p',)); var(sy, s.L, ('p',))
            q = lambda t: 'q%d_%d' % (t, k)
            O = s.O
            G.append(Gad('inv%d' % k, [(1, bx, w), (-1, ax, w)], [(-1, q(0), p)], -1 + O * p))
            G.append(Gad('slope%d' % k, [(1, bx, lam), (-1, ax, lam)],
                         [(-1, by, 1), (1, ay, 1), (-1, q(1), p)], O * p))
            # lam^2 - ax - bx - sx
            lin2 = [(-1, ax, 1), (-1, bx, 1), (-1, q(2), p)]
            c2 = O * p
            if last: c2 -= R[0]
            else: lin2.append((-1, sx, 1))
            G.append(Gad('xsum%d' % k, [(1, lam, lam)], lin2, c2))
            # lam*ax - lam*sx - sy - ay
            bil3 = [(1, lam, ax)]
            lin3 = [(-1, ay, 1), (-1, q(3), p)]
            c3 = O * p
            if last:
                c3 -= R[1]
                # lam*sx with sx = R.x constant
                lin3.append((-1, lam, R[0]))
            else:
                bil3.append((-1, lam, sx)); lin3.append((-1, sy, 1))
            G.append(Gad('ysum%d' % k, bil3, lin3, c3))
            ax, ay = sx, sy
        s.V, s.G = V, G
        # sanity
        for n, v in V.items(): assert v['nd'] <= s.par.D, n

    def chains(s):
        out = []
        for n, v in s.V.items():
            if v['rng'] == ('p',): out.append((n, s.p - 1))
            elif v['rng'] == ('B',): out.append((n, s.B - 1))
        return out

    # integer witness; mode: returns dict of var values or None
    def witness(s, tup, force=False):
        p, a, b, m, O = s.p, s.a, s.b, s.m, s.O
        vals = {}
        for i, (x, y) in enumerate(tup):
            vals['x%d' % i], vals['y%d' % i] = x, y
            u = x * x; vals['u%d' % i] = u
            vals['qc%d' % i] = (y * y - u * x - a * x - b) // p + O
        ax, ay = tup[0]
        for k in range(1, m):
            bx, by = tup[k]; last = (k == m - 1)
            dx = (bx - ax) % p
            if dx == 0:
                if not force: return None
                w = 0
            else: w = pow(dx, -1, p)
            lam = (by - ay) * w % p
            vals['w%d' % k], vals['lam%d' % k] = w, lam
            vals['q0_%d' % k] = ((bx - ax) * w - 1) // p + O
            vals['q1_%d' % k] = (bx * lam - ax * lam - by + ay) // p + O
            sx = s.R[0] if last else (lam * lam - ax - bx) % p
            vals['q2_%d' % k] = (lam * lam - ax - bx - sx) // p + O
            sy = s.R[1] if last else (lam * (ax - sx) - ay) % p
            vals['q3_%d' % k] = (lam * ax - lam * sx - sy - ay) // p + O
            if not last: vals['sx%d' % k], vals['sy%d' % k] = sx, sy
            ax, ay = sx, sy
        for k_, v in vals.items():
            if not (0 <= v < 2 ** (s.par.d * s.V[k_]['nd'])): return None
        return vals

# ---------- gate-level semantics ----------
class Sim:
    def __init__(s, spec):
        s.sp = spec; s.par = spec.par
        s.cnum_hat = {}
    def dft_const(s, c):
        par = s.par; sg = -1 if c < 0 else 1
        dg = digits(abs(c), par.d, par.T)
        return [sg * sum(dg[i] * par.om(i * k) for i in range(par.T)) % par.mod for k in range(par.T)]
    def gadget_prep(s, g):
        if not hasattr(g, 'ch'):
            g.cl = [(sg, v, s.dft_const(c)) for sg, v, c in g.lin]
            g.kh = s.dft_const(g.const)
            g.ch = True
    # FA message to MID k1
    def fa_msg(s, dg, r, k1):
        par = s.par; t = 0
        for i1 in range(par.h):
            i = r + par.A1 * i1
            if i < len(dg): t += dg[i] * par.om(par.A1 * i1 * k1)
        return t % par.mod
    def mid_out(s, g, Y, k1):
        """Y[v][r] -> Z'[j0] list (j0<A1)"""
        par = s.par; s.gadget_prep(g)
        Xh = {v: [sum(par.om(r * (k1 + par.A2 * k2)) * Y[v][r] for r in range(par.A1)) % par.mod
                  for k2 in range(par.A1)] for v in g.vars}
        C = []
        for k2 in range(par.A1):
            k = k1 + par.A2 * k2
            t = g.kh[k]
            for sg, u, v in g.bil: t += sg * Xh[u][k2] * Xh[v][k2]
            for sg, v, ch in g.cl: t += sg * Xh[v][k2] * ch[k]
            C.append(t % par.mod)
        return [sum(C[k2] * par.om(-j0 * par.A2 * k2) for k2 in range(par.A1)) % par.mod
                for j0 in range(par.A1)]
    def ib_out(s, Zp, j):
        par = s.par
        return par.Tinv * sum(par.om(-j * k1) * Zp[k1] for k1 in range(par.A2)) % par.mod
    def carry_ok(s, cs):
        par = s.par; u = 0
        for c in cs:
            t = par.signed(c) + u
            if t % (1 << par.d): return False
            u = t >> par.d
        return u == 0
    def gadget_accept(s, g, vals):
        """full gate-level run: FA -> MID -> IB -> CAR"""
        par = s.par; sp = s.sp
        dg = {v: digits(vals[v], par.d, sp.V[v]['nd']) for v in g.vars}
        Zp = [None] * par.A2
        for k1 in range(par.A2):
            Y = {v: [s.fa_msg(dg[v], r, k1) for r in range(par.A1)] for v in g.vars}
            Zp[k1] = s.mid_out(g, Y, k1)
        cs = []
        for j in range(par.T):
            cs.append(s.ib_out([Zp[k1][j % par.A1] for k1 in range(par.A2)], j))
        return s.carry_ok(cs)
    def chain_accept(s, v, bound, val):
        par = s.par; nd = s.sp.V[v]['nd']
        dv = digits(val, par.d, nd)
        if bound >= 2 ** (par.d * nd): return True
        sl = bound - val
        if sl < 0: return False
        ds = digits(sl, par.d, nd)
        bd = digits(bound, par.d, nd)
        u = 0
        for j in range(nd):
            t = dv[j] + ds[j] + u
            if (t & (2 ** par.d - 1)) != bd[j]: return False
            u = t >> par.d
        return u == 0
    def prefix_ok(s, vals):
        for n, v in s.sp.V.items():
            for (bi, bit) in v['pre']:
                if (vals[n] >> bi) & 1 != bit: return False
        return True
    def accept(s, vals):
        sp = s.sp
        if not s.prefix_ok(vals): return 0
        for n, bound in sp.chains():
            if not s.chain_accept(n, bound, vals[n]): return 0
        for g in sp.G:
            if not s.gadget_accept(g, vals): return 0
        return 1

# ---------- topology (nodes, edges) ----------
def topology(sp):
    """returns nodes {gid: setting bits}, edges [(sender, receiver, width)]"""
    par = sp.par; d = par.d
    nodes, edges = {}, []
    for v, info in sp.V.items():
        nd = info['nd']
        for r in range(min(par.A1, nd)):
            cnt = len([i for i in range(r, nd, par.A1)])
            nodes[('FA', v, r)] = cnt * d
    for gi, g in enumerate(sp.G):
        for k1 in range(par.A2):
            tot = sum(min(par.A1, sp.V[v]['nd']) for v in g.vars)
            nodes[('MID', gi, k1)] = tot * par.fw
            for v in g.vars:
                for r in range(min(par.A1, sp.V[v]['nd'])):
                    edges.append((('FA', v, r), ('MID', gi, k1), par.fw))
            for j0 in range(par.A1):
                edges.append((('MID', gi, k1), ('IB', gi, j0), par.fw))
        for j0 in range(par.A1):
            nodes[('IB', gi, j0)] = par.A2 * par.fw
            for j in range(j0, par.T, par.A1):
                edges.append((('IB', gi, j0), ('CAR', gi, j), par.fw))
        for j in range(par.T):
            nodes[('CAR', gi, j)] = par.fw + par.cb
            if j + 1 < par.T: edges.append((('CAR', gi, j), ('CAR', gi, j + 1), par.cb))
    for v, bound in sp.chains():
        nd = sp.V[v]['nd']
        for j in range(nd):
            nodes[('CH', v, j)] = 2 * d + 1
            edges.append((('FA', v, j % par.A1), ('CH', v, j), d))
            if j + 1 < nd: edges.append((('CH', v, j), ('CH', v, j + 1), 1))
    return nodes, edges

def rowsums(nodes, edges):
    rs = {a: 0 for a in nodes}
    for a, b, c in edges: rs[a] += c; rs[b] += c
    return rs

def cluster_sizes(nodes, edges, g):
    """greedy clustering of gates into g clusters; returns dict with P (max over clusters of
    max(setting bits, shared bits)), cluster bits, total U, held bits."""
    rs = rowsums(nodes, edges)
    ids = list(nodes)
    held = sum(nodes.values())
    Ugate = 2 * sum(c for _, _, c in edges)
    best = None
    orders = [sorted(ids, key=lambda a: -(nodes[a] + rs[a])), ids]
    for strat, order in enumerate(orders):
        asg = {}
        if g >= len(ids):
            for i, a in enumerate(order): asg[a] = i
            ncl = len(ids)
        else:
            ncl = g
            if strat == 0:
                load = [0] * g
                import heapq
                h = [(0, i) for i in range(g)]
                heapq.heapify(h)
                for a in order:
                    l, i = heapq.heappop(h); asg[a] = i
                    heapq.heappush(h, (l + nodes[a] + rs[a], i))
            else:
                tot = sum(nodes[a] + rs[a] for a in order); acc = 0
                for a in order:
                    asg[a] = min(g - 1, int(acc * g / tot)); acc += nodes[a] + rs[a]
        bits = {}; row = {}
        for a, i in asg.items(): bits[i] = bits.get(i, 0) + nodes[a]
        Ucl = 0
        for a, b, c in edges:
            if asg[a] != asg[b]:
                row[asg[a]] = row.get(asg[a], 0) + c; row[asg[b]] = row.get(asg[b], 0) + c; Ucl += 2 * c
        P = max([bits.get(i, 0) for i in bits] + list(row.values()))
        res = dict(P=P, U=Ucl, clusters=ncl, maxbits=max(bits.values()), maxrow=max(row.values()) if row else 0)
        if best is None or res['P'] < best['P']: best = res
    best['held'] = held; best['Ugate'] = Ugate; best['gates'] = len(ids)
    best['maxgate'] = max(max(nodes[a], rs[a]) for a in ids)
    return best
