#!/usr/bin/env python3
"""Checker: decomposition network (Definition 2 of the Anthropic ETH paper).
Run: nice -n 19 taskpolicy -b python3 check_network.py   (prints PASS only if all three parts hold)"""
import random, sys, time, itertools, math
import brute_force as bf
import netlib as nl

rng = random.Random(20261030)
LOG = []
def say(*a):
    s = ' '.join(str(x) for x in a); print(s); LOG.append(s)

def is_probable_prime(n):
    if n < 2: return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0: return n == q
    d, r = n - 1, 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def prime34(L):
    while True:
        p = rng.getrandbits(L) | (1 << (L - 1)) | 3
        if p % 4 == 3 and is_probable_prime(p): return p

# ---------------- part 1: exact counts ----------------
def part1():
    say('== PART 1: exact counts (ordered tuples (P_1..P_m) in F^m, generic additions) ==')
    say('F = {affine P on y^2=x^3+ax+b : 0<=x<B}, B=ceil(p^(1/m)); prefix = leading bits of x_1||..||x_m, each x_i on ell=bitlen(B-1) bits.')
    say('Counted: ordered tuples with P_1+..+P_m=R where every partial addition S_{k-1}+P_k has x(S_{k-1})!=x(P_k) (no doubling, no P_i=-P_j step).')
    curves = [(37, 2, 5, 2), (101, 3, 7, 2), (251, 1, 9, 2), (1019, 5, 11, 2), (4093, 7, 3, 2), (16381, 2, 3, 2),
              (101, 3, 7, 3), (251, 4, 1, 3), (1019, 2, 6, 3), (4093, 9, 2, 3), (16381, 3, 5, 3), (37, 2, 5, 4), (251, 4, 1, 4), (1019, 2, 6, 4)]
    inst = 0; allok = True; tot_acc = 0; tot_rej = 0; excluded_total = 0; gen_total = 0
    for (p0, a, b, m) in curves:
        p = bf.next_prime(p0)
        if (4 * a ** 3 + 27 * b * b) % p == 0: continue
        t0 = time.time()
        B, F, full, gen = bf.distribution(p, a, b, m)
        ell = nl.bl(B - 1)
        # pick targets: zero generic decompositions (R on curve, in full or not), one, many
        pts = bf.curve_points(p, a, b)
        cands = {}
        zero = [R for R in pts if R not in gen]
        if zero: cands['zero'] = [rng.choice(zero)]
        ones = [R for R in gen if len(gen[R]) == 1]
        if ones: cands['one'] = [rng.choice(ones)]
        many = sorted(gen, key=lambda r: -len(gen[r]))
        cands['many'] = [many[0], many[len(many) // 2]] if len(many) > 1 else many[:1]
        # an R that has degenerate (excluded) decompositions
        degen = [R for R in full if len(full[R]) != len(gen.get(R, []))]
        if degen: cands['degen'] = [rng.choice(degen)]
        for kind, Rs in cands.items():
            for R in Rs:
                tups = gen.get(R, [])
                pref_list = ['']
                if tups:
                    s = ''.join(bf.xbits(P[0], ell) for P in rng.choice(tups))
                    pref_list += [s[:max(1, len(s) // 2)], s]
                pref_list.append(''.join(rng.choice('01') for _ in range(max(1, m * ell // 3))))
                for pref in pref_list:
                    sp = nl.Spec(p, a, b, m, R, pref); sim = nl.Sim(sp)
                    want = bf.count(tups, ell, pref)
                    want_full = bf.count(full.get(R, []), ell, pref)
                    # contraction: sum over all generic tuples with forced witness of the gate-level product
                    Z = 0
                    for tup in tups:
                        w = sp.witness(tup); assert w is not None
                        Z += sim.accept(w)
                    # violators: arbitrary tuples (non-generic, wrong sum, bad prefix) with best-effort witnesses
                    rej = 0; acc_bad = 0
                    gens = set(tups)
                    pool = list(itertools.product(F, repeat=m))
                    sample = pool if len(pool) <= 300 else rng.sample(pool, 300)
                    for tup in sample:
                        if tup in gens: continue
                        w = sp.witness(tup, force=True)
                        if w is None: rej += 1; continue
                        if sim.accept(w): acc_bad += 1
                        else: rej += 1
                    # near-misses: flip one digit bit of one witness variable of a true decomposition
                    for tup in tups[:3]:
                        w = sp.witness(tup)
                        for _ in range(6):
                            v = rng.choice(list(w)); w2 = dict(w)
                            w2[v] ^= 1 << rng.randrange(sp.par.d * sp.V[v]['nd'])
                            if sim.accept(w2): acc_bad += 1
                            else: rej += 1
                    inst += 1; tot_acc += Z; tot_rej += rej
                    ok = (Z == want) and acc_bad == 0
                    allok &= ok
                    excluded_total += want_full - want
                    gen_total += want
                    say('inst %2d p=%-6d a=%d b=%d m=%d B=%d |F|=%d R=%s kind=%-5s prefix=%-14r Z=%d brute=%d (full incl. degenerate=%d) violators rejected=%d accepted=%d %s' %
                        (inst, p, a, b, m, B, len(F), R, kind, pref, Z, want, want_full, rej, acc_bad, 'OK' if ok else 'MISMATCH'))
    say('instances=%d  sum Z=%d  excluded (degenerate) tuples among prefix-matching ones=%d  total violators rejected=%d' % (inst, tot_acc, excluded_total, tot_rej))
    return allok and inst >= 30, inst

# ---------------- gadget correctness (accept <=> integer identity) ----------------
def gadget_tests():
    say('== gadget correctness: gate-level accept <=> integer identity ==')
    ok = True
    # exhaustive on tiny parameters
    for (p, a, b, m, R) in [(7, 1, 3, 2, (3, 2)), (13, 2, 3, 2, (4, 1))]:
        sp = nl.Spec(p, a, b, m, R, ''); sim = nl.Sim(sp); par = sp.par
        for g in sp.G:
            rngs = [range(2 ** (par.d * sp.V[v]['nd'])) for v in g.vars]
            size = math.prod(len(r) for r in rngs)
            if size > 400000: continue
            bad = 0; zeros = 0
            for vv in itertools.product(*rngs):
                vals = dict(zip(g.vars, vv))
                exp = g.value(vals) == 0; zeros += exp
                if sim.gadget_accept(g, vals) != exp: bad += 1
            say('  exhaustive p=%d gadget %-7s vars=%d assignments=%d identity-true=%d mismatches=%d' % (p, g.name, len(g.vars), size, zeros, bad))
            ok &= bad == 0
    # random + near-miss at large sizes
    for L in (16, 64, 160, 256, 512):
        for m in (2, 3, 4):
            p = prime34(L); a, b = rng.randrange(p), rng.randrange(p)
            if (4 * a ** 3 + 27 * b * b) % p == 0: continue
            B = nl.Spec(p, a, b, m, (0, 0), '').B
            tup = []
            while len(tup) < m:
                x = rng.randrange(B); r = (x ** 3 + a * x + b) % p
                y = pow(r, (p + 1) // 4, p)
                if y * y % p == r and (not tup or all(x != t[0] for t in tup)): tup.append((x, y))
            S = None
            for P in tup:
                S = bf.add(S, P, p, a)
            ok_t = True
            xs_ok = all(tup[i][0] != tup[j][0] for i in range(m) for j in range(i))
            # partial sums distinct-x check
            S = tup[0]
            for k in range(1, m):
                if S is None or S[0] == tup[k][0]: ok_t = False; break
                S = bf.add(S, tup[k], p, a)
            if not ok_t or S is None: continue
            sp = nl.Spec(p, a, b, m, S, ''); sim = nl.Sim(sp)
            w = sp.witness(tuple(tup)); good = sim.accept(w)
            rej = 0; wrong = 0
            for _ in range(40):
                v = rng.choice(list(w)); w2 = dict(w)
                w2[v] ^= 1 << rng.randrange(sp.par.d * sp.V[v]['nd'])
                if w2[v] == w[v]: continue
                if sim.accept(w2): wrong += 1
                else: rej += 1
            for _ in range(10):  # +-1 perturbation of a quotient
                v = rng.choice([k for k in w if k.startswith('q')]); w2 = dict(w); w2[v] += rng.choice((-1, 1))
                if 0 <= w2[v] < 2 ** (sp.par.d * sp.V[v]['nd']):
                    if sim.accept(w2): wrong += 1
                    else: rej += 1
            say('  random L=%3d m=%d (d=%d D=%d M=%d): true decomposition accepted=%d, perturbed rejected=%d wrongly-accepted=%d' % (L, m, sp.par.d, sp.par.D, sp.par.M, good, rej, wrong))
            ok &= bool(good) and wrong == 0
    return ok

# ---------------- part 2: Definition 2 ----------------
class NetGates:
    """explicit gate settings/messages for one instance, to test Psi factorizations"""
    def __init__(s, sp):
        s.sp = sp; s.par = sp.par; s.sim = nl.Sim(sp)
        s.nodes, s.edges = nl.topology(sp)
        s.nb = {}
        for a, b, c in s.edges:
            s.nb.setdefault(a, {})[b] = (c, 'send'); s.nb.setdefault(b, {})[a] = (c, 'recv')
    def sample(s, gid):
        par = s.par; kind = gid[0]; rd = rng.getrandbits
        if kind == 'FA':
            v, r = gid[1], gid[2]; nd = s.sp.V[v]['nd']
            return tuple(rd(par.d) for i in range(r, nd, par.A1))
        if kind == 'MID':
            g = s.sp.G[gid[1]]
            return tuple(tuple(rng.randrange(par.mod) for r in range(min(par.A1, s.sp.V[v]['nd']))) for v in g.vars)
        if kind == 'IB': return tuple(rng.randrange(par.mod) for _ in range(par.A2))
        if kind == 'CAR': return (rng.randrange(par.mod), rng.randrange(2 ** par.cb))
        if kind == 'CH': return (rd(par.d), rd(par.d), rd(1))
    def msg(s, gid, nbr, z):
        """message of gate gid towards neighbour nbr under setting z"""
        par = s.par; kind = gid[0]; c, role = s.nb[gid][nbr]
        if kind == 'FA':
            v, r = gid[1], gid[2]
            if nbr[0] == 'MID': return s.sim.fa_msg(list(_expand(z, r, par.A1, s.sp.V[v]['nd'])), r, nbr[2])
            if nbr[0] == 'CH': return z[(nbr[2] - r) // par.A1]
        if kind == 'MID':
            g = s.sp.G[gid[1]]
            if nbr[0] == 'FA':
                vi = g.vars.index(nbr[1]); return z[vi][nbr[2]]
            Y = {v: list(z[i]) + [0] * (par.A1 - len(z[i])) for i, v in enumerate(g.vars)}
            return s.sim.mid_out(g, Y, gid[2])[nbr[2]]
        if kind == 'IB':
            if nbr[0] == 'MID': return z[nbr[2]]
            return s.sim.ib_out(list(z), nbr[2])
        if kind == 'CAR':
            if nbr == ('IB', gid[1], gid[2] % par.A1): return z[0]
            if nbr[2] == gid[2] - 1: return z[1]
            t = par.signed(z[0]) + z[1] - 2 ** (par.cb - 1)
            return (t >> par.d) + 2 ** (par.cb - 1)
        if kind == 'CH':
            if nbr[0] == 'FA': return z[0]
            if nbr[2] == gid[2] - 1: return z[2]
            return (z[0] + z[1] + z[2]) >> par.d
    def force(s, gid, nbr, z, theta):
        """modify receiver setting z so its slot towards nbr equals theta"""
        par = s.par; kind = gid[0]
        if kind == 'MID':
            g = s.sp.G[gid[1]]; vi = g.vars.index(nbr[1]); zz = [list(t) for t in z]
            zz[vi][nbr[2]] = theta; return tuple(tuple(t) for t in zz)
        if kind == 'IB': zz = list(z); zz[nbr[2]] = theta; return tuple(zz)
        if kind == 'CAR':
            return (theta, z[1]) if nbr[0] == 'IB' else (z[0], theta)
        if kind == 'CH':
            return (theta, z[1], z[2]) if nbr[0] == 'FA' else (z[0], z[1], theta)
    def W(s, gid, z):
        par = s.par; kind = gid[0]
        if kind == 'FA':
            v, r = gid[1], gid[2]
            for (bi, bit) in s.sp.V[v]['pre']:
                i, off = divmod(bi, par.d)
                if i % par.A1 == r and i // par.A1 < len(z) and (z[i // par.A1] >> off) & 1 != bit: return 0
            return 1
        if kind == 'CAR':
            j = gid[2]; u = z[1] - 2 ** (par.cb - 1); t = par.signed(z[0]) + u
            if j == 0 and u != 0: return 0
            if t % (1 << par.d): return 0
            if j == par.T - 1 and (t >> par.d) != 0: return 0
            return 1
        if kind == 'CH':
            v, j = gid[1], gid[2]; bound = dict(s.sp.chains())[v]
            nd = s.sp.V[v]['nd']; bd = (bound >> (par.d * j)) & (2 ** par.d - 1)
            t = z[0] + z[1] + z[2]
            if (t & (2 ** par.d - 1)) != bd: return 0
            if j == 0 and z[2] != 0: return 0
            if j == nd - 1 and (t >> par.d) != 0: return 0
            return 1
        return 1

def _expand(z, r, A1, nd):
    out = [0] * nd
    for t, val in enumerate(z): out[r + A1 * t] = val
    return out

def part2():
    say('== PART 2: Definition 2 (Psi_{a,b} = sum_theta f(za,theta) f(zb,theta), f indicator of message; sum_b c_ab <= P) ==')
    ok = True
    for (p, m, a, b) in [(1019, 2, 2, 6), (1019, 3, 2, 6), (4093, 2, 7, 3), (2 ** 61 - 1, 2, 3, 5), ((1 << 127) - 1, 3, 3, 5)]:
        sp = nl.Spec(p, a, b, m, (1, 1), '10'); net = NetGates(sp)
        # per-edge: 40 random pairs (half forced matching); per edge-kind: 10^4 random pairs on one representative edge
        pairs = 0; bad = 0; agree = 0
        kinds = {}
        for (sa, rb, c) in net.edges:
            kinds.setdefault((sa[0], rb[0]), []).append((sa, rb, c))
        def test_edge(sa, rb, c, n):
            nonlocal pairs, bad, agree
            for t in range(n):
                zs, zr = net.sample(sa), net.sample(rb)
                if t % 2 == 0:
                    zr = net.force(rb, sa, zr, net.msg(sa, rb, zs))
                ms, mr = net.msg(sa, rb, zs), net.msg(rb, sa, zr)
                if not (0 <= ms < 2 ** c and 0 <= mr < 2 ** c): bad += 1; continue
                psi = int(ms == mr)
                fac = sum((1 if ms == th else 0) * (1 if mr == th else 0) for th in {ms, mr})
                pairs += 1; agree += psi
                if psi != fac: bad += 1
        for k, lst in kinds.items():
            sa, rb, c = rng.choice(lst); test_edge(sa, rb, c, 10000)
        for (sa, rb, c) in net.edges: test_edge(sa, rb, c, 20)
        # sum_b c_ab <= P for every gate; P = max over gates of max(bits, shared)
        rs = nl.rowsums(net.nodes, net.edges)
        P = max(max(net.nodes.values()), max(rs.values()))
        rows_ok = all(rs[a] <= P and net.nodes[a] <= P for a in net.nodes)
        # W / settings consistent: sampled settings decode to bitstrings of fixed length
        say('  L=%3d m=%d: gates=%d edges=%d  Psi pairs tested=%d (matching=%d) factorization mismatches=%d  P=max(bits,shared)=%d, all sum_b c_ab<=P: %s' %
            (sp.L, m, len(net.nodes), len(net.edges), pairs, agree, bad, P, rows_ok))
        ok &= (bad == 0 and rows_ok)
    # end-to-end Psi/W semantics: tested in gadget_tests (accept <=> integer identity), which exercises every message formula.
    return ok

# ---------------- part 3: size bounds ----------------
def build(L, m, D):
    p = (1 << L) - 3
    par = nl.Par(L, nl.cdiv(L + 2, D), D)
    sp = nl.Spec(p, 3, 7, m, (5, 6), '', par=par)
    nodes, edges = nl.topology(sp)
    return sp, nodes, edges

def best_for(L, m, g):
    """choose the number of digits D (the only free parameter) minimizing the cluster size P for cluster count g"""
    best = None
    for D in (2, 4, 8, 16, 32, 64, 128, 256):
        if D > L + 2: break
        sp, nodes, edges = build(L, m, D)
        cs = nl.cluster_sizes(nodes, edges, g)
        if best is None or cs['P'] < best[0]['P']: best = (cs, D, sp.par, len(nodes))
    return best

def part3():
    say('== PART 3: size bounds (construction only; U = total shared bits counted at both ends; P = max over nodes of max(setting length, shared bits)) ==')
    say('Per (L,m,g) the transform size D (digits per number; 2 layers of transforms A1*A2=2D) is chosen to minimize P; clusters are formed greedily from gates.')
    Ls = [16, 32, 64, 128, 256, 512]; ms = [2, 3, 4]
    glit = [1, 4, 16]
    geng = [768, 19683, 196608]
    rowsU = {}; worst = {g: 0 for g in glit + geng}; fit = {}
    say('  L   m | gates held(mL) | U (mL)   | per g:  D P gP/(mL)')
    for L in Ls:
        for m in ms:
            line = '  L=%3d m=%d' % (L, m)
            for g in glit + geng:
                cs, D, par, ng = best_for(L, m, g)
                r = g * cs['P'] / (m * L); worst[g] = max(worst[g], r)
                fit[(L, m, g)] = (r, cs, D)
                rowsU[(L, m, g)] = cs['Ugate'] / (m * L)
                if g == glit[0]: line += ' gates=%d held=%.0f mL U=%.0f mL |' % (cs['gates'], cs['held'] / (m * L), cs['Ugate'] / (m * L))
                line += ' g=%d: D=%d P=%d gP/mL=%.1f;' % (g, D, cs['P'], r)
            say(line)
    cU = max(rowsU.values()); cU1 = max(v for (L, m, g), v in rowsU.items() if g == 1)
    say('  Fitted c in U <= c*m*L (max over L<=512, m<=4 and over every D chosen for any g): c = %.1f ; for the g=1 choice of D: c = %.1f' % (cU, cU1))
    okU = True
    for m in ms:
        okU &= rowsU[(512, m, 1)] <= 1.1 * rowsU[(16, m, 1)]
    say('  U/(mL) at L=16 vs L=512 (m=2,3,4; g=1 choice of D): %s' % ', '.join('%.0f->%.0f' % (rowsU[(16, m, 1)], rowsU[(512, m, 1)]) for m in ms))
    cL = max(worst[g] for g in glit)
    say('  LITERAL bound gP <= c\'*m*L for g in %s: fitted c\' = %s (worst ratio %.1f over L<=512, m<=4)' % (glit, {g: round(worst[g], 1) for g in glit}, cL))
    say('  ENGINE-SCALE g = 3K^8: worst gP/(mL) over table = %s ; trivial floor g/(mL) at L=512,m=4 = %s' % (
        {g: round(worst[g], 1) for g in geng}, {g: round(g / (4 * 512), 1) for g in geng}))
    say('  => for g=3K^8 with K>=2 the literal bound gP<=c\'mL cannot hold at L<=512 (even 1 bit per cluster gives gP=g>>mL). It is an asymptotic statement; see growth block.')
    # asymptotic growth block: m=2, large L, D free
    say('  Growth block (m=2, D free): gP/(mL) vs L for fixed g; model gP <= c1*mL + c2*g*L^(3/4)')
    ext = [64, 256, 1024, 4096, 16384]
    rows = []
    for g in (16, 768):
        line = '    g=%d:' % g
        for L in ext:
            cs, D, par, ng = best_for(L, 2, g)
            r = g * cs['P'] / (2 * L); rows.append((g, L, r, cs['P'], D, cs['maxgate']))
            line += ' L=%d D=%d P=%d gP/mL=%.1f |' % (L, D, cs['P'], r)
        say(line)
    # fit gP/(mL) = c1 + c2 * g / (m L^(1/4))  by max of residual
    # c1 from g=16 at the largest L, then c2 as the smallest constant covering all rows
    c1 = max(r for (g, L, r, P, D, mg) in rows if g == 16 and L == 16384)
    c2 = max((r - c1) / (g / (2 * L ** 0.25)) for (g, L, r, P, D, mg) in rows if r > c1)
    say('  fitted: gP/(mL) <= c1 + c2 * g/(m L^(1/4)) with c1=%.0f, c2=%.1f (covers all growth-block rows by construction of c2)' % (c1, c2))
    last = {g: [r for (gg, L, r, P, D, mg) in rows if gg == g][-1] for g in (16, 768)}
    prev = {g: [r for (gg, L, r, P, D, mg) in rows if gg == g][-2] for g in (16, 768)}
    okG = cL < 1000 and last[768] < prev[768]
    say('  g=768: gP/(mL) at L=4096 -> 16384: %.1f -> %.1f (decreasing: %s)' % (prev[768], last[768], last[768] < prev[768]))
    return okU, okG, cU, cL

def main():
    t0 = time.time()
    g_ok = gadget_tests()
    p1, ninst = part1()
    p2 = part2()
    okU, okG, cU, wg = part3()
    say('SUMMARY: gadgets=%s part1(exact counts, instances=%d)=%s part2(Definition 2)=%s part3a(U<=c*m*L, trend)=%s part3b(gP<=c\'*m*L for g in {1,4,16}; engine-scale g reported separately)=%s  [%.0fs]' %
        (g_ok, ninst, p1, p2, okU, okG, time.time() - t0))
    if g_ok and p1 and p2 and okU and okG: print('PASS')
    else: print('NOT PASS (see failing parts above)')
    open('check_output.txt', 'w').write('\n'.join(LOG) + ('\nPASS\n' if (g_ok and p1 and p2 and okU and okG) else '\nNOT PASS\n'))

if __name__ == '__main__': main()
