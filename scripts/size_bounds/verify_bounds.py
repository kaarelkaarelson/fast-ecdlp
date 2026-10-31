#!/usr/bin/env python3
"""Checker: closed-form size bounds for the decomposition network under the clean parameter
choice (netlib.choose_par_clean).  Construction only (topology), no witness/simulation.
Run: nice -n 19 taskpolicy -b python3 verify_bounds.py      (prints PASS only if everything holds)"""
import math, sys, time
import netlib as nl
from netlib import cdiv

C1, CW, C2, C3 = 1410, 2140, 2250, 1    # constants claimed in PROOF.md (U <= C1 m L, U+H <= CW m L, g P <= C2 m L for g <= C3 L^(1/4))
MS = (2, 3, 5, 8, 16)

def isqrt_root(p, m):                  # smallest B with B^m >= p
    lo, hi = 1, 1 << (cdiv(p.bit_length(), m) + 2)
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** m >= p: hi = mid
        else: lo = mid + 1
    return lo

def params(L):
    """closed-form parameters (independent of netlib.Par)."""
    D = 4
    while 2 * D * D < L: D *= 2
    k = D.bit_length() - 1
    T = 2 * D; A1 = 2 ** cdiv(k + 1, 2); A2 = T // A1
    d = cdiv(L + 2, D)
    return dict(D=D, k=k, T=T, A1=A1, A2=A2, h=D // A1, d=d)

def var_classes(L, m, ell, d):
    """(count, bits, uses, ranged): uses = number of gadgets containing the variable."""
    cl = [(1, ell, 6, True), (m - 1, ell, 5, True), (1, L, 3, True), (m - 1, L, 2, True),
          (m, 2 * ell, 2, False), (m, L + 2, 1, False),
          (m - 1, L, 1, True), (m - 1, L, 3, True), (4 * (m - 1), L + 2, 1, False),
          (m - 2, L, 6, True), (m - 2, L, 3, True)]
    return [(c, b, u, r) for (c, b, u, r) in cl if c > 0]

def closed_forms(L, m, ell, par):
    """exact closed forms: U (= 2 * sum of edge widths), H (= total held bits), node count"""
    D, T, A1, A2, d = par['D'], par['T'], par['A1'], par['A2'], par['d']
    fw, cb = par['fw'], par['cb']
    G = 6 * m - 4
    S = 0; sumnd = 0; chains = 0; chain_held = 0; ranged_nd = 0; fa_nodes = 0
    for (c, bits, uses, rg) in var_classes(L, m, ell, d):
        nd = cdiv(bits, d)
        S += c * uses * min(A1, nd); sumnd += c * nd; fa_nodes += c * min(A1, nd)
        if rg:
            chains += c * (nd * d + nd - 1); chain_held += c * nd * (2 * d + 1); ranged_nd += c * nd
    U = 2 * (A2 * S * fw + G * (2 * T * fw + (T - 1) * cb) + chains)
    H = d * sumnd + A2 * S * fw + G * (T * fw + T * (fw + cb)) + chain_held
    nn = fa_nodes + G * (A2 + A1 + T) + ranged_nd
    return dict(U=U, H=H, nodes=nn, S=S, G=G)

def upper_bounds(L, m, par):
    """closed-form upper bounds as functions of (L,m,D,k,d) only"""
    D, k, d, A1 = par['D'], par['k'], par['d'], par['A1']
    fwB = 2 * d + D + k + 5
    TfwB = 2 * D * fwB
    UB = 2 * ((45 * m - 36) * TfwB + (6 * m - 6) * (L + 2 + d + D))
    HB = 12 * m * (L + 2 + d) + (27 * m - 24) * TfwB + 3 * (6 * m - 4) * TfwB + (6 * m - 6) * (2 * (L + 2 + d) + D)
    wB = 13 * A1 * fwB
    return dict(fwB=fwB, TfwB=TfwB, UB=UB, HB=HB, wB=wB)

def cluster(nodes, rs, edges, g, W):
    """explicit assignment: nodes in construction order, cluster = floor(g * (weight of earlier nodes) / W)."""
    asg = {}; acc = 0
    for a in nodes:
        asg[a] = acc * g // W; acc += nodes[a] + rs[a]
    bits = [0] * g; row = [0] * g; wt = [0] * g
    for a in nodes: bits[asg[a]] += nodes[a]; wt[asg[a]] += nodes[a] + rs[a]
    for a, b, c in edges:
        if asg[a] != asg[b]: row[asg[a]] += c; row[asg[b]] += c
    return bits, row, wt

def check_instance(L, m, p, errs, stats):
    par0 = params(L)
    sp = nl.Spec(p, 3, 7, m, (5, 6), '', par=nl.choose_par_clean(L))
    P = sp.par
    # (E5) parameters
    ok = (P.D == par0['D'] and P.T == par0['T'] and P.A1 == par0['A1'] and P.A2 == par0['A2'] and P.d == par0['d'] and P.h == par0['h'])
    ok &= (L <= 2 * P.D ** 2 < 4 * L + 1) or P.D == 4
    ok &= P.D * P.D < 2 * L or P.D == 4
    par = dict(par0, fw=P.fw, cb=P.cb, M=P.M)
    ell = isqrt_root(p, m).__sub__(1).bit_length() or 1
    ok &= (ell == sp.ell)
    fwB = 2 * par['d'] + par['D'] + par['k'] + 5
    ok &= P.fw <= fwB and P.M % P.D == 0 and P.cb < P.fw and P.A2 <= P.A1
    ok &= P.A1 ** 2 >= P.T and P.A1 ** 2 <= 4 * P.D and P.h <= P.A1
    if not ok: errs.append(('params', L, m)); return
    nodes, edges = nl.topology(sp)
    rs = nl.rowsums(nodes, edges)
    U = 2 * sum(c for _, _, c in edges); H = sum(nodes.values()); W = U + H
    # (E1) exact closed forms
    cf = closed_forms(L, m, sp.ell, par)
    if (cf['U'], cf['H'], cf['nodes']) != (U, H, len(nodes)): errs.append(('exact', L, m, cf, U, H)); return
    # variable usage counts: 6 max, sum 27m-24
    use = {}
    for g in sp.G:
        for v in g.vars: use[v] = use.get(v, 0) + 1
    if max(use.values()) > 6 or sum(use.values()) != 27 * m - 24 or len(sp.G) != 6 * m - 4: errs.append(('usage', L, m)); return
    # (E3) upper bounds
    ub = upper_bounds(L, m, par)
    if not (U <= ub['UB'] and H <= ub['HB'] and ub['UB'] <= C1 * m * L and ub['UB'] + ub['HB'] <= CW * m * L): errs.append(('ub', L, m, U, ub, C1 * m * L)); return
    # (E2) per-kind weights
    A1, A2, fw = par['A1'], par['A2'], par['fw']
    wmax = 0
    for a, hb in nodes.items():
        w = hb + rs[a]; wmax = max(wmax, w); kd = a[0]
        lim = {'FA': 7 * A1 * fw, 'MID': 13 * A1 * fw, 'IB': 3 * A2 * fw, 'CAR': 5 * fw, 'CH': 3 * par['d'] + 3}[kd]
        if w > lim: errs.append(('weight', L, m, a, w, lim)); return
    if wmax > ub['wB']: errs.append(('wmax', L, m)); return
    # (E4) clusters
    gs = sorted({1, 2, max(1, int(L ** 0.25)), max(1, math.ceil(L ** 0.25)), 2 * max(1, int(L ** 0.25))} if L < 4096 else {1, int(L ** 0.25), 2 * int(L ** 0.25)})
    worst = 0
    for g in gs:
        bits, row, wt = cluster(nodes, rs, edges, g, W)
        if sum(wt) != W: errs.append(('wsum', L, m, g)); return
        if max(wt) * g >= W + g * wmax: errs.append(('clusterweight', L, m, g, max(wt), W / g + wmax)); return
        Pc = max(max(bits), max(row))
        if Pc > max(wt) or any(r > Pc for r in row): errs.append(('P', L, m, g)); return
        if g <= C3 * L ** 0.25:
            if g * Pc > W + g * ub['wB']: errs.append(('gP-bound', L, m, g)); return
            if W + g * ub['wB'] > C2 * m * L: errs.append(('C2', L, m, g, (W + g * ub['wB']) / (m * L))); return
            worst = max(worst, g * Pc / (m * L))
        stats['gP_actual_max'] = max(stats['gP_actual_max'], g * Pc / (m * L)) if g <= C3 * L ** 0.25 else stats['gP_actual_max']
    stats['U/mL'] = max(stats['U/mL'], U / (m * L)); stats['UB/mL'] = max(stats['UB/mL'], ub['UB'] / (m * L))
    stats['W/mL'] = max(stats['W/mL'], W / (m * L)); stats['WB/mL'] = max(stats['WB/mL'], (ub['UB'] + ub['HB']) / (m * L))
    stats['wmax/L^.75'] = max(stats['wmax/L^.75'], wmax / L ** 0.75); stats['wB/L^.75'] = max(stats['wB/L^.75'], ub['wB'] / L ** 0.75)
    stats['bound(gP) worst'] = max(stats['bound(gP) worst'], (W + int(L ** 0.25) * ub['wB']) / (m * L))

def hand_steps(errs, Lmax=1 << 20):
    """numerically re-check, for EVERY integer L in [16, Lmax], the analytic inequalities used in PROOF.md (steps S1-S11)."""
    for L in range(16, Lmax + 1):
        D = 4
        while 2 * D * D < L: D *= 2
        k = D.bit_length() - 1; d = -(-(L + 2) // D); r = math.sqrt(L)
        F = 2 * d + D + k + 5
        TF = 2 * D * F
        A1 = 2 ** (-(-(k + 1) // 2))
        ok = (L <= 2 * D * D and (D * D < 2 * L))                       # S1
        ok &= d <= math.sqrt(2) * (r + 2 / r) + 1                        # S2
        ok &= TF <= 8 * L + 8 + math.sqrt(2 * L) * (math.log2(2 * L) + 14) # S3
        ok &= TF <= 15.3 * L                                             # S4
        ok &= (L + 2 + d + D <= 2 * L) and (L + 2 + d <= 1.6 * L) and (D <= 0.36 * L)  # S5
        ok &= F <= 6.97 * r                                              # S6
        ok &= A1 <= 2 * math.sqrt(D) and A1 * A1 >= 2 * D and A1 * A1 <= 4 * D and (D // A1) <= A1   # S7
        ok &= 13 * A1 * F <= 216 * L ** 0.75 and 6 * A1 * F <= 100 * L ** 0.75   # S8
        ok &= (2 * (45 * TF + 12 * L) <= 1410 * L)                      # S9 (per unit m)
        ok &= (12 * 1.6 * L + 45 * TF + 6 * (3.2 * L + D) <= 730 * L) and (2 * 45 * TF + 24 * L + 730 * L <= 2140 * L)   # S10 (H <= 730 mL, W <= 2140 mL)
        ok &= (2140 + 216 * 0.5) <= 2250                                  # S11 (gP, g<=L^(1/4), m>=2: 216 g L^.75 <= 108 m L)
        if not ok: errs.append(('hand-step', L)); return False
    return True

def sample_Ls():
    S = set(range(16, 65)) | {2 ** k for k in range(4, 17)} | {2 ** k + 1 for k in range(4, 16)} | {2 ** k - 1 for k in range(5, 17)}
    S |= {3 * 2 ** k for k in range(3, 15)} | {3 * 2 ** k + 1 for k in range(3, 15)}
    x = 65.0
    while x < 65536:
        S.add(int(x)); S.add(int(x) | 1); x *= (1.045 if x < 8192 else 1.12)
    return sorted(l for l in S if 16 <= l <= 65536)

def main():
    t0 = time.time(); errs = []; n = 0
    stats = {k: 0.0 for k in ('U/mL', 'UB/mL', 'W/mL', 'WB/mL', 'wmax/L^.75', 'wB/L^.75', 'gP_actual_max', 'bound(gP) worst')}
    hand_steps(errs); print('hand-proof inequalities S1-S11 checked for every integer L in [16, 2^20]: %s' % ('ok' if not errs else 'FAILED'), flush=True)
    Ls = sample_Ls()
    for L in Ls:
        for m in MS:
            if m > 3 and L > 8192 and L not in (16384, 65536): continue
            if m == 3 and L > 16384 and L != 65536: continue
            if m > 5 and L > 2048: continue
            full = (L & (L - 1) == 0) or L < 65
            for p in (((1 << L) - 3, (1 << (L - 1)) + 1) if full else (((1 << L) - 3,) if L % 4 in (0, 1) else ((1 << (L - 1)) + 1,))):
                check_instance(L, m, p, errs, stats); n += 1
        if errs: break
        if L % 50 == 0 or L in (4096, 65536): print('  ..', L, int(time.time() - t0), 's', flush=True)
        if time.time() - t0 > 1100: errs.append(('time budget exceeded, incomplete sweep', L)); break
    print('L values: %d (min %d, max %d, powers of two %d, odd %d); instances (L,m,p): %d; m in %s' % (
        len(Ls), Ls[0], Ls[-1], sum(1 for l in Ls if l & (l - 1) == 0), sum(1 for l in Ls if l & 1), n, MS))
    for k, v in stats.items(): print('  max %-18s %.3f' % (k, v))
    print('constants: C1=%d (U<=C1 m L), CW=%d (U+H<=CW m L), C2=%d (gP<=C2 m L for g<=%d L^(1/4)), L0=16' % (C1, CW, C2, C3))
    if errs: print('FAIL', errs[:5]); print('NOT PASS'); sys.exit(1)
    print('closed forms exact (U,H,node count), upper bounds >= exact, weights/cluster bounds hold  [%.0fs]' % (time.time() - t0))
    print('PASS')

if __name__ == '__main__': main()
