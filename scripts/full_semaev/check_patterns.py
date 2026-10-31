"""Checker: pattern-sum == direct enumeration of the FULL Semaev bounded decomposition problem (toy)."""
import itertools, math, random, sys, time
import netlib as nl, patterns as pt, brute_force as bf

rng = random.Random(100)
T0 = time.time()
def say(*a): print(*a, flush=True)

def classify(tup, p, a):
    """independent pattern of a tuple from the group law: letters for steps 2..m; plus final sum (None = O)"""
    S = tup[0]; word = ''
    for k in range(1, len(tup)):
        P = tup[k]
        if S is None: word += 'S'; S = P; continue
        if S[0] != P[0]: word += 'A'
        elif S[1] == P[1] and S[1] != 0: word += 'D'
        else: word += 'C'                      # P = -S (includes y = 0)
        S = bf.add(S, P, p, a)
    return word, S

def solve_q(g, base):
    """fill the (single) q variable of gadget g: q = (E + O p)/p floor, so value == 0 iff divisible"""
    qs = [v for v in g.vars if v[0] == 'q' and v not in base]
    if not qs: return {}
    assert len(qs) == 1, (g.name, qs)
    q = qs[0]; d = dict(base); d[q] = 0
    v0 = g.value(d)                  # = E + O p   (the coefficient of q is -p)
    coef = [sg * c for (sg, v, c) in g.lin if v == q][0]; assert coef < 0
    return {q: v0 // (-coef)}

def accept_free(sp, base):
    """base: values for all non-q variables. accepts iff the integer system has (unique) q-completion"""
    vals = dict(base)
    for g in sp.G:
        qq = solve_q(g, vals)
        for k, v in qq.items():
            if not 0 <= v < 2 ** (sp.par.d * sp.V[k]['nd']): return None
            vals[k] = v
    return vals if sp.int_accept(vals) else None

# ---------------------------------------------------------------- Part 1
def part1():
    say('== PART 1: exhaustive soundness, m = 2, all non-q variables free (x0,x1 < B; y0,y1,w,lam in [0,p)); R forced by xsum/ysum ==')
    ok = True
    for p in (7, 11, 13, 17):
        Bp = bf.ceil_root(p, 2)
        best = None
        for a0 in range(p):
            for b0 in range(p):
                if (4 * a0 ** 3 + 27 * b0 * b0) % p == 0: continue
                n = sum(1 for P in bf.curve_points(p, a0, b0) if P[0] < Bp)
                if best is None or n > best[0]: best = (n, a0, b0)
        _, a, b = best
        pts = bf.curve_points(p, a, b); B = bf.ceil_root(p, 2)
        FB = [P for P in pts if P[0] < B]
        want = {}                       # (tuple, R) -> word   (direct)
        for t in itertools.product(FB, repeat=2):
            wd, S = classify(t, p, a)
            want[(t, S)] = wd
        got = {}
        for word in ('A', 'D'):
            for x0, y0, x1, y1, w, lam in itertools.product(range(B), range(p), range(B), range(p), range(p), range(p)):
                # R forced by the sum identities (any other R fails xsum or ysum, being linear in R)
                if word == 'A': e2 = lam * lam - x0 - x1
                else: e2 = lam * lam - 2 * x0
                R = (e2 % p, (lam * (x0 - e2 % p) - y0) % p)
                sp = PS(p, a, b, 2, R, word)
                base = dict(x0=x0, y0=y0, u0=x0 * x0, x1=x1, y1=y1, u1=x1 * x1, w1=w, lam1=lam)
                vals = accept_free(sp, base)
                if vals is not None:
                    key = ((((x0, y0), (x1, y1))), R)
                    got.setdefault(key, []).append(word)
        for x0, y0, x1, y1 in itertools.product(range(B), range(p), range(B), range(p)):
            sp = PS(p, a, b, 2, None, 'C')
            vals = accept_free(sp, dict(x0=x0, y0=y0, u0=x0 * x0, x1=x1, y1=y1, u1=x1 * x1))
            if vals is not None: got.setdefault((((x0, y0), (x1, y1)), None), []).append('C')
        bad = [k for k in got if len(got[k]) != 1] + [k for k in got if k not in want] + [k for k in want if k not in got]
        bad += [k for k in got if k in want and got[k][0] != want[k]]
        agree = len(bad) == 0
        ok &= agree
        say('  p=%d a=%d b=%d B=%d |FB|=%d: accepted (tuple,R) pairs=%d, direct pairs=%d, by word %s, each pair accepted by exactly its own word: %s'
            % (p, a, b, B, len(FB), len(got), len(want), {w: sum(1 for v in got.values() if v[0] == w) for w in 'ADC'}, agree))
        if bad: say('   BAD (first 5):', bad[:5])
    return ok

_cache = {}
def PS(p, a, b, m, R, word, prefix=''):
    key = (p, a, b, m, R, word, prefix)
    if key not in _cache:
        if len(_cache) > 200000: _cache.clear()
        _cache[key] = pt.PSpec(p, a, b, m, R, word, prefix)
    return _cache[key]

# ---------------------------------------------------------------- Part 2
def curves_for(p, k):
    out = []
    tries = 0
    while len(out) < k and tries < 200:
        tries += 1
        a, b = rng.randrange(p), rng.randrange(p)
        if (4 * a ** 3 + 27 * b * b) % p == 0 or (a, b) in out: continue
        out.append((a, b))
    return out

def part2(primes, ms, ncurves):
    say('== PART 2: full tuples: sum over patterns of network counts == direct enumeration, all R incl. O ==')
    allok = True
    tot = dict(tors=0, inst=0, tuples=0, degenerate=0, pairs=0, wrongR=0, byclass={})
    for p in primes:
        for (a, b) in curves_for(p, ncurves):
            for m in ms:
                if m == 4 and p > 61: continue
                if m == 3 and p > 199: continue
                B, F, full, gen = bf.distribution(p, a, b, m)
                Rset = set(full) | {None}
                if len(F) ** m > 120000: continue
                pairs = 0
                # network count per R (and the one-pattern check) via tuples in FB^m
                Z = {}
                for t in itertools.product(F, repeat=m):
                    wd, Rt = classify(t, p, a)
                    tot['tuples'] += 1
                    if any(P[1] == 0 for P in t): tot['tors'] += 1
                    if 'A' * (m - 1) != wd: tot['degenerate'] += 1
                    tot['byclass'][wd] = tot['byclass'].get(wd, 0) + 1
                    # all words valid for the true R: exactly one accepts, and it is the independent classification
                    acc = [w for w in pt.words(m, Rt is None)
                           if PS(p, a, b, m, Rt, w).int_accept(PS(p, a, b, m, Rt, w).witness(t))]
                    pairs += 1
                    if acc != [wd]:
                        allok = False; say('  MISMATCH p=%d a=%d b=%d m=%d tuple=%s true=%s accepted=%s' % (p, a, b, m, t, wd, acc)); break
                    Z[Rt] = Z.get(Rt, 0) + 1
                    # one wrong R: nothing accepts
                    Rw = rng.choice(sorted(Rset - {Rt}, key=lambda r: (r is not None, r))) if len(Rset) > 1 else None
                    if Rw != Rt:
                        for w in pt.words(m, Rw is None):
                            s2 = PS(p, a, b, m, Rw, w)
                            if s2.int_accept(s2.witness(t)):
                                allok = False; say('  WRONG R ACCEPTED', p, a, b, m, t, Rw, w)
                        tot['wrongR'] += 1
                direct = {R: len(v) for R, v in full.items()}
                # direct count of tuples summing to O (bf.distribution drops S=None): recompute
                cntO = 0
                for t in itertools.product(F, repeat=m):
                    if classify(t, p, a)[1] is None: cntO += 1
                direct[None] = cntO
                agree = all(Z.get(R, 0) == direct.get(R, 0) for R in Rset | set(Z))
                allok &= agree
                tot['inst'] += 1; tot['pairs'] += pairs
                if not agree: say('  COUNT MISMATCH', p, a, b, m)
        say('  p=%-4d done (instances so far %d, tuples %d, non-generic tuples %d)  [%.0fs]' % (p, tot['inst'], tot['tuples'], tot['degenerate'], time.time() - T0))
    say('PART 2 totals: instances=%d tuples=%d non-generic tuples=%d (each accepted by exactly its own pattern) wrong-R tests=%d; tuples containing a 2-torsion point (y=0)=%d' % (tot['inst'], tot['tuples'], tot['degenerate'], tot['wrongR'], tot['tors']))
    say('tuples by pattern letter-word (all instances):', dict(sorted(tot['byclass'].items())))
    return allok, tot

def part2b():
    say('== PART 2b: prefix-restricted counts: pattern-sum == direct, several prefixes ==')
    ok = True; n = 0
    for (p, m) in [(53, 2), (101, 2), (31, 3), (61, 3), (23, 4)]:
        for (a, b) in curves_for(p, 2):
            B, F, full, gen = bf.distribution(p, a, b, m)
            ell = max(1, (B - 1).bit_length())
            for _ in range(8):
                pref = ''.join(rng.choice('01') for _ in range(rng.randrange(0, m * ell + 1)))
                Z = {}; D = {}
                for t in itertools.product(F, repeat=m):
                    wd, Rt = classify(t, p, a)
                    xs = ''.join(format(P[0], '0%db' % ell) for P in t)
                    if xs.startswith(pref): D[Rt] = D.get(Rt, 0) + 1
                for Rt in set(D) | set(full) | {None}:
                    z = 0
                    for t in itertools.product(F, repeat=m):
                        for w in pt.words(m, Rt is None):
                            s = PS(p, a, b, m, Rt, w, pref)
                            z += s.int_accept(s.witness(t))
                    Z[Rt] = z
                agree = all(Z[R] == D.get(R, 0) for R in Z)
                ok &= agree; n += 1
                if not agree: say('  PREFIX MISMATCH', p, a, b, m, pref)
    say('  prefix instances compared: %d  all equal: %s' % (n, ok))
    return ok

# ---------------------------------------------------------------- Part 3
def part3():
    say('== PART 3: gate-level (Schoenhage-Strassen) Sim.accept == integer system, on D / C / S patterns ==')
    ok = True; nacc = 0; nrej = 0; nbad = 0
    for p in (37, 41, 53, 61):
        for (a, b) in curves_for(p, 1):
            for m in (2, 3):
                B, F, full, gen = bf.distribution(p, a, b, m)
                tuples = list(itertools.product(F, repeat=m)); rng.shuffle(tuples)
                done = {}
                for t in tuples:
                    wd, Rt = classify(t, p, a)
                    if done.get(wd, 0) >= 3: continue
                    done[wd] = done.get(wd, 0) + 1
                    sp = PS(p, a, b, m, Rt, wd); w = sp.witness(t); sim = nl.Sim(sp)
                    g = sim.accept(w); i = sp.int_accept(w)
                    if not (g == 1 and i == 1): ok = False; say('  gate/integer mismatch', p, m, wd, g, i)
                    nacc += 1
                    for _ in range(25):
                        v = rng.choice(list(w)); w2 = dict(w)
                        w2[v] ^= 1 << rng.randrange(sp.par.d * sp.V[v]['nd'])
                        if w2[v] == w[v]: continue
                        if sim.accept(w2) != sp.int_accept(w2): ok = False; nbad += 1
                        elif sim.accept(w2): nbad += 1
                        else: nrej += 1
                    # wrong word, forced witness: must be rejected at gate level
                    for w_alt in pt.words(m, Rt is None):
                        if w_alt == wd: continue
                        s2 = PS(p, a, b, m, Rt, w_alt); wv = s2.witness(t)
                        if wv is not None and nl.Sim(s2).accept(wv): ok = False; nbad += 1
                        else: nrej += 1
    say('  true decompositions accepted at gate level=%d, perturbed/wrong-word witnesses rejected=%d, wrongly accepted=%d' % (nacc, nrej, nbad))
    return ok and nbad == 0

# ---------------------------------------------------------------- Part 4 (topology)
def part4():
    say('== PART 4: topology sizes (exact U, held bits, largest gate) for every word, vs the all-A baseline and the L33 bound ==')
    ok = True
    rows = []
    for L in (16, 24, 40, 64, 128, 256, 512, 1024, 2048):
        p = (1 << L) - 1 if L % 2 else (1 << L) - 3          # any odd integer with bit length L; no primality used by the topology
        for m in (2, 3, 4, 5, 6):
            worst = None
            for Ris_O in (False, True):
                for w in pt.words(m, Ris_O):
                    sp = pt.PSpec(p, 0, 7, m, None if Ris_O else (1, 2), w)
                    nodes, edges = nl.topology(sp)
                    U = 2 * sum(c for _, _, c in edges); H = sum(nodes.values())
                    rs = nl.rowsums(nodes, edges)
                    wmax = max(nodes[x] + rs[x] for x in nodes)
                    uses = {}
                    for g in sp.G:
                        for v in g.vars: uses[v] = uses.get(v, 0) + 1
                    r = (U, H, wmax, len(sp.G), max(uses.values()), w, Ris_O)
                    if worst is None or U > worst[0]: worst = r
            base = pt.PSpec(p, 0, 7, m, (1, 2), 'A' * (m - 1))
            nb, eb = nl.topology(base); Ub = 2 * sum(c for _, _, c in eb)
            U, H, wmax, G, mu, w, R_O = worst
            c1 = U / (m * L)
            ok &= (c1 <= 1410) and (wmax <= 216 * L ** 0.75)
            say('  L=%4d m=%d: baseline(all A) U/(mL)=%7.1f | worst word %-6s (R=O:%s) U/(mL)=%7.1f (x%.3f of baseline) G=%d max-uses=%d  U+H over mL=%.0f  wmax/L^(3/4)=%.1f'
                % (L, m, Ub / (m * L), w, R_O, c1, U / Ub, G, mu, (U + H) / (m * L), wmax / L ** 0.75))
    return ok

def main():
    primes = [q for q in range(5, 200) if all(q % r for r in range(2, int(q ** .5) + 1))]
    res = {}
    res['p1'] = part1()
    res['p2'], tot = part2(primes, (2, 3, 4), 3)
    res['p2b'] = part2b()
    res['p3'] = part3()
    res['p4'] = part4()
    say(res)
    say('PASS' if all(res.values()) and tot['degenerate'] > 0 else 'FAIL')
main()
