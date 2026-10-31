#!/usr/bin/env python3
"""End-to-end toy.  usage: run_toy.py LO HI SEED TRIALS"""
import sys, random, math, collections
import numpy as np
from toy_l62 import *
import l47_base as B47

lo, hi, seed, trials = (int(a) for a in sys.argv[1:5])
B47.PRIMES = [q for q in range(lo, hi) if all(q % r for r in range(2, int(q ** .5) + 1))]
rng = random.Random(seed)
inst = B47.find_instances(rng)
print("INSTANCES:")
for k, v in inst.items(): print(f"  {k}: p={v[0]} N={v[3]}={factor(v[3])} G~Z/{v[4]}xZ/{v[5]}")
configs = [("zsigma", "mix"), ("rref", "raw"), ("zsigma", "ph")]
tot = collections.Counter(); good = collections.Counter()
smin_field = collections.defaultdict(list); smin_pp = collections.defaultdict(list)
defects = []; levels_seen = []
for cat, (p, A, Bc, N, n1, n2) in inst.items():
    C = Curve(p, A, Bc); fN = factor(N)
    for kind in ("gen", "small", "any"):
        try: P, o = B47.pick_points(C, N, fN, n1, rng, kind)
        except Exception: continue
        if o == 1: continue
        for t in range(trials):
            d = rng.randrange(o); Q = C.mul(d, P)
            for fm, pm in configs:
                d2, st = run_instance(C, P, Q, N, fN, rng, fm, pm, expG=n1)
                okk = d2 is not None and (d2 - d) % o == 0 and C.mul(d2, P) == Q
                key = (cat, fm + "/" + pm)
                tot[key] += 1; good[key] += okk
                if st:
                    for (l, v), inf in st['per'].items():
                        if pm == 'ph': continue
                        (smin_field if v == 1 else smin_pp)[(fm if v == 1 else pm)].append(inf.get('smin')) if inf.get('smin') is not None else None
                        defects.append((cat, l, v, st['f'], st['Nr'], inf.get('defect'), inf.get('kerdim', inf.get('kerdim_free'))))
                        if v >= 2: levels_seen.append((cat, l, v, inf['levels']))
                if not okk: print("FAIL", cat, p, N, kind, d, d2)
print("\nRECOVERY (category, config): good/total")
for k in sorted(tot): print(f"  {k[0]:18s} {k[1]:14s} {good[k]}/{tot[k]}")
def summ(xs):
    xs2 = [x for x in xs if x is not None]
    c = collections.Counter(xs2)
    return f"n={len(xs)} none={len(xs)-len(xs2)} mean={np.mean(xs2):.2f} max={max(xs2)} hist={dict(sorted(c.items()))}"
print("\nMINIMAL NUMBER s* OF KERNEL VECTORS (prefix of stream) with which Howell recovers d_l")
for k, xs in smin_field.items(): print(f"  field path (v=1), mode {k:7s}: {summ(xs)}")
for k, xs in smin_pp.items(): print(f"  prime-power path (v>=2), mode {k:5s}: {summ(xs)}")
print("\nRANK DEFECT d0 = f - rank_l(E) of the relation matrix (raw, N_r = f+12 rows), by (cat,l,v):")
agg = collections.defaultdict(list)
for cat, l, v, f, Nr, dd, kd in defects: agg[(cat, l, v)].append((dd / f))
for k in sorted(agg): print(f"  {k}: mean d0/f = {np.mean(agg[k]):.3f}  (n={len(agg[k])})")
print("\nSCHUR LEVEL TRACE (first 6 prime-power runs): (depth, n, c, r, defect)")
for x in levels_seen[:6]: print("  ", x)
allok = all(good[k] == tot[k] for k in tot)
print("\nSUMMARY", sum(good.values()), "/", sum(tot.values()))
print("PASS toy_l62" if allok else "FAIL toy_l62")
