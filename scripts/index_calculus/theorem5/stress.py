# stress: (1) B1,B2 inside <P> (S != G) with small ord P, (2) too few rows (Nr=f+1) -> must never output wrong d
import random, math, numpy as np
import myic
from myic import *
from run30 import find, pick_P
rng = random.Random(4242)
# (1) monkeypatch rand_pt to return multiples of P
wrong = none = good = 0
for i in range(10):
    C, fN, e = find('cycpp' if i%2 else 'noncyc', rng)
    P, oP = pick_P(C, fN, e, 'small', rng)
    d0 = rng.randrange(oP); Q = C.mul(d0, P)
    old = Curve.rand_pt
    Curve.rand_pt = lambda s, r, P=P, oP=oP: s.mul(r.randrange(1, oP), P) if oP>1 else P
    d, rounds, diag = run_instance(C, P, Q, rng, fN, maxrounds=6)
    Curve.rand_pt = old
    if d is None: none += 1
    elif d % oP == d0 % oP: good += 1
    else: wrong += 1
    print("S=<P> case: N=%d ordP=%d -> %s rounds=%d" % (C.N, oP, 'none' if d is None else ('ok' if d%oP==d0 else 'WRONG'), rounds), flush=True)
print("stress(1): ok=%d none=%d WRONG=%d" % (good, none, wrong))
