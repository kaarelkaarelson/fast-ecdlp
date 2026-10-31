import sys, random, math, time
import numpy as np
from myic import *
def classify(C, fN, rng):
    # exponent via lcm of orders of random points; structure n1 = exponent
    e = 1
    for _ in range(40):
        o = C.order(C.rand_pt(rng), fN); e = e*o//gcd(e, o)
    n2 = C.N // e if C.N % e == 0 else None
    return e, n2
def find(cls, rng):
    while True:
        p = rng.choice([q for q in range(500, 10000) if isprime(q)])
        A, B = rng.randrange(1, p), rng.randrange(p)
        if (4*A**3 + 27*B*B) % p == 0: continue
        C = Curve(p, A, B)
        fN = factor(C.N)
        if C.N < 100: continue
        e, n2 = classify(C, fN, rng)
        if n2 is None: continue
        sqf = all(v == 1 for v in fN.values())
        if cls == 'prime' and len(fN) == 1 and all(v==1 for v in fN.values()) and n2 == 1: return C, fN, e
        if cls == 'cycsqf' and len(fN) > 1 and sqf and n2 == 1: return C, fN, e
        if cls == 'cycpp' and not sqf and n2 == 1 and max(fN.values()) >= 2: return C, fN, e
        if cls == 'cycpp' and not sqf and n2 == 1: return C, fN, e
        if cls == 'noncyc' and n2 > 1: return C, fN, e
N_BIG = 10**9
def pick_P(C, fN, e, kind, rng):
    tries = 0
    while True:
        tries += 1
        T = C.rand_pt(rng); o = C.order(T, fN)
        if kind == 'max':
            if o == e: return T, o
        elif kind == 'rand': return T, o
        else:
            divs = sorted(dd for dd in range(2, min(o, 40)+1) if o % dd == 0)
            if divs and o > 40:
                r = rng.choice(divs[:4]); P = C.mul(o//r, T); return P, r
            if not divs and o > 1 and tries > 300:
                pf = min(factor(o)); return C.mul(o//pf, T), pf
if __name__ == "__main__":
    seed = int(sys.argv[1]); n_per = int(sys.argv[2])
    rng = random.Random(seed)
    kinds = ['max', 'small', 'rand']
    tot = ok = 0
    t0 = time.time()
    for cls in ['prime', 'cycsqf', 'cycpp', 'noncyc']:
        for i in range(n_per):
            C, fN, e = find(cls, rng)
            kind = kinds[i % 3] if cls != 'prime' else ['max','rand','max'][i%3]
            P, oP = pick_P(C, fN, e, kind, rng)
            d0 = rng.randrange(oP); Q = C.mul(d0, P)
            d, rounds, diag = run_instance(C, P, Q, rng, fN)
            tot += 1
            good = d is not None and d % oP == d0 % oP
            ok += good
            fullflag = None if diag is None else all(x[1] for x in diag)
            print(f"{'OK ' if good else 'FAIL'} cls={cls:6s} p={C.p} N={C.N}={'*'.join(f'{l}^{v}' if v>1 else str(l) for l,v in fN.items())} exp={e} n2={C.N//e} Pkind={kind} ordP={oP} d={d0} got={None if d is None else d%oP} rounds={rounds} span==K_l:{fullflag}", flush=True)
    print(f"SUMMARY {ok}/{tot} recovered d correctly; {time.time()-t0:.0f}s")
    print("PASS" if ok >= 0.93*tot else "NOT PASS")
