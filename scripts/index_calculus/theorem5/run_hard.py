# hard cases: non-cyclic with n2>=3 (rank-2 Sylow of odd / prime-power order) + stress variants
import sys, random
from myic import *
from run30 import classify, pick_P
def find_nc(rng, minn2):
    while True:
        p = rng.choice([q for q in range(500, 10000) if isprime(q)])
        # bias: p = 1 mod 3 / 4 / 5 helps full l-torsion
        A, B = rng.randrange(1, p), rng.randrange(p)
        if (4*A**3+27*B*B) % p == 0: continue
        C = Curve(p, A, B); fN = factor(C.N)
        if C.N < 100: continue
        e, n2 = classify(C, fN, rng)
        if n2 and n2 >= minn2: return C, fN, e
if __name__ == "__main__":
    rng = random.Random(777); ok = tot = 0
    for i in range(12):
        C, fN, e = find_nc(rng, 3)
        kind = ['max','small','rand'][i%3]
        P, oP = pick_P(C, fN, e, kind, rng)
        d0 = rng.randrange(oP); Q = C.mul(d0, P)
        d, rounds, diag = run_instance(C, P, Q, rng, fN)
        good = d is not None and d % oP == d0 % oP; ok += good; tot += 1
        print(f"{'OK ' if good else 'FAIL'} p={C.p} N={C.N}={fN} exp={e} n2={C.N//e} {kind} ordP={oP} d={d0} got={None if d is None else d%oP} rounds={rounds} diag={diag}", flush=True)
    print(f"SUMMARY hard noncyclic n2>=3: {ok}/{tot}")
