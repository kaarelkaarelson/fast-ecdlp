import random, sys
from myic import *
import myic
from run30 import find, pick_P
rng = random.Random(int(sys.argv[1])); n = int(sys.argv[2])
for i in range(n):
    cls = ['prime','cycsqf','cycpp','noncyc'][i%4]
    C, fN, e = find(cls, rng)
    P, oP = pick_P(C, fN, e, 'max' if cls=='prime' else ('max' if cls=='prime' else ['max','rand','small'][(i//4)%3]), rng)
    d0 = rng.randrange(oP)
    run_instance(C, P, C.mul(d0, P), rng, fN)
tot = len(myic.STATS); gen = sum(1 for s in myic.STATS if s[2])
print(f"Lemma 3 literal (first 12 non-pivot Lambda rows): {gen}/{tot} (instance, prime) pairs generate K_l; non-generating:", [s for s in myic.STATS if not s[2]])
sm = [s for s in myic.STATS if s[0]==2]
print(f"  of which l=2: {sum(1 for s in sm if s[2])}/{len(sm)}")
