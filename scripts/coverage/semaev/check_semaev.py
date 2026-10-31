"""Test Semaev's theorem (a) as used in Lemma N: f_n(x)=0 over F_p  <=>  exists signs/y in F_{p^2}-bar with sum=O,
including repeated x-values, for n=3,4,5,6, x in F_p. Independent brute force over E(F_{p^2})."""
import random, sys
from semaev_lib import *
random.seed(42)
tot=0; bad=0; pos=0
for p,n,N in [(11,3,3000),(13,3,3000),(11,4,3000),(13,4,3000),(17,4,2000),(11,5,600),(13,5,600),(11,6,150),(13,6,150)]:
    F=F2(p); loc=0; locpos=0
    while loc<N:
        A=random.randrange(p);B=random.randrange(p)
        if (4*A**3+27*B*B)%p==0: continue
        xs=[random.randrange(p) for _ in range(n)]
        if random.random()<0.5:       # bias toward repeated x values
            xs=[random.choice(xs[:2]) if random.random()<0.6 else x for x in xs]
        rel=relation_exists(F,(A,0),(B,0),xs)
        fz=(fval(xs,A,B,p)==0)
        loc+=1; tot+=1
        if rel: locpos+=1
        if rel!=fz: bad+=1; print("MISMATCH",p,n,A,B,xs,rel,fz)
    pos+=locpos
    print("p=%d n=%d tests=%d with_relation=%d"%(p,n,loc,locpos))
print("total",tot,"relations",pos,"mismatches",bad)
print("PASS semaev_iff" if bad==0 else "FAIL")
