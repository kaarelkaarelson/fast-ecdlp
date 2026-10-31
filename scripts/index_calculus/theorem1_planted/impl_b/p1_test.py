#!/usr/bin/env python3
"""P1 empirical: law of accepted R_i and of oracle row T'_i vs M (own code)."""
import random, math, collections
from pl import *
rng=random.Random(5)
l=67; G=AbGroup(l*l); f=4; m=30
F=[G.rand(rng) for _ in range(f)]
orc=Oracle(G,F,m,policy='hunter'); orc.state=0
while True:
    B1,B2,P=G.rand(rng),G.rand(rng),G.rand(rng)
    if B1[0]%l: break
X=[B1,B2,P,G.mul(5,P)]
Dec=sorted(orc.tab)
print("cover",len(Dec)/G.N)
n=60000
res={}
for M in (0,1,17,63,1000003):
    cnt=collections.Counter(); acc=0; tot=0; diag=0
    for _ in range(n):
        a=[rng.randrange(G.N) for _ in range(4)]
        R=G.O
        for aj,Xj in zip(a,X): R=G.add(R,G.mul(aj,Xj))
        R=G.add(R,G.mul(M,F[0])); tot+=1
        orc.state=0
        c=orc.D(R)
        if c is None: continue
        acc+=1; cnt[R]+=1; diag+=c[0]
    k=len(Dec); exp=acc/k
    chi2=sum((cnt[R]-exp)**2/exp for R in Dec)
    z=(chi2-(k-1))/math.sqrt(2*(k-1))
    print(f"M={M}: accept rate {acc/tot:.4f}  chi2 vs uniform-on-Dec z={z:+.2f}  mean c_1 (hunter oracle, i=0) {diag/acc:.3f}")
