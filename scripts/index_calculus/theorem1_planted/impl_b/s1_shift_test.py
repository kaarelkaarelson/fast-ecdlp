#!/usr/bin/env python3
"""Lemma S1 transfer to shifted tags: G=Z/9, l=3, v=2. mu_k distribution on K_l given planted rows, conditioned on B invertible mod 3."""
import random, math, collections, itertools
from pl import *
rng=random.Random(int(__import__('os').environ.get('SEED','11')))
G=AbGroup(9); l=3; v=2; mod=9; f=3; m=3
F=[1,2,5]; F=[(x,0) for x in F]
orc=Oracle(G,F,m,policy='first'); print("cover",orc.cover)
X=[(1,0),(3,0),(2,0),(4,0)]   # Q=2P
K=[mu for mu in itertools.product(range(9),repeat=4) if (mu[0]+3*mu[1]+2*mu[2]+4*mu[3])%9==0]
idx={mu:i for i,mu in enumerate(K)}; print("|K_l|",len(K))
import sys
n=int(sys.argv[1]); 
c1=collections.Counter(); cj=collections.Counter(); got=0; tries=0; singular=0
def draw(i,M):
    while True:
        a=[rng.randrange(9) for _ in range(4)]
        R=(sum(aj*Xj[0] for aj,Xj in zip(a,X))+M*F[i][0])%9 if i is not None else sum(aj*Xj[0] for aj,Xj in zip(a,X))%9
        c=orc.D((R,0))
        if c is not None: return a,list(c)
while got<n:
    tries+=1
    M=rng.randrange(1000)
    rows=[];tags=[]
    for i in range(f):
        a,c=draw(i,M);c[i]-=M;rows.append(c);tags.append(a)
    for _ in range(12):
        a,c=draw(None,0);rows.append(c);tags.append(a)
    Xi=inv_mat_lv(rows[:f],l,v)
    if Xi is None: singular+=1;continue
    got+=1
    mus=[]
    for k in range(2):
        rk=rows[f+k]
        x=[(-sum(rk[j]*Xi[j][i] for j in range(f)))%mod for i in range(f)]
        lam=x+[0]*12; lam[f+k]=1
        mu=tuple(sum(lam[i]*tags[i][c] for i in range(f+12))%mod for c in range(4))
        assert mu in idx
        mus.append(mu)
    c1[idx[mus[0]]]+=1
    cj[(mus[0][0]%3,mus[0][1]%3,mus[1][0]%3,mus[1][1]%3)]+=1
k=len(K); e=n/k
chi=sum((c1[i]-e)**2/e for i in range(k)); z=(chi-(k-1))/math.sqrt(2*(k-1))
print(f"rounds used {n}, B singular mod 3 rejected {singular}/{tries}; marginal mu_1 over K_l ({k} cells, mean {e:.0f}): chi2={chi:.1f} df={k-1} z={z:+.2f}")
k2=81; e2=n/k2
chi2=sum((cj[key]-e2)**2/e2 for key in itertools.product(range(3),repeat=4)); z2=(chi2-(k2-1))/math.sqrt(2*(k2-1))
print(f"joint (mu_1,mu_2) mod (l) coords (81 cells): chi2={chi2:.1f} df=80 z={z2:+.2f}")
