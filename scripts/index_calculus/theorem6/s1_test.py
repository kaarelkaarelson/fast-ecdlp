"""Direct test of Lemma S1: fixed real E (from the oracle), a structured (non-random) Lambda of rank 12 mod l,
tags resampled conditionally on the R_i (a mod l uniform on {a : sum a_j t_j = r_i}); mu = Lambda a must be
(i) always in K_l (Lemma 1) and (ii) uniform / independent on K_l (S1)."""
import random, math, itertools, sys
import numpy as np
from toy66 import *
from collections import Counter

def chi2_p(counts,cells):
    n=sum(counts.values()); e=n/cells
    chi=sum((c-e)**2/e for c in counts.values())+(cells-len(counts))*e
    # Wilson-Hilferty normal approx of p-value
    k=cells-1; z=((chi/k)**(1/3)-(1-2/(9*k)))/math.sqrt(2/(9*k))
    return chi,k,0.5*math.erfc(z/math.sqrt(2))

def trial(p,A,B,l,seed,nsamp=30000):
    rng=random.Random(seed)
    C=Curve(p,A,B); N=C.N; fac=factor(N); assert fac[l]==1
    while True:
        B1=rng.choice(C.pts[1:]);B2=rng.choice(C.pts[1:]);P=rng.choice(C.pts[1:]);Q=rng.choice(C.pts[1:])
        Xp=[B1,B2,P,Q]
        t=[C.mul(N//l,X) for X in Xp]
        if any(x is not None for x in t): break
    g=next(x for x in t if x is not None)
    tl=[dlog_small(C,g,x,l) for x in t]
    dat=collect(C,Xp,rng)
    F,E,tags,Rs=dat
    Rl=[dlog_small(C,g,C.mul(N//l,R),l) for R in Rs]
    S=Solver(E.T.copy(),l); Lam=np.array(S.null_basis()[:12],dtype=np.int64)
    assert len(rref_with_transform(Lam,l)[2])==12 and np.all(E.T.dot(Lam.T)%l==0)
    Nr=E.shape[0]
    K=[mu for mu in itertools.product(range(l),repeat=4) if sum(m*x for m,x in zip(mu,tl))%l==0]
    inK=True; c1=Counter(); c12=Counter()
    for _ in range(nsamp):
        T=np.zeros((Nr,4),dtype=np.int64)
        for i in range(Nr):
            while True:
                a=[rng.randrange(l) for _ in range(4)]
                if sum(x*y for x,y in zip(a,tl))%l==Rl[i]: break
            T[i]=a
        mu=Lam[:3].dot(T)%l
        for j in range(3):
            if sum(int(m)*x for m,x in zip(mu[j],tl))%l: inK=False
        c1[tuple(mu[0])]+=1; c12[(tuple(mu[0]),tuple(mu[1]))]+=1
    out=dict(l=l,p=p,N=N,K=len(K),inK=inK,m1=chi2_p(c1,len(K)),nsamp=nsamp)
    if len(K)**2<=800: out['joint12']=chi2_p(c12,len(K)**2)
    return out

if __name__=='__main__':
    rng=random.Random(5); found={}
    while len(found)<4:
        p=rng.randrange(300,700)
        if not is_prime(p): continue
        A=rng.randrange(1,p);B=rng.randrange(1,p)
        if (4*A**3+27*B*B)%p==0: continue
        C=Curve(p,A,B); fac=factor(C.N)
        for l in (3,5,2):
            if fac.get(l)==1 and l not in found and C.N>200: found[l]=(p,A,B)
        if len(found)>=3 and 3 in found and 5 in found: break
    ok=True
    for l,(p,A,B) in found.items():
        r=trial(p,A,B,l,seed=l,nsamp=6000 if l==5 else 20000); print(r,flush=True)
        ok&=r['inK'] and r['m1'][2]>1e-3 and r.get('joint12',(0,0,1))[2]>1e-3
    print("PASS s1_test" if ok else "FAIL s1_test")
