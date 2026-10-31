#!/usr/bin/env python3
"""Own Wiedemann (nonsingular) + Dixon lifting on B = T' - M I, T' sparse with row sum m.  Counts mat-vecs."""
import random, sys, time
def nextprime(n):
    def isp(k):
        if k<2:return False
        for q in (2,3,5,7,11,13,17,19,23,29,31,37):
            if k%q==0:return k==q
        d=k-1;s=0
        while d%2==0:d//=2;s+=1
        for a in (2,3,5,7,11,13,17,19,23,29,31,37):
            x=pow(a,d,k)
            if x in(1,k-1):continue
            for _ in range(s-1):
                x=x*x%k
                if x==k-1:break
            else:return False
        return True
    while not isp(n):n+=1
    return n
def BM(s,l):
    C=[1];Bp=[1];Ls=0;m=1;b=1
    for n in range(len(s)):
        d=s[n]
        for i in range(1,Ls+1): d=(d+C[i]*s[n-i])%l
        if d==0: m+=1;continue
        T=C[:]
        coef=d*pow(b,-1,l)%l
        C=C+[0]*(len(Bp)+m-len(C))
        for i,x in enumerate(Bp): C[i+m]=(C[i+m]-coef*x)%l
        if 2*Ls<=n: Ls=n+1-Ls;Bp=T;b=d;m=1
        else: m+=1
    return C[:Ls+1],Ls   # C(z)=1+c1 z+...  : s_n + sum c_i s_{n-i}=0
class Sparse:
    def __init__(s,rows,n): s.rows=rows;s.n=n;s.mv=0   # rows: list of list (col,val); y=A x
    def mul(s,x,mod):
        s.mv+=1
        return [sum(v*x[c] for c,v in r)%mod for r in s.rows]
def wied_solve(A,b,l,rng):
    n=A.n
    while True:
        u=[rng.randrange(l) for _ in range(n)]
        seq=[];v=b[:]
        for i in range(2*n):
            seq.append(sum(x*y for x,y in zip(u,v))%l); v=A.mul(v,l)
        C,Ls=BM(seq,l)
        # recurrence s_n + sum_{i=1}^{Ls} C_i s_{n-i} =0  => poly z^Ls + C1 z^{Ls-1}+...+C_Ls ; constant term C_Ls
        if Ls==0 or C[Ls]==0: continue
        # f(A)b=0 with f=z^Ls + C1 z^{Ls-1}+...+C_Ls ; x = -(1/C_Ls) * (A^{Ls-1} b + C1 A^{Ls-2} b + ... + C_{Ls-1} b)
        acc=[0]*n; v=b[:]
        for k in range(Ls):          # coefficient of A^k b is C_{Ls-1-k}
            c=C[Ls-1-k]
            acc=[(a+c*y)%l for a,y in zip(acc,v)]
            if k<Ls-1: v=A.mul(v,l)
        iv=pow(C[Ls],-1,l); x=[(-iv*a)%l for a in acc]
        if A.mul(x,l)==[bb%l for bb in b]: return x
def dixon(A,b,l,v,rng):
    n=A.n; mod=l**v; x=[0]*n; r=b[:]; pw=1
    for k in range(v):
        xk=wied_solve(A,[t%l for t in r],l,rng)
        x=[(a+pw*c)%mod for a,c in zip(x,xk)]
        Ax=A.mul(xk,mod*l)  # exact-enough integer residual: use Python ints without mod
        # exact: compute integer A xk
        Ax=[sum(val*xk[c] for c,val in row) for row in A.rows]; A.mv+=0
        r=[(t-a)//l for t,a in zip(r,Ax)]
        # r may be negative ints, fine
        pw*=l
    return x
if __name__=='__main__':
    rng=random.Random(7)
    for n in (100,200,400,800):
        l=nextprime(4*n*n+rng.randrange(1000)); v=3; m=6
        # T': each row m entries (random cols, counts), M random
        M=rng.randrange(max(8*n,4*n*n))
        rows=[]
        T=[[0]*n for _ in range(n)]
        for i in range(n):
            for _ in range(m): T[i][rng.randrange(n)]+=1
            T[i][i]-=M
        # Bt = B^T sparse rows
        cols=[[] for _ in range(n)]
        for i in range(n):
            for j,val in enumerate(T[i]):
                if val: cols[j].append((i,val))
        A=Sparse(cols,n)   # A=B^T
        b=[rng.randrange(l**v) for _ in range(n)]
        t=time.time(); x=dixon(A,b,l,v,rng)
        Ax=[sum(val*x[c] for c,val in row)%(l**v) for row in A.rows]
        ok=Ax==b
        print(f"f={n} l={l} v={v}: solution exact mod l^v: {ok}; matvecs={A.mv} = {A.mv/n:.2f} f ; per level {A.mv/n/v:.2f} f ; {time.time()-t:.1f}s")
        assert ok
    print("PASS wied")
