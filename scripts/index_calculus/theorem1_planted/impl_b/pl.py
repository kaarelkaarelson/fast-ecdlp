#!/usr/bin/env python3
"""Planted-diagonal pipeline on abstract/curve groups with brute-force oracle."""
import random, itertools, math

# ---------- groups ----------
class AbGroup:
    """Z/n1 x Z/n2 ; element (x,y)"""
    def __init__(s,n1,n2=1): s.n1,s.n2=n1,n2; s.N=n1*n2; s.O=(0,0)
    def add(s,P,Q): return ((P[0]+Q[0])%s.n1,(P[1]+Q[1])%s.n2)
    def mul(s,k,P): return ((k*P[0])%s.n1,(k*P[1])%s.n2)
    def rand(s,rng): return (rng.randrange(s.n1),rng.randrange(s.n2))
    def order(s,P):
        return s.n1//math.gcd(s.n1,P[0]) if s.n2==1 else _lcm(s.n1//math.gcd(s.n1,P[0]), s.n2//math.gcd(s.n2,P[1]))
def _lcm(a,b): return a*b//math.gcd(a,b)

class Curve:
    def __init__(s,p,A,B):
        s.p,s.A,s.B=p,A,B; s.O=None
        sq={}
        for y in range(p): sq.setdefault(y*y%p,[]).append(y)
        s.pts=[None]+[(x,y) for x in range(p) for y in sq.get((x**3+A*x+B)%p,[])]
        s.N=len(s.pts)
    def add(s,P,Q):
        p=s.p
        if P is None: return Q
        if Q is None: return P
        x1,y1=P;x2,y2=Q
        if x1==x2:
            if (y1+y2)%p==0: return None
            lam=(3*x1*x1+s.A)*pow(2*y1,-1,p)%p
        else: lam=(y2-y1)*pow(x2-x1,-1,p)%p
        x3=(lam*lam-x1-x2)%p
        return (x3,(lam*(x1-x3)-y1)%p)
    def mul(s,k,P):
        R=None
        while k:
            if k&1: R=s.add(R,P)
            P=s.add(P,P);k>>=1
        return R
    def rand(s,rng): return rng.choice(s.pts)
    def order(s,P):
        n=s.N;o=n
        for q in _primes(n):
            while o%q==0 and s.mul(o//q,P) is None: o//=q
        return o
def _primes(n):
    r=[];d=2
    while d*d<=n:
        if n%d==0:
            r.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:r.append(n)
    return r

def lin(G,coefs,pts):
    R=G.O
    for c,P in zip(coefs,pts): R=G.add(R,G.mul(c%max(1,G.N*1000) if False else c,P))
    return R

# ---------- oracle with table ----------
def compositions(m,f):
    if f==1: yield (m,); return
    for k in range(m+1):
        for rest in compositions(m-k,f-1): yield (k,)+rest

class Oracle:
    """Dec(R): table of all multisets (count vectors) of size m over factor base F; policy chooses among them."""
    def __init__(s,G,F,m,policy='first',chi=None,l=None,hint=None):
        s.G,s.F,s.m=G,F,m; s.policy=policy; s.chi=chi; s.l=l
        mult=[[G.O] for _ in F]
        for i,Fi in enumerate(F):
            for k in range(1,m+1): mult[i].append(G.add(mult[i][-1],Fi))
        s.tab={}
        for c in compositions(m,len(F)):
            R=G.O
            for i,k in enumerate(c): R=G.add(R,mult[i][k])
            s.tab.setdefault(R,[]).append(c)
        s.state=0; s.f=len(F)
        s.cover=len(s.tab)/G.N
        s.avgdec=sum(len(v) for v in s.tab.values())/len(s.tab)
    def D(s,R):
        L=s.tab.get(R)
        if L is None: return None
        if s.policy=='first': return L[0]
        if s.policy=='adv':   # hidden chi mod l: prefer chi.c == 0 mod l
            for c in L:
                if sum(a*b for a,b in zip(s.chi,c))%s.l==0: return c
            return L[0]
        if s.policy=='hunter': # stateful: guesses current planted row index i=state, maximises c_i
            i=s.state%s.f; s.state+=1
            return max(L,key=lambda c:c[i])
        raise ValueError

# ---------- modular linear algebra ----------
def vp(x,l,v):
    x%=l**v
    if x==0: return v
    k=0
    while x%l==0: x//=l;k+=1
    return k
def inv_mat_modl(B,l):
    n=len(B);A=[[B[i][j]%l for j in range(n)]+[1 if i==j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        piv=next((r for r in range(c,n) if A[r][c]%l),None)
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]
        iv=pow(A[c][c],-1,l); A[c]=[x*iv%l for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]:
                t=A[r][c];A[r]=[(x-t*y)%l for x,y in zip(A[r],A[c])]
    return [row[n:] for row in A]
def matmul(A,B,mod):
    return [[sum(a*b for a,b in zip(r,col))%mod for col in zip(*B)] for r in A]
def inv_mat_lv(B,l,v):
    """Hensel/Newton lift of B^{-1} mod l to mod l^v; None if singular mod l."""
    X=inv_mat_modl(B,l)
    if X is None: return None
    n=len(B);mod=l;
    while mod<l**v:
        mod=min(mod*mod,l**v)
        BX=matmul(B,X,mod)
        T=[[(2*(i==j)-BX[i][j])%mod for j in range(n)] for i in range(n)]
        X=matmul(X,T,mod)
    return X

def smith_val_counts(E,l,v):
    """valuations of elementary divisors of E over Z/l^v (min valuation pivoting). returns list of valuations of pivots."""
    mod=l**v; A=[[x%mod for x in r] for r in E]; nr=len(A); nc=len(A[0]) if A else 0
    ar=list(range(nr)); ac=list(range(nc)); vals=[]
    while ar and ac:
        best=None
        for i in ar:
            for j in ac:
                k=vp(A[i][j],l,v)
                if k<v and (best is None or k<best[0]): best=(k,i,j)
                if best and best[0]==0: break
            if best and best[0]==0: break
        if best is None: break
        k,pi,pj=best; vals.append(k)
        w=(A[pi][pj]//l**k)%mod
        wi=pow(w,-1,mod)
        for i in ar:
            if i==pi: continue
            if A[i][pj]%mod:
                q=((A[i][pj]//l**k)*wi)%mod
                A[i]=[(x-q*y)%mod for x,y in zip(A[i],A[pi])]
        # column ops: clear pivot row similarly
        for j in ac:
            if j==pj: continue
            if A[pi][j]%mod:
                q=((A[pi][j]//l**k)*wi)%mod
                for i in ar: A[i][j]=(A[i][j]-q*A[i][pj])%mod
        ar.remove(pi); ac.remove(pj)
    return vals

def howell_d(mus,l,v,tol=None):
    """find d' with (0,0,d',-1) in span of mus (4-vectors mod l^v); None if absent"""
    mod=l**v; gens=[list(m) for m in mus]
    for c in (0,1):
        gens=[g for g in gens if any(x%mod for x in g)]
        cand=[(vp(g[c],l,v),idx) for idx,g in enumerate(gens) if g[c]%mod]
        if not cand: continue
        k,idx=min(cand); piv=gens.pop(idx)
        w=(piv[c]//l**k)%mod; wi=pow(w,-1,mod)
        new=[]
        for g in gens:
            if g[c]%mod:
                q=((g[c]//l**k)*wi)%mod
                g=[(x-q*y)%mod for x,y in zip(g,piv)]
            new.append(g)
        new.append([(x*l**(v-k))%mod for x in piv])
        gens=new
    for g in gens:
        if g[3]%l:  # unit
            iv=pow(g[3],-1,mod)
            # also need g[0],g[1] ==0 (guaranteed by elimination)
            return (-g[2]*iv)%mod
    return None
