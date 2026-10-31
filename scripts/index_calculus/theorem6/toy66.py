"""Independent toy: m=2 index calculus, brute-force oracle, own mod-l solver, Algorithm H
(field path for l || N, Pohlig-Hellman for l^2 | N).  Own code; nothing imported from the other implementations."""
import random, sys, math
import numpy as np

def is_prime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factor(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f

class Curve:
    def __init__(s,p,A,B):
        s.p,s.A,s.B=p,A,B
        sq={}
        for y in range(p): sq.setdefault(y*y%p,[]).append(y)
        s.pts=[None]
        for x in range(p):
            for y in sq.get((x**3+A*x+B)%p,[]): s.pts.append((x,y))
        s.N=len(s.pts)
    def add(s,P,Q):
        if P is None: return Q
        if Q is None: return P
        p=s.p
        if P[0]==Q[0]:
            if (P[1]+Q[1])%p==0: return None
            lam=(3*P[0]*P[0]+s.A)*pow(2*P[1],-1,p)%p
        else:
            lam=(Q[1]-P[1])*pow(Q[0]-P[0],-1,p)%p
        x=(lam*lam-P[0]-Q[0])%p
        return (x,(lam*(P[0]-x)-P[1])%p)
    def mul(s,k,P):
        R=None; k%=max(1,s.N*2)
        while k:
            if k&1: R=s.add(R,P)
            P=s.add(P,P); k>>=1
        return R
    def order(s,P,facN):
        o=s.N
        for l in facN:
            while o%l==0 and s.mul(o//l,P) is None: o//=l
        return o

# ---- own linear algebra mod l (numpy) ----
def rref_with_transform(A,l):
    """A: f x n int array.  returns (R,T,piv) with T A = R mod l, R in RREF, piv list of (row,col)."""
    f,n=A.shape
    M=np.concatenate([A%l,np.eye(f,dtype=np.int64)],axis=1)
    r=0; piv=[]
    for c in range(n):
        if r>=f: break
        nz=np.nonzero(M[r:,c])[0]
        if len(nz)==0: continue
        k=r+nz[0]
        if k!=r: M[[r,k]]=M[[k,r]]
        M[r]=M[r]*pow(int(M[r,c]),-1,l)%l
        col=M[:,c].copy(); col[r]=0
        M=(M-np.outer(col,M[r]))%l
        piv.append((r,c)); r+=1
    return M[:,:n],M[:,n:],piv
class Solver:
    def __init__(s,A,l):
        s.A=A%l; s.l=l; s.f,s.n=A.shape
        s.R,s.T,s.piv=rref_with_transform(A,l)
    def solve(s,b):  # any solution of A x=b (b in column space)
        tb=s.T.dot(b)%s.l
        x=np.zeros(s.n,dtype=np.int64)
        for (r,c) in s.piv: x[c]=tb[r]
        assert np.all(s.A.dot(x)%s.l==b%s.l)
        return x
    def nullvec_uniform(s,rng):
        y=np.array([rng.randrange(s.l) for _ in range(s.n)],dtype=np.int64)
        z=(y-s.solve(s.A.dot(y)%s.l))%s.l
        return z
    def null_basis(s):
        pc={c for _,c in s.piv}; free=[c for c in range(s.n) if c not in pc]
        B=[]
        for fc in free:
            v=np.zeros(s.n,dtype=np.int64); v[fc]=1
            for (r,c) in s.piv: v[c]=(-s.R[r,fc])%s.l
            B.append(v)
        return B

def howell_dlog(mus,l):
    """mus: list of vectors in F_l^4.  Find d with (0,0,d,-1) in span, or None; (d,-1) in W where W = span ∩ {c1=c2=0}."""
    rows=[list(map(int,m)) for m in mus]
    for col in (0,1):
        piv=None
        for r in rows:
            if r[col]%l: piv=r; break
        if piv is None: continue
        iv=pow(piv[col],-1,l); piv=[x*iv%l for x in piv]
        new=[]
        for r in rows:
            if r is piv or r[col]%l==0 and r is not piv:
                if r[col]%l==0: new.append(r)
                continue
            q=r[col]; new.append([(a-q*b)%l for a,b in zip(r,piv)])
        # drop piv (annihilator l^{v-k} piv is zero for v=1,k=0)
        rows=[r for r in new if any(x%l for x in r)]
    W=[(r[2],r[3]) for r in rows]
    # span of W in F_l^2; find (d,-1)
    W=[w for w in W if w!=(0,0)]
    if not W: return None
    # rank
    if len(W)>=2:
        a,b=W[0]
        for c,d_ in W[1:]:
            if (a*d_-b*c)%l: return 0      # full space: any d works
    a,b=W[0]
    if b%l==0: return None
    return (-a*pow(b,-1,l))%l

def pohlig_hellman(C,P,Q,l,a,cP):
    """P_l=cP has order l^a; return d mod l^a with Q_l=dP_l (brute force digits)."""
    Pl=C.mul(cP,P); Ql=C.mul(cP,Q)
    gamma=C.mul(l**(a-1),Pl)           # order l
    d=0
    for k in range(a):
        # Q_l - d P_l, scaled by l^(a-1-k)
        T=Ql
        if d: 
            mP=C.mul(d,Pl); T=C.add(Ql,(mP[0],(-mP[1])%C.p) if mP else None)
        T=C.mul(l**(a-1-k),T)
        dig=None; cur=None
        for t in range(l):
            if cur==T: dig=t;break
            cur=C.add(cur,gamma)
        assert dig is not None
        d+=dig*l**k
    return d

def dlog_small(C,g,T,l):
    cur=None
    for t in range(l):
        if cur==T: return t
        cur=C.add(cur,g)
    raise ValueError

def round_data(C,X,rng,Bpts):
    p=C.p; Xb=math.isqrt(p)
    u=rng.randrange(1,p)
    u2=u*u%p
    F=[P for P in C.pts[1:] if (u2*P[0])%p<Xb]
    f=len(F)
    # brute-force deterministic oracle on pair sums
    table={}
    for i in range(f):
        for j in range(f):
            if i!=j and F[i][0]!=F[j][0]:
                S=C.add(F[i],F[j])
                if S not in table: table[S]=(i,j)
    return F,table
def collect(C,Xp,rng):
    F,table=round_data(C,Xp,rng,None)
    f=len(F); Nr=f+12
    rows=[];tags=[];Rs=[];tries=0
    while len(rows)<Nr:
        tries+=1
        if tries>40*Nr: return None
        a=[rng.randrange(C.N) for _ in range(4)]
        R=None
        for aj,Xj in zip(a,Xp): R=C.add(R,C.mul(aj,Xj))
        if R is None or R not in table: continue
        i,j=table[R]
        e=np.zeros(f,dtype=np.int64); e[i]+=1; e[j]+=1
        rows.append(e); tags.append(a); Rs.append(R)
    return F,np.array(rows),tags,Rs

def lam_to_mu(lam,tags,l):
    T=np.array(tags,dtype=np.int64)
    return (lam.dot(T))%l

def run_instance(C,P,Q,facN,rng,mode='uniform',ph=True,max_rounds=60,stats=None):
    N=C.N; ordP=C.order(P,facN)
    res={}  # modulus -> residue
    fieldp=[]
    for l,v in facN.items():
        if v>=2 and ph:
            a=0; cP=N//l**v; T=C.mul(cP,P)
            while T is not None: T=C.mul(l,T); a+=1
            if a>=1: 
                M=l**a; res[M]=pohlig_hellman(C,P,Q,l,a,cP)
        else: fieldp.append(l)
    for rd in range(1,max_rounds+1):
        while True:
            B1=rng.choice(C.pts[1:]); B2=rng.choice(C.pts[1:])
            break
        Xp=[B1,B2,P,Q]
        eB=1
        for Y in Xp: eB=eB*C.order(Y,facN)//math.gcd(eB,C.order(Y,facN))
        dat=collect(C,Xp,rng)
        if dat is None: continue
        F,E,tags,Rs=dat
        ok=True; cur=dict(res)
        for l in fieldp:
            if eB%l: continue
            S=Solver(E.T.copy(),l)
            if mode=='uniform':
                vecs=[S.nullvec_uniform(rng) for _ in range(24)]
            else:
                vecs=S.null_basis()[:24]
            # greedy independent 12
            keep=[];basis=np.zeros((0,E.shape[0]),dtype=np.int64)
            for v in vecs:
                M=np.vstack([basis,v[None,:]])
                if len(rref_with_transform(M,l)[2])>len(basis):
                    basis=M; keep.append(v)
                if len(keep)==12: break
            if len(keep)<12: ok=False;break
            mus=[lam_to_mu(v,tags,l) for v in keep]
            d=howell_dlog(mus,l)
            if d is None: ok=False;break
            cur[l]=d
        if not ok: continue
        # CRT
        d=0; M=1
        for m_,r_ in cur.items():
            # combine d mod M with r_ mod m_ (moduli coprime)
            t=((r_-d)*pow(M,-1,m_))%m_; d+=M*t; M*=m_
        if C.mul(d,P)==Q:
            if stats is not None: stats['rounds']=rd
            return d%ordP if ordP else d, ordP
    return None,ordP

def exponent(C,fac):
    ex=1;best=None;bo=0
    for Y in C.pts[1:]:
        oy=C.order(Y,fac); ex=ex*oy//math.gcd(ex,oy)
        if oy>bo: bo=oy;best=Y
    return ex,best,bo

def family_instances(seed,per,plo=400,phi=1600):
    """families: sqfree N; square N cyclic with l^2 | exp-or-N ; square N non-cyclic."""
    rng=random.Random(seed); fams={'sqfree':[], 'sq_cyclic':[], 'sq_noncyc':[]}
    while any(len(v)<per for v in fams.values()):
        p=rng.randrange(plo,phi)
        if not is_prime(p): continue
        A=rng.randrange(1,p);B=rng.randrange(1,p)
        if (4*A**3+27*B*B)%p==0: continue
        C=Curve(p,A,B)
        if C.N<500: continue
        fac=factor(C.N); sqf=all(v==1 for v in fac.values())
        if sqf: k='sqfree'
        else:
            ex,_,_=exponent(C,fac); k='sq_cyclic' if ex==C.N else 'sq_noncyc'
        if len(fams[k])<per: fams[k].append((p,A,B))
    return fams

if __name__=='__main__':
    seed=int(sys.argv[1]); per=int(sys.argv[2]); mode=sys.argv[3]; ph=(sys.argv[4]=='ph') if len(sys.argv)>4 else True
    rng=random.Random(seed)
    good=tot=0; fam=family_instances(seed,per)
    for k,lst in fam.items():
        for (p,A,B) in lst:
            C=Curve(p,A,B); fac=factor(C.N)
            ex,Pmax,omax=exponent(C,fac)
            for pv in ('random','maxord'):
                P=rng.choice(C.pts[1:]) if pv=='random' else Pmax
                op=C.order(P,fac)
                d=rng.randrange(op); Q=C.mul(d,P)
                st={}
                dd,o=run_instance(C,P,Q,fac,rng,mode=mode,ph=ph,stats=st)
                ok=dd is not None and dd==d%op
                good+=ok; tot+=1
                sqpart=[l for l,v in fac.items() if v>=2]
                print(f"{k} p={p} N={C.N}={fac} exp={ex} ordP={op}({pv}) d={d} got={dd} rounds={st.get('rounds')} {'OK' if ok else 'FAIL'}",flush=True)
    print(f"RESULT mode={mode} ph={ph} {good}/{tot}")
    print("PASS toy66" if good==tot else "FAIL toy66")
