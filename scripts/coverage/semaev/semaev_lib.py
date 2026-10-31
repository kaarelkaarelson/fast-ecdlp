"""Own implementation: F_{p^2}, E(F_{p^2}) group law, sign-relation test, and Semaev f_n evaluation mod p via
Sylvester resultants with FORMAL degrees + Lagrange interpolation."""
import random, itertools

def find_nr(p):
    for r in range(2,p):
        if pow(r,(p-1)//2,p)==p-1: return r
class F2:
    def __init__(s,p):
        s.p=p; s.r=find_nr(p)
        s.sq={}
        for a in range(p):
            for b in range(p):
                z=s.mul((a,b),(a,b)); s.sq.setdefault(z,[]).append((a,b))
    def mul(s,x,y):
        p=s.p; return ((x[0]*y[0]+s.r*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    def add(s,x,y): return ((x[0]+y[0])%s.p,(x[1]+y[1])%s.p)
    def sub(s,x,y): return ((x[0]-y[0])%s.p,(x[1]-y[1])%s.p)
    def neg(s,x): return ((-x[0])%s.p,(-x[1])%s.p)
    def inv(s,x):
        p=s.p; n=(x[0]*x[0]-s.r*x[1]*x[1])%p; ni=pow(n,p-2,p)
        return ((x[0]*ni)%p,(-x[1]*ni)%p)
    def sqrt(s,z):
        l=s.sq.get(z); return l[0] if l else None
def ec_add(F,A,P,Q):
    if P is None: return Q
    if Q is None: return P
    if P[0]==Q[0]:
        if F.add(P[1],Q[1])==(0,0): return None
        num=F.add(F.mul((3,0),F.mul(P[0],P[0])),A); den=F.mul((2,0),P[1])
    else:
        num=F.sub(Q[1],P[1]); den=F.sub(Q[0],P[0])
    l=F.mul(num,F.inv(den))
    x3=F.sub(F.sub(F.mul(l,l),P[0]),Q[0])
    return (x3,F.sub(F.mul(l,F.sub(P[0],x3)),P[1]))
def relation_exists(F,A,B,xs):
    """exists signs with sum (x_j,+-Y_j)=O, Y_j in F_{p^2}?  (own brute force; independent of Semaev)"""
    pts=[]
    for x in xs:
        x2=(x%F.p,0)
        l=F.add(F.add(F.mul(x2,F.mul(x2,x2)),F.mul(A,x2)),B)
        Y=F.sqrt(l)
        if Y is None: return None   # cannot happen in F_{p^2} for x in F_p (every element of F_p is a square in F_p^2) 
        pts.append((x2,Y))
    n=len(pts)
    for signs in itertools.product([1,-1],repeat=n-1):
        S=pts[0]
        for sg,P in zip(signs,pts[1:]):
            S=ec_add(F,A,S,P if sg==1 else (P[0],F.neg(P[1])))
            if S is None and False: pass
        if S is None: return True
    return False

# ---- Semaev polynomials mod p (A,B in F_p)
def det_mod(M,p):
    n=len(M); M=[r[:] for r in M]; d=1
    for c in range(n):
        piv=None
        for r in range(c,n):
            if M[r][c]%p: piv=r;break
        if piv is None: return 0
        if piv!=c: M[c],M[piv]=M[piv],M[c]; d=-d
        d=d*M[c][c]%p; iv=pow(M[c][c],p-2,p)
        for r in range(c+1,n):
            f=M[r][c]*iv%p
            if f:
                for k in range(c,n): M[r][k]=(M[r][k]-f*M[c][k])%p
    return d%p
def resultant(F,G,dF,dG,p):
    """formal-degree Sylvester resultant; F,G coefficient lists low->high of length dF+1,dG+1"""
    n=dF+dG
    if n==0: return 1
    M=[]
    for i in range(dG):
        row=[0]*n
        for j in range(dF+1): row[i+j]=F[dF-j]
        M.append(row)
    for i in range(dF):
        row=[0]*n
        for j in range(dG+1): row[i+j]=G[dG-j]
        M.append(row)
    return det_mod(M,p)
def f3_coeffs(x1,x2,A,B,p):
    """f3(x1,x2,X) as poly in X: (x1-x2)^2 X^2 -2((x1+x2)(x1x2+A)+2B) X + ((x1x2-A)^2-4B(x1+x2))"""
    return [((x1*x2-A)**2-4*B*(x1+x2))%p, (-2*((x1+x2)*(x1*x2+A)+2*B))%p, (x1-x2)**2%p]
def interp(xs,ys,p):
    n=len(xs); coef=[0]*n
    for i in range(n):
        num=[1]; den=1
        for j in range(n):
            if j==i: continue
            num=[( (num[k-1] if k>0 else 0) - xs[j]*(num[k] if k<len(num) else 0))%p for k in range(len(num)+1)]
            den=den*(xs[i]-xs[j])%p
        c=ys[i]*pow(den,p-2,p)%p
        for k in range(n): coef[k]=(coef[k]+c*num[k])%p
    return coef
def fpoly(args,A,B,p):
    """f_n(args[0..n-2], X) as coefficient list in X, formal degree 2^{n-2} (n=len(args)+1)"""
    n=len(args)+1
    if n==2: return [(args[0])%p,(-1)%p]    # x1 - X  -> but f2=X1-X2 ; poly in X: args0 - X
    if n==3: return f3_coeffs(args[0],args[1],A,B,p)
    d=2**(n-2)
    xs=list(range(d+1)); ys=[fval(list(args)+[x0],A,B,p) for x in xs for x0 in [x]]
    return interp(xs,ys,p)
def fval(args,A,B,p):
    """f_n(args) = Res_X(f_{n-1}(args[:n-2],X), f_3(args[n-2],args[n-1],X))  (Semaev (2), k=1)"""
    n=len(args)
    if n==2: return (args[0]-args[1])%p
    if n==3: return sum(c*pow(args[2],i,p) for i,c in enumerate(f3_coeffs(args[0],args[1],A,B,p)))%p
    Fp=fpoly(args[:n-2],A,B,p)       # f_{n-1}(args[:n-2], X), formal degree 2^{n-3}
    G=f3_coeffs(args[n-2],args[n-1],A,B,p)
    return resultant(Fp,G,2**(n-3),2,p)
