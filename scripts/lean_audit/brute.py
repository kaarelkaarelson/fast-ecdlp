# Independent brute force of the Lean `strings`/`lexLeast` spec (pure python, affine group law written by hand)
import sys, itertools
def isprime(n): return n>1 and all(n%d for d in range(2,int(n**.5)+1))
def ceilroot(p,m):
    B=0
    while B**m<p: B+=1
    return B
def add(p,a,P,Q):  # P,Q affine (x,y) or None=O
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2:
        if (y1+y2)%p==0: return None
        l=(3*x1*x1+a)*pow(2*y1,-1,p)%p
    else: l=(y2-y1)*pow(x2-x1,-1,p)%p
    x3=(l*l-x1-x2)%p; y3=(l*(x1-x3)-y1)%p
    return (x3,y3)
def lexleast(m,p,a,b,xR,yR,pre=()):
    if not isprime(p): return None
    if (4*a**3+27*b*b)%p==0: return None
    B=ceilroot(p,m); nb=B.bit_length()
    pts=[(x,y) for x in range(min(B,p)) for y in range(p) if (y*y-x**3-a*x-b)%p==0]
    best=None; cnt=0
    for tup in itertools.product(pts,repeat=m):
        S=None; ok=True
        for k,P in enumerate(tup):
            if k>0:
                if S is None or S[0]==P[0]: ok=False;break
            S=add(p,a,S,P)
        if not ok or S is None or S!=(xR%p,yR%p): continue
        s=[]
        for (x,y) in tup:
            s+= [(x>>j)&1 for j in reversed(range(nb))]+[int((p-1)//2<y)]
        s=tuple(s)
        if s[:len(pre)]!=tuple(pre): continue
        cnt+=1
        if best is None or s<best: best=s
    return best,cnt
if __name__=="__main__":
    for args in [(2,13,1,1,None),(2,31,2,3,None),(3,31,2,3,None),(3,13,1,1,None)]:
        m,p,a,b,_=args
        # try all R on the curve, print several
        B=ceilroot(p,m)
        Rs=[(x,y) for x in range(p) for y in range(p) if (y*y-x**3-a*x-b)%p==0]
        for R in Rs[:4]:
            print(m,p,a,b,R,lexleast(m,p,a,b,R[0],R[1]))
