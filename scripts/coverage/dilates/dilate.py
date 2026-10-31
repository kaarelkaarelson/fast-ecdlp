# Fixed curve E/F_p, average over dilated boxes {P : w*x(P) mod p in [1,X]}, w = u^2 (E_u model).
# Also max nontrivial character sum over F for the s=1 box and for dilates.
import sys, numpy as np, math
def curve_points(p,A,B):
    sq={}
    for y in range(p): sq.setdefault(y*y%p,[]).append(y)
    pts=[]
    for x in range(p):
        r=(x*x*x+A*x+B)%p
        for y in sq.get(r,[]): pts.append((x,y))
    return pts
def add(P,Q,p,A):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P;x2,y2=Q
    if x1==x2:
        if (y1+y2)%p==0: return None
        l=(3*x1*x1+A)*pow(2*y1,-1,p)%p
    else: l=(y2-y1)*pow(x2-x1,-1,p)%p
    x3=(l*l-x1-x2)%p
    return (x3,(l*(x1-x3)-y1)%p)
def logtable(p,A,B):
    n=len(curve_points(p,A,B))+1
    pts=curve_points(p,A,B)
    # find generator of full group (cyclic?) 
    for g in pts:
        Q=None; seen=[]
        lt={}
        R=g;k=1;ok=True
        lt[g]=1
        while True:
            R=add(R,g,p,A); k+=1
            if R is None: break
            if k>n: break
            lt[R]=k
        if k==n: return n,lt  # order of g == n (R None at k==n)
    return n,None
def main(p,A,B,ms):
    n,lt=logtable(p,A,B)
    if lt is None: print("not cyclic",p,A,B,n); return
    xs=np.array([P[0] for P in lt]); ls=np.array([lt[P] for P in lt])
    print(f"p={p} A={A} B={B} n={n} cyclic")
    squares=sorted({u*u%p for u in range(1,p)})
    for m,X in ms:
        res=[]
        for w in squares:
            xp=(xs*w)%p
            mask=(xp>=1)&(xp<=X)
            v=np.zeros(n); v[ls[mask]%n]=1
            f=int(v.sum())
            S=np.fft.fft(v)
            E=float((np.abs(S)**(2*m)).sum()/n)
            Sm=np.fft.ifft(S**m).real
            cov=float((Sm>0.5).sum()/n)
            M=float(np.abs(S[1:]).max())
            res.append((f,E,cov,M))
        r=np.array(res)
        s1=res[squares.index(1)]
        trivial=math.prod(range(1,2*m,2))*X**m  # (2m-1)!! X^m
        print(f" m={m} X={X} #dil={len(res)}: mean f={r[:,0].mean():.1f}  mean E_m={r[:,1].mean():.1f}  (E/X^m mean={r[:,1].mean()/X**m:.2f}, max={r[:,1].max()/X**m:.2f}, X^2m/p={X**(2*m)/p:.2f})  "
              f"cov mean={r[:,2].mean():.3f} min={r[:,2].min():.3f} frac(cov>0.1)={(r[:,2]>0.1).mean():.3f}")
        print(f"    w=1 box: f={s1[0]} E={s1[1]:.1f} cov={s1[2]:.3f}; maxnontriv|S|: w=1 {s1[3]:.1f}, over dilates mean {r[:,3].mean():.1f} max {r[:,3].max():.1f}; sqrtX={X**.5:.1f} sqrt p={p**.5:.1f} 3sqrt(p)(ln p+1)={3*p**.5*(math.log(p)+1):.0f}")
if __name__=="__main__":
    p=int(sys.argv[1]);A=int(sys.argv[2]);B=int(sys.argv[3])
    ms=[]
    for a in sys.argv[4:]:
        m,X=a.split(','); ms.append((int(m),int(X)))
    main(p,A,B,ms)
