# A = 0 numerics: fixed curve, all dilated boxes {P: w*x(P) mod p in [1,X]}, w over squares.
# Reports Lemma F (mean (f-X)^2 / X vs 13), E_m/X^m, coverage, and (A=0) the omega-pair phenomenon.
import sys, math, numpy as np
sys.path.insert(0,'../dilates')
from dilate import logtable
def run(p,A,B,Xs,ms=(2,3)):
    n,lt=logtable(p,A,B)
    if lt is None: print(f"p={p} A={A} B={B} n={n}: not cyclic, skipped"); return
    xs=np.array([P[0] for P in lt]); ls=np.array([lt[P] for P in lt])
    squares=sorted({u*u%p for u in range(1,p)})
    om=[r for r in range(2,p) if pow(r,3,p)==1]
    print(f"p={p} A={A} B={B} n={n} cyclic  omega={om} sqrt(p/3)={math.sqrt(p/3):.1f} sqrt(p)={math.sqrt(p):.1f}")
    for X in Xs:
        # does [1,X] contain a pair t, t' with t'/t = omega^{+-1}?
        pairs=sum(1 for t in range(1,X+1) for r in om if (t*r)%p<=X and (t*r)%p>=1)
        rows={m:[] for m in ms}; fs=[]
        for w in squares:
            xp=(xs*w)%p; mask=(xp>=1)&(xp<=X)
            v=np.zeros(n); v[ls[mask]%n]=1; f=int(v.sum()); fs.append(f)
            S=np.fft.fft(v)
            for m in ms:
                E=float((np.abs(S)**(2*m)).sum()/n); Sm=np.fft.ifft(S**m).real
                rows[m].append((E,float((Sm>0.5).sum()/n)))
        fs=np.array(fs); varF=float(((fs-X)**2).mean())
        print(f"  X={X}: omega-pairs in [1,X]: {pairs}; mean f={fs.mean():.1f}; mean (f-X)^2/X={varF/X:.2f} (Lemma F: <=13)")
        for m in ms:
            r=np.array(rows[m])
            print(f"     m={m}: E_m/X^m mean={r[:,0].mean()/X**m:.2f} max={r[:,0].max()/X**m:.2f}  cover mean={r[:,1].mean():.3f} min={r[:,1].min():.3f}")
if __name__=="__main__":
    p=int(sys.argv[1]);A=int(sys.argv[2]);B=int(sys.argv[3]);Xs=[int(a) for a in sys.argv[4:]]
    run(p,A,B,Xs)
