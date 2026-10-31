# A=0: dilations w and omega*w give isomorphic (curve,box) pairs via the automorphism [zeta]; energies/coverage must coincide exactly.
import sys, numpy as np
sys.path.insert(0,'../dilates')
from dilate import logtable
p,B,X=2011,7,30
n,lt=logtable(p,0,B); xs=np.array([P[0] for P in lt]); ls=np.array([lt[P] for P in lt])
w0=[r for r in range(2,p) if pow(r,3,p)==1][0]
def stat(w):
    xp=(xs*w)%p; m=(xp>=1)&(xp<=X); v=np.zeros(n); v[ls[m]%n]=1
    S=np.fft.fft(v); return round(float((np.abs(S)**4).sum()/n),6), int(v.sum()), round(float((np.fft.ifft(S**3).real>0.5).mean()),6)
bad=0;tested=0
for w in sorted({u*u%p for u in range(1,p)}):
    tested+=1
    if stat(w)!=stat(w*w0%p): bad+=1
print(f"p={p} squares tested={tested}, (E_2,f,cov_3) differ between w and omega*w in {bad} cases")
print("PASS a0_orbit" if bad==0 else "FAIL a0_orbit")
