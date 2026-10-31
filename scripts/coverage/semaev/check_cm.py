"""c_m(K)=1/(8*16^m*K*c_E), c_E=(2m-1)!!*2^m+4^m*D_{2m}, D_4=4, D_{2m}=(2m-1)2^{2m-3} (m>=3).
Exact big-integer computation of log2(1/c_m(K=1)); compare with m*log2(m); check the rigorous upper bound
  log2(1/c_m(1)) <= m*log2(m) + 6m + log2(m) + 6   (to be verified here), and Theorem-3 side conditions."""
import math
from math import log2, lgamma, log
def dfact(m):  # (2m-1)!!
    r=1
    for i in range(1,2*m,2): r*=i
    return r
def D(m): return 4 if m==2 else (2*m-1)*2**(2*m-3)
def log2_inv_c(m):
    cE=dfact(m)*2**m+4**m*D(m)
    return 3+4*m+math.log2(cE) if cE<2**1000 else 3+4*m+ (cE.bit_length()-1)+math.log2(cE/2**(cE.bit_length()-1))
def log2_inv_c_big(m):
    if m==2: return log2_inv_c(2)
    return _big(m)
def _big(m):   # via logs for large m: (2m-1)!! = (2m)!/(2^m m!)
    l1=(lgamma(2*m+1)-m*log(2)-lgamma(m+1))/log(2)+m           # log2 T_m
    l2=2*m+log2(2*m-1)+2*m-3                                   # log2(4^m D)
    return 3+4*m+max(l1,l2)+log2(1+2**(-abs(l1-l2)))
print("m  log2(1/c_m(1))  m*log2(m)  ratio  bound_m*log2(m)+6m+log2(m)+6  ok")
allok=True
for m in [2,3,4,5,6,8,10,12,16,32,64,128,256,512,1024,4096,10**5,10**6]:
    v=log2_inv_c_big(m)
    if m<=200: assert abs(v-log2_inv_c(m))<1e-6,(m,v,log2_inv_c(m))
    b=m*log2(m)+6*m+log2(m)+6
    ok=v<=b; allok&=ok
    print("%8d  %14.2f %14.2f  %.3f  %14.2f  %s"%(m,v,m*log2(m),v/(m*log2(m)),b,ok))
print("m=2: 1/c=%d (K=1)  m=3: 1/c=%d"%(8*16**2*76, 8*16**3*2680))
# side conditions: X>=12m  and p^{1/m}>=2.  With L=log2 p, X=floor(2^{L/m}); sufficient: L >= m*log2(12m+1)
print("\nSide conditions: sufficient L >= m*log2(12m+1)  (gives p^{1/m}>=12m+1, hence X>=12m, f>=X/2>=6m w.p. >=1-4/X)")
for L in [64,128,256,2**20,2**40]:
    mx=max(m for m in range(2,10**6) if m*log2(12*m+1)<=L) if L<10**7 else None
    print("L=%d  largest admissible m = %s"%(L,mx))
# relative size of the c_m loss against the leading L/m term and against Cor.2's log2(m!)
print("\nlog2(1/c_m(1)) vs log2(m!) :")
for m in [4,8,16,64,256,1024]:
    print(m, "%.1f"%log2_inv_c_big(m), "%.1f"%(lgamma(m+1)/log(2)))
print("PASS cm_bound" if allok else "FAIL")
