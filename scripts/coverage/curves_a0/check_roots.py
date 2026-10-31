# Lemma "squares": exactly which (A,B,r) make l(x)l(rx) a constant times a square (over Fbar_p)?
# Prediction (derived): iff l(rx)=r^3 l(x) iff  A(r-r^3)=0 and B(1-r^3)=0, i.e. r=1, or (r=-1,B=0), or (r^3=1,A=0).
import itertools,sys
from polylib import *
bad=0;tot=0;exc={}
for p in [7,11,13,19,31,37,43]:
    for A in range(p):
        for B in range(p):
            if (4*A**3+27*B*B)%p==0: continue
            l=trim([B%p,A%p,0,1])
            for r in range(1,p):
                lr=trim([B%p,A*r%p,0,r**3%p])
                sq=is_const_times_square(pmul(l,lr,p),p)
                pred=(A*(r-r**3)%p==0 and B*(1-r**3)%p==0)
                tot+=1
                if sq!=pred: bad+=1
                if sq and r!=1:
                    kind=("A=0,r^3=1" if A==0 and pow(r,3,p)==1 else "B=0,r=-1" if B==0 and r==p-1 else "OTHER")
                    exc[kind]=exc.get(kind,0)+1
print("cases",tot,"mismatches",bad,"nontrivial exceptions by kind",exc)
print("PASS roots_criterion" if bad==0 and "OTHER" not in exc else "FAIL")
