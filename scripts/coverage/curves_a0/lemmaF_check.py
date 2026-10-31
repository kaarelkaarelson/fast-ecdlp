# Lemma F: (1/(p-1)) sum_u (f^(u)-X)^2 vs 13X, f^(u)=#{P!=O on E_u: x in [1,X]} = sum_{t<=X}(1+chi(l(u^-2 t))), exact (no sampling).
import sys
def chi_table(p):
    c=[-1]*p; c[0]=0
    for y in range(1,p): c[y*y%p]=1
    return c
worst=0;rows=[]
for p in [101,211,499,1009,2003,4003,10007,20011]:
    c=chi_table(p)
    for (A,B,name) in [(2,3,'gen'),(5,1,'gen'),(0,7,'j=0'),(0,1,'j=0'),(3,0,'j=1728'),(1,0,'j=1728')]:
        if (4*A**3+27*B*B)%p==0: continue
        for X in sorted({max(2,int(p**.5)),max(2,int(p**(1/3))),max(2,int((p/3)**.5))}):
            tot=0
            for u in range(1,p):
                s=pow(u,-2,p)  # u^-2
                f=sum(1+c[((s*t)**3+A*s*t+B)%p] for t in range(1,X+1))
                tot+=(f-X)**2
            ratio=tot/(p-1)/X
            rows.append((p,A,B,name,X,ratio)); worst=max(worst,ratio)
            print(f"p={p} A={A} B={B} {name} X={X}: mean (f-X)^2/X = {ratio:.2f}")
print("max ratio",round(worst,2),"(claim <=13; A=0 claim <= 13+2/X)")
print("PASS lemmaF_numeric" if worst<=13 else "FAIL")
