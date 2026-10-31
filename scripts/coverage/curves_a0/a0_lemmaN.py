# Count s in F_p^* with a signed relation sum +-(s t_j, .) = O, for t containing an omega-pair, on y^2=x^3+B (A=0).
# Lemma N' (repaired) predicts: nonzero polynomial g_t of degree <= D'_{2m} => #s <= D'.  Also shows the genuine exception (full omega-orbit).
import sys, itertools, random, numpy as np
sys.path.insert(0,'../dilates')
from dilate import logtable
p=int(sys.argv[1]); B=int(sys.argv[2]); X=int(sys.argv[3]); seed=int(sys.argv[4]) if len(sys.argv)>4 else 1
n,lt=logtable(p,0,B); assert lt is not None
has=np.zeros(p,bool); lg=np.zeros(p,np.int64)
for (x,y),l in lt.items(): has[x]=True; lg[x]=l
om=[r for r in range(2,p) if pow(r,3,p)==1]; w=om[0]
S=np.arange(1,p)
def nrel(t):
    k=len(t); signs=np.array(list(itertools.product([1,-1],repeat=k-1)))
    xv=(S[:,None]*np.array(t)[None,:])%p
    ok=has[xv].all(axis=1)
    lv=lg[xv]; tot=(lv[:,:1]+lv[:,1:]@signs.T)%n
    return int((((tot==0).any(axis=1))&ok).sum())
pairs=[(a,(a*r)%p) for a in range(1,X+1) for r in om if 1<=(a*r)%p<=X]
print(f"p={p} B={B} n={n} omega={om} X={X} sqrt(p/3)={(p/3)**.5:.1f} sqrt p={p**.5:.1f} omega-pairs in [1,X]: {pairs}")
random.seed(seed); ALL_OK=True
for (a,b) in pairs[:2]:
    mx4=0
    for c in range(1,X+1):
        for d in range(c,X+1):
            t=(a,b,c,d)
            if len({a,b,c,d})==4 or True:
                from collections import Counter
                if all(v%2==0 for v in Counter(t).values()): continue
                mx4=max(mx4,nrel(t))
    mx6=0
    for _ in range(600):
        t=(a,b)+tuple(random.randint(1,X) for _ in range(4))
        if all(v%2==0 for v in Counter(t).values()): continue
        mx6=max(mx6,nrel(t))
    ALL_OK = ALL_OK and mx4<=12 and mx6<=80
    print(f"  pair {(a,b)}: max #s over nontrivial 4-tuples containing the pair = {mx4} (D'_4=12); over 600 random 6-tuples = {mx6} (D'_6=80)")
# genuine exception: full omega-orbit (not inside [1,X])
a=1;t=(a,w*a%p,w*w*a%p,2,2*w%p,2*w*w%p)
print(f"  full orbit tuple {t}: #s={nrel(t)} (s with all six points existing ~ (p-1)/4 = {(p-1)//4}); D'_6=80 -> exceptional, g_t==0")
print('PASS a0_lemmaN' if (ALL_OK and nrel(t)>80) else 'FAIL a0_lemmaN')
