# Check Lemma N' + degree bound: for fixed E, each nontrivial multiset t of 4 x-values in [1,X],
# the number of s in F_p^* such that x_j = s*t_j admit signs with sum of points = O is <= D'=12 (zeros of f_4(s t;A,B), s in F_p^*).
import sys, itertools, numpy as np
from dilate import curve_points, logtable
p=int(sys.argv[1]);A=int(sys.argv[2]);B=int(sys.argv[3]);X=int(sys.argv[4])
n,lt=logtable(p,A,B)
assert lt is not None
L={}  # x -> log of one point with that x (other is -log); x with y=0 -> 2-torsion log n/2 (== -itself)
for (x,y),l in lt.items(): L[x]=l
xs=np.arange(p)
has=np.zeros(p,bool); lg=np.zeros(p,np.int64)
for x,l in L.items(): has[x]=True; lg[x]=l
signs=np.array(list(itertools.product([1,-1],repeat=4)))
worst=0; worstt=None; ntriv_all=True; tested=0; cnt_hist={}
S=np.arange(1,p)
for t in itertools.combinations_with_replacement(range(1,X+1),4):
    from collections import Counter
    c=Counter(t); triv=all(v%2==0 for v in c.values())
    xv=(S[:,None]*np.array(t)[None,:])%p
    ok=has[xv].all(axis=1)
    lv=lg[xv]  # (p-1,4)
    tot=(lv@signs.T)%n   # (p-1,16)
    rel=(tot==0).any(axis=1)&ok
    k=int(rel.sum()); tested+=1
    if triv:
        if k<p-1-0: pass
        continue
    cnt_hist[k]=cnt_hist.get(k,0)+1
    if k>worst: worst=k;worstt=t
print(f"p={p} A={A} B={B} X={X} nontrivial multisets tested={sum(cnt_hist.values())}; max #s with relation = {worst} at t={worstt}; D'=12; hist={dict(sorted(cnt_hist.items()))}")
print("PASS lemma_degree" if worst<=12 else "FAIL lemma_degree")
