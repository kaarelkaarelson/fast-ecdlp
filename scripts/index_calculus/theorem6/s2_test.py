import itertools, random, numpy as np
from collections import Counter
from toy66 import Solver
rng=random.Random(3); ok=True
for trial in range(40):
    l=rng.choice([2,3,5]); f=rng.randrange(2,4); n=rng.randrange(f+1,7 if l<5 else 5)
    A=np.array([[rng.randrange(l) if rng.random()<.6 else 0 for _ in range(n)] for _ in range(f)],dtype=np.int64)
    S=Solver(A,l); cnt=Counter()
    for y in itertools.product(range(l),repeat=n):
        y=np.array(y,dtype=np.int64); z=(y-S.solve(A.dot(y)%l))%l
        assert np.all(A.dot(z)%l==0); cnt[tuple(z)]+=1
    nullsize=len([1 for z in itertools.product(range(l),repeat=n) if np.all(A.dot(np.array(z))%l==0)])
    ok&= (len(cnt)==nullsize and len(set(cnt.values()))==1)
print("PASS s2_test (z - sigma(Ay) exactly uniform on null space, 40 random A, full enumeration)" if ok else "FAIL s2_test")
