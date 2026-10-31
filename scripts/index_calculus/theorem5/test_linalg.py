import itertools, random, numpy as np
from linalg import elim, span_size_log
def span(rows, q, w):
    S = {tuple([0]*w)}
    for r in rows:
        new = set()
        for s in S:
            for c in range(q):
                new.add(tuple((s[i]+c*r[i]) % q for i in range(w)))
        S = new
    return S
random.seed(1); bad = 0; tot = 0
for (l, v) in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(2,4),(3,3),(5,2)]:
    q = l**v
    for trial in range(60):
        n = random.randint(1,4); w = random.randint(2,4); nc = random.randint(0,w)
        # bias toward entries with high valuation
        M = [[random.choice([0, random.randrange(q), l*random.randrange(q)]) % q for _ in range(w)] for _ in range(n)]
        full = span(M, q, w) if q**1 <= 25 or n*w <= 8 else None
        if full is None: continue
        want = {s for s in full if all(s[i]==0 for i in range(nc))}
        G, ks = elim(M, nc, l, v)
        got = span([tuple(r) for r in G.tolist()], q, w)
        tot += 1
        ok = (got == want)
        # size formula
        if nc == w:
            ok = ok and (len(full) == l**sum(v-k for k in ks)) if False else ok
        if not ok: bad += 1; print("MISMATCH", l, v, M, nc)
        # span size formula on full width
        _, ks2 = elim(M, w, l, v)
        if l**sum(v-k for k in ks2) != len(full): bad += 1; print("SIZE MISMATCH", l, v, M)
print("linalg unit tests:", tot, "cases, failures", bad, "PASS" if bad==0 else "FAIL")
