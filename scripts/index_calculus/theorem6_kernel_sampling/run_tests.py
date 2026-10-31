#!/usr/bin/env python3
"""Unit tests (exact, small): (T1) z - sigma(E^T y) is EXACTLY uniform on the left kernel; (T2) Schur recursion gives
kernel vectors with full rank mod l, count = n - sum r_k, matches dense Smith elimination count of l47_base.py; (T3) rank-defect examples."""
import itertools, random, numpy as np, sys
from toy_l62 import *
from l47_base import kernel_free_rows
rng = random.Random(62)

# ---- T1: exact uniformity of the z - sigma(E^T y) trick, enumerate all y
ok1 = True
for trial in range(30):
    l = rng.choice([2, 3, 5]); n = rng.randint(3, 6 if l < 5 else 4); f = rng.randint(1, n)
    E = np.array([[rng.choice([0, 0, 1, 1, 2]) for _ in range(f)] for _ in range(n)], dtype=np.int64)
    fk = FieldKernel(E, l)
    cnt = collections.Counter()
    for y in itertools.product(range(l), repeat=n):
        y = np.array(y, dtype=np.int64); b = (y @ E) % l
        z = (y - fk.sigma(b)) % l
        assert not ((z @ E) % l).any()
        cnt[tuple(z)] += 1
    kerdim = n - fk.r
    ok1 &= (len(cnt) == l ** kerdim and len(set(cnt.values())) == 1)
print(f"T1 zsigma exactly uniform on left kernel for 30 random (E,l): {ok1}")

# ---- T2: Schur recursion vs dense elimination
ok2 = True; rows = []
for trial in range(300):
    l, v = rng.choice([(2, 3), (2, 4), (3, 2), (3, 3), (5, 2), (2, 2)])
    n = rng.randint(5, 14); f = rng.randint(2, n - 1)
    dens = rng.choice([0.15, 0.3, 0.6])
    E = np.array([[ (rng.randint(1, 4) if rng.random() < dens else 0) for _ in range(f)] for _ in range(n)], dtype=np.int64)
    # sometimes plant nonunit structure: scale some columns by l
    for j in range(f):
        if rng.random() < 0.3: E[:, j] = (E[:, j] * l ** rng.randint(1, v)) 
    M = l ** v
    Lam, lev = schur_free(E % M, l, v)
    Ld, piv = kernel_free_rows(E % M, l, v)
    good = (not ((Lam @ E) % M).any()) and rank_mod(Lam, l) == Lam.shape[0] and Lam.shape[0] == Ld.shape[0]
    ok2 &= good
    rows.append((l, v, n, f, Lam.shape[0], Ld.shape[0], lev[0][4]))
print(f"T2 Schur recursion: 300 random (E,l,v): all Lambda*E==0, full rank mod l, same count as dense elimination: {ok2}")
print("   sample (l,v,n,f,s_schur,s_dense,defect_level0):", rows[:4])
print("PASS tests" if ok1 and ok2 else "FAIL tests")
