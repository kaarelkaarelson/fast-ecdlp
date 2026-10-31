#!/usr/bin/env python3
"""Crossover lower bounds of the paper's Limitations section (Section "The results are galactic").

The proved guarantee beats Pollard's rho only if, for some m >= 5,
    e_l * c1 * m < 1/2 - 1/m,
with e_l >= rho^l / 2 (Engine Theorem (a)) and l the largest index whose cluster size K_l fits the
network's cluster condition. With log2 K_l = (3 x0 + 6) 2^l - 6 l - 2 x0 - 6 (Engine Theorem (a)),
the smallest admissible l gives a lower bound on log2 L (L = ceil(log2 p)), valid for every C_0.
For each m >= 5 take the least l meeting the first inequality, convert it to a bound on log2 L, and
minimise over m. Cluster conditions:
    'L^(1/32)' : K_l <= L^(1/32)                 (network of Section "size"; g = 3 K^8 <= 3 L^(1/4))
    'edge'     : K_l <= (L/81)^(1/32)            (edge network of Theorem 2)
    'v7'       : 3 K_l^8 <= sqrt(L) / log2 L     (network V7 of the appendix)
"""
import math

def log2K(l, x0=18):
    return (3 * x0 + 6) * 2 ** l - 6 * l - 2 * x0 - 6

def log2L_needed(lk, cond):
    if cond == 'L^(1/32)':
        return 32 * lk
    if cond == 'edge':
        return 32 * lk + math.log2(81)
    if cond == 'v7':  # solve x/2 - log2 x >= 8 lk + log2 3 for x = log2 L
        t = 8 * lk + math.log2(3)
        x = 2 * t
        for _ in range(100):
            x = 2 * (t + math.log2(x))
        return x
    raise ValueError(cond)

def crossover(c1, rho, cond, x0=18, mmax=200):
    best = None
    for m in range(5, mmax + 1):
        l = 0
        while rho ** l / 2 * c1 * m >= 0.5 - 1 / m:
            l += 1
        x = log2L_needed(log2K(l, x0), cond)
        if best is None or x < best[0]:
            best = (x, m, l)
    return best

CASES = [  # (label, c1, rho, cluster condition, value stated in the paper, its significant digits)
    ("proved c1 = 1410, rho = 1/sqrt2", 1410, 2 ** -0.5, 'L^(1/32)', 5.15e11, 3),
    ("asymptotic c1 = 744, rho = 1/sqrt2", 744, 2 ** -0.5, 'L^(1/32)', 1.29e11, 3),
    ("measured c1 = 182, rho = 1/sqrt2", 182, 2 ** -0.5, 'L^(1/32)', 8.05e9, 3),
    ("V7 c1 = 125, rho = 1/sqrt2 (Hypothesis H)", 125, 2 ** -0.5, 'v7', 2.01e9, 3),
    ("edge network c1 = 549504, rho = 1/sqrt2", 549504, 2 ** -0.5, 'edge', 6.8e16, 2),
    ("main-text pieces rho = 11/12, c1 = 1410", 1410, 11 / 12, 'L^(1/32)', 6.2e35, 2),
    ("c1 = 1, rho = 1/sqrt2", 1, 2 ** -0.5, 'L^(1/32)', 2.4e5, 2),
]

ok = True
for label, c1, rho, cond, paper, sig in CASES:
    x, m, l = crossover(c1, rho, cond)
    match = float(f"{x:.{sig}g}") == paper  # agrees to the digits the paper states
    ok &= match
    print(f"{label:45s} log2 L >= {x:.3e}  (m = {m}, l = {l})  paper {paper:.3g}  {'match' if match else 'MISMATCH'}")
print("PASS crossover" if ok else "FAIL crossover")
