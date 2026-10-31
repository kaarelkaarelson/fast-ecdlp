#!/usr/bin/env python3
"""Adversarial-oracle toy.  A VALID oracle (always returns a true decomposition) that, whenever possible, returns a tuple t
with chi(t) = sum_k chi[t_k] == 0 mod l for a fixed hidden chi in F_l^f.  Then every row of the vanilla matrix is orthogonal to chi mod l
(chi is not rational, so this is l-torsion: delta >= 1) while the planted-diagonal matrix T'-M I is singular mod l only if M is an eigenvalue of T'.
"""
import sys, random, itertools
from l47_base import Curve, factor, order, howell_solve
import toy_l97 as T

class AdvInst(T.Inst):
    def __init__(s, p, A, B, m, f_target, rng, l):
        s.C = Curve(p, A, B); s.p = p; s.m = m; s.rng = rng
        pts = s.C.points(); s.N = len(pts) + 1; s.fN = factor(s.N)
        s.fb = rng.sample(pts, f_target); s.f = f_target
        s.chi = [rng.randrange(1, l) for _ in range(f_target)]
        s.first = {}; s.orth = {}
        f = f_target
        def rec(start, depth, R, csum, tup):
            if depth == m:
                s.first.setdefault(R, tup)
                if csum % l == 0: s.orth.setdefault(R, tup)
                return
            for j in range(start, f):
                rec(j, depth + 1, s.C.add(R, s.fb[j]), csum + s.chi[j], tup + (j,))
        rec(0, 0, None, 0, ())
        s.D = {R: s.orth.get(R, s.first[R]) for R in s.first}
        s.cover = len(s.D) / s.N
        s.orth_frac = len(s.orth) / len(s.D)

def main():
    rng = random.Random(1997)
    p, A, B, l, m, ft = 5021, 880, 4274, 41, 4, int(sys.argv[1]) if len(sys.argv) > 1 else 80
    inst = AdvInst(p, A, B, m, ft, rng, l)
    N = inst.N; fN = inst.fN; v = fN[l]
    print(f"p={p} N={N}={fN} l={l} f={ft} m={m} cover={inst.cover:.3f} fraction of sums with a chi-orthogonal tuple={inst.orth_frac:.4f}", flush=True)
    pts = inst.C.points()
    for _ in range(500):
        P = rng.choice(pts); o = order(inst.C, P, N, fN)
        if o % (l ** v) == 0: break
    d = rng.randrange(1, o); Q = inst.C.mul(d, P)
    cof = N // (l ** v); Pl, Ql = inst.C.mul(cof, P), inst.C.mul(cof, Q)
    trials = 20
    defects = []
    for _ in range(trials):
        rQ, rl = T.delta_vanilla(inst, P, Q, l, rng)
        defects.append(rQ - rl)
    print("VANILLA: delta_l = rank_Q - rank_l over", trials, "rounds:", sorted(defects))
    M0 = l  # distinct residues mod l
    ok = sing = wrong = 0
    for _ in range(trials):
        res = T.run_plant(inst, l, d, P, Q, M0)
        if res[0] == "singular": sing += 1; continue
        good = res[2] is not None and inst.C.mul(res[2], Pl) == Ql
        ok += good; wrong += (not good)
    print(f"PLANTED: ok {ok}/{trials}, B singular mod l {sing}, wrong {wrong}")
    print("PASS run_adv" if wrong == 0 and ok > 0 and min(defects) >= 1 else "FAIL run_adv")
main()
