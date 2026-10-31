# Reproducing the checks

Claim → exact command → expected output → time. Lean commands run in `lean/`; script commands run in the folder named (`scripts/<folder>`). Times are wall-clock on a 16-core Mac (October 31, 2026); "recorded" marks the time of the original run. Python 3 with `numpy`.

## Lean

| Claim | Command | Expected output | Time |
|---|---|---|---|
| Setup | `lake exe cache get` | `Decompressed 9031 file(s)` (or `Already decompressed`) | about 1 min |
| Everything: Challenge, Solution, 409 ECDLP modules, 133 vendored modules, Verify | `lake build` | `Build completed successfully`; the only `sorry` warning is in `Challenge.lean` | see `VERIFICATION.md` |
| Theorem 2(ii), no hypotheses | `lake env lean Solution.lean` | `'ECDLP.subexponentialRate' depends on axioms: [propext, Classical.choice, Quot.sound]` | about 1 min after the build |
| Main theorem and every theorem of the paper's Lean table | `lake env lean Verify.lean` | 42 lines, each `... depends on axioms: [propext, Classical.choice, Quot.sound]` | about 1 min after the build |
| Solution proves exactly the Challenge's statement | [Comparator](https://github.com/leanprover/comparator) with `comparator.json` | no mismatch; permitted axioms only | not run for this release |

## Scripts

| Claim | Folder | Command | Expected output (last line) | Time |
|---|---|---|---|---|
| Lean statement matches brute force (E1, E2, E4) | `lean_audit` | `python3 brute.py` | 16 lines `m p a b R (string, count)`, as in `brute_out.txt` | under 1 s |
| Hand-optimised network: value = count, 168 instances | `network` | `python3 check_network.py` | `PASS` | 40 s |
| Same, 172 instances, final parameters | `size_bounds` | `python3 run_exact_clean.py` | `EXACT-PART PASS` | 30 s |
| Closed forms and size bounds (U ≤ 1410 mL, cluster bound) | `size_bounds` | `python3 verify_bounds.py` | `PASS` | 839 s recorded |
| Extension to all tuples (words A, D, C, S) | `full_semaev` | `python3 check_patterns.py` | `PASS` then `done` | 118 s |
| Theorem S over F_{p^2} (15,500 cases) | `coverage/semaev` | `python3 check_semaev.py` | `PASS semaev_iff` | 1 s |
| Constant c_m(κ) | `coverage/semaev` | `python3 check_cm.py` | `PASS cm_bound` | under 1 s |
| Lemma W | `coverage/energy` | `python3 check_weight.py` | `PASS semaev_weight` | under 1 s |
| Lemma N′ (root count) | `coverage/dilates` | `python3 lemma_check.py 1013 1 5 12` | `PASS lemma_degree` | under 1 s |
| Energy and coverage over the models E_u | `coverage/dilates` | `python3 dilate.py 30013 5 7 2,173 3,31 3,90` | table as in `dilate_out.txt` | minutes |
| Lemma "squares" (161,084 cases) | `coverage/curves_a0` | `python3 check_roots.py` | `PASS roots_criterion` | 3 s |
| Lemma F (ratio ≤ 13) | `coverage/curves_a0` | `python3 lemmaF_check.py` | `PASS lemmaF_numeric` | 6 s |
| A = 0 needs X < p/3 (243 values of s at p = 1033) | `coverage/curves_a0` | `python3 a0_lemmaN.py 1033 3 32` | `PASS a0_lemmaN` | under 1 s |
| A = 0: invariance under x → ωx | `coverage/curves_a0` | `python3 a0_orbit.py` | `PASS a0_orbit` | under 1 s |
| Theorems 4–5: toy index calculus, every group structure | `index_calculus/every_order_toy` | `python3 toy_ic.py 1000 3000 4747` | `PASS toy_ic` (28/28) | 1 s |
| Theorem 5: 48/48 | `index_calculus/theorem5` | `python3 run30.py 20261031 12` | `PASS` | 3 s |
| Theorem 5: non-cyclic, stress (with the above, 70/70) | `index_calculus/theorem5` | `python3 run_hard.py`; `python3 stress.py` | `SUMMARY hard noncyclic n2>=3: 12/12`; `stress(1): ok=10 none=0 WRONG=0` | 1 s each |
| Theorem 5: generation, uniformity, linear algebra | `index_calculus/theorem5` | `python3 lemma3.py 31 120`; `python3 uniformity.py 3 40000`; `python3 test_linalg.py` | `of which l=2: 76/76`; `UNIFORMITY_EXPERIMENT consistent with Lemma 2`; `linalg unit tests: 517 cases, failures 0 PASS` | 6 s; 1 s; 1 s |
| Theorem 6: kernel samples (Lemmas S1, S2), toy recovery 72/72 | `index_calculus/theorem6` | `python3 s1_test.py`; `python3 s2_test.py`; `python3 toy66.py 66 12 uniform` | `PASS s1_test`; `PASS s2_test ...`; `PASS toy66` | 5 s; 1 s; 2 s |
| Theorem 6: kernel sampling with Schur recursion, 144/144 | `index_calculus/theorem6_kernel_sampling` | `python3 run_toy.py 1000 5000 4747 20`; `python3 run_tests.py` | `PASS toy_l62`; `PASS tests` | 7 s; under 1 s |
| Theorem 1: planted diagonal on six curves, 231/240, 0 wrong | `index_calculus/theorem1_planted/impl_a` | `python3 toy_l97.py 97 40` | `PASS toy_l97` | 4 s |
| Theorem 1: adversarial oracle | `index_calculus/theorem1_planted/impl_a` | `python3 run_adv.py 80` | `PASS run_adv` | 4 s |
| Theorem 1: sparse solve of B = T′ − νI | `index_calculus/theorem1_planted/impl_a` | `python3 wied_dixon.py` | `PASS wied_dixon` | 1 s |
| Theorem 1, independent implementation (one configuration; the output files list all) | `index_calculus/theorem1_planted/impl_b` | `python3 run_pipe.py cyc 67 200 1 first 4 30` | `RESULT ... howell_fail=0 wrong=0 ...` | under 1 s |
| Theorem 1: Lemma S1 with planted rows | `index_calculus/theorem1_planted/impl_b` | `SEED=11 python3 s1_shift_test.py 150000` | `seed=11 joint (mu_1,mu_2) ... z=+2.11` (as recorded) | 12 s |
| Theorem 1: Lemma P1; Wiedemann–Dixon mod ℓ^3 | `index_calculus/theorem1_planted/impl_b` | `python3 p1_test.py`; `python3 wied.py` | `M=1000003: accept rate 0.8831 ...`; `PASS wied` | 1 s; 4 s |
| Crossover lower bounds | `crossover` | `python3 crossover.py` | `PASS crossover` | under 1 s |

Every command above was re-run for this release on a copy of `scripts/` and ended with the expected output, except `verify_bounds.py` and `dilate.py` (long; not re-run).
