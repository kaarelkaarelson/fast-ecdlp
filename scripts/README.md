# Numerical checks

These are the scripts that back the paper's claims that are not proved in Lean. Each one recomputes a claim and can fail. Python 3 with `numpy`; nothing else. Run each command from inside its folder (`cd scripts/<folder>`). Scripts print to the terminal; the recorded output sits next to each script. None needs network access.

"Time" is the wall-clock time of a re-run on a 16-core Mac (October 31, 2026) unless marked "recorded", which is the time of the original run. Toy runs take a seed; where the recorded seed is known the command shown reproduces the recorded file, otherwise the note says so.

## Networks: value = decomposition count, size bounds

| Folder | Claim (paper) | Command | Expected last line | Recorded output | Time |
|---|---|---|---|---|---|
| `network/` | Value equals count: 168 instances against brute force, gadgets exhaustive for p = 7, 13, perturbed witnesses rejected (Section "Network", item "Value equals count") | `python3 check_network.py` | `PASS` | `check_output.txt` | 39 s recorded |
| `size_bounds/` | The same with the final parameters: 172 instances | `python3 run_exact_clean.py` | `EXACT-PART PASS` | `exact_clean_output.txt` | 142 s recorded |
| `size_bounds/` | Closed forms (U), (H) exact against the constructed topology; bounds of Propositions U and cluster, `U <= 1410 mL` for `L >= 16` (item "Size bounds") | `python3 verify_bounds.py` | `PASS` | `verify_output.txt` | 839 s recorded |
| `full_semaev/` | Extension to all tuples (words in {A, D, C, S}): 312 instances, word sums equal direct counts, `R = O` included, perturbed witnesses rejected (Section "Theorem 2", extension paragraph) | `python3 check_patterns.py` | `PASS` (then `done`) | `check_output.txt` | 118 s |

## Coverage (Theorem 3): Theorem S, Lemmas W, N′, F, squares, the case A = 0

| Folder | Claim (paper) | Command | Expected last line | Recorded output | Time |
|---|---|---|---|---|---|
| `coverage/semaev/` | Theorem S checked over F_{p^2}: 15,500 cases, no mismatch | `python3 check_semaev.py` | `PASS semaev_iff` | `check_semaev_out.txt` | 1 s |
| `coverage/semaev/` | The constant `c_m(κ) = 2^{-m log2 m - O(m)}/κ` of Theorem 3 | `python3 check_cm.py` | `PASS cm_bound` | `check_cm_out.txt` | under 1 s |
| `coverage/energy/` | Lemma W (weights and homogeneity of Semaev polynomials) | `python3 check_weight.py` | `PASS semaev_weight` | `weight_out.txt` | under 1 s |
| `coverage/dilates/` | Lemma N′ as a root count: a nontrivial relation holds for at most `D'` values of `s` | `python3 lemma_check.py 1013 1 5 12` (also `2003 7 11 12`, `1009 5 1 12`, `1009 2 3 12`) | `PASS lemma_degree` | `lemma_out.txt` | under 1 s each |
| `coverage/dilates/` | Proposition "energy over the dilations" and coverage over the models `E_u` of one curve | `python3 dilate.py 30013 5 7 2,173 3,31 3,90`; `python3 dilate.py 10009 0 5 2,100 3,22` | table (no verdict line) | `dilate_out.txt` | minutes |
| `coverage/curves_a0/` | Lemma "squares": 161,084 cases over seven primes up to 43, exceptions only at A = 0 and B = 0 | `python3 check_roots.py` | `PASS roots_criterion` | `check_roots_out.txt` | 3 s |
| `coverage/curves_a0/` | Lemma F: mean `(f - X)^2 / X <= 13` | `python3 lemmaF_check.py` | `PASS lemmaF_numeric` | `lemmaF_out.txt` | 6 s |
| `coverage/curves_a0/` | A = 0 needs `X < p/3`: at p = 1033, B = 3 a full orbit gives 243 values of s, above `D'_6 = 80` | `python3 a0_lemmaN.py 1033 3 32`; `python3 a0_lemmaN.py 4003 2 63` | `PASS a0_lemmaN` | `a0_lemmaN_out.txt` | under 1 s |
| `coverage/curves_a0/` | A = 0: energy and coverage invariant under `x -> ωx` | `python3 a0_orbit.py` | `PASS a0_orbit` | `a0_orbit_out.txt` | under 1 s |
| `coverage/curves_a0/` | A = 0: energy, coverage and Lemma F ratio on curves `y^2 = x^3 + B` | `python3 a0_test.py 2011 0 7 12 20 25 30 45 60` (one run per curve in the file's header lines) | table (no verdict line) | `a0_out.txt` | 1 s per curve |

## Index calculus (Theorems 1 and 4 to 6): toy runs with a brute-force oracle

All use `m = 2` (or `m = 4` for Theorem 1) and a brute-force decomposition oracle in place of the engine, and check that the algorithm recovers the planted logarithm `d`. They test the algebra (relation lattices, uniformity, Pohlig–Hellman, Chinese remaindering), not the asymptotic cost.

| Folder | Claim (paper) | Command | Expected last line | Recorded output | Time |
|---|---|---|---|---|---|
| `index_calculus/every_order_toy/` | First implementation: every group structure (prime, cyclic, non-cyclic) | `python3 toy_ic.py 1000 3000 4747` (28/28 on re-run) | `PASS toy_ic` | `toy_out.txt` (26/26), `toy_out_10k.txt` (22/22); arguments of these runs not recorded | 1 s |
| `index_calculus/theorem5/` | Theorem 5 (`p^{3/m}`, every curve): 48/48 recoveries | `python3 run30.py 20261031 12` | `PASS` | `out_main.txt` | 3 s |
| `index_calculus/theorem5/` | Non-cyclic groups with `n2 >= 3`; stress cases (70/70 together with the above) | `python3 run_hard.py`; `python3 stress.py` | `SUMMARY hard noncyclic n2>=3: 12/12`; `stress(1): ok=10 none=0 WRONG=0` | `out_hard.txt`, `out_stress.txt` | 1 s each |
| `index_calculus/theorem5/` | Lemma "generation": rows generate the relation lattice; Lemma "uniformity" (chi-square); linear algebra unit tests | `python3 lemma3.py 31 120`; `python3 uniformity.py 3 40000`; `python3 test_linalg.py` | `of which l=2: 76/76`; `UNIFORMITY_EXPERIMENT consistent with Lemma 2`; `517 cases, failures 0 PASS` | `out_lemma3.txt`, `out_uniformity.txt`, `out_test_linalg.txt` | 6 s, 1 s, 1 s |
| `index_calculus/theorem6/` | Theorem 6 (`p^{2/m}`, squarefree exponent or `m <= 8`): uniform kernel samples (Lemma S2), toy recovery with Pohlig–Hellman | `python3 s1_test.py`; `python3 s2_test.py`; `python3 toy66.py 66 12 uniform` (reproduces `out_uniform.txt` exactly); `python3 toy66.py SEED 12 rref` | `PASS s1_test`; `PASS s2_test ...`; `PASS toy66` | `out_s1.txt`, `out_s2.txt`, `out_uniform.txt` and `out_rref.txt` (72/72 each; seed of the rref run not recorded) | 5 s, 1 s, about 2 s |
| `index_calculus/theorem6/` | Negative control: without Pohlig–Hellman, primes with `ℓ^2 | N` fail in 13 of 48 | `python3 toy66.py SEED 8 uniform noph` | `FAIL toy66` (by design) | `out_control_noph.txt` (35/48; seed not recorded) | about 1 s |
| `index_calculus/theorem6_kernel_sampling/` | Third implementation (kernel sampling, Schur recursion for `ℓ^v`): 144/144 | `python3 run_toy.py 1000 5000 4747 20`; `python3 run_tests.py` | `PASS toy_l62`; `PASS tests` | `toy_out.txt` (144/144), `toy_out_10k.txt` (66/66), `tests_out.txt` | 7 s, under 1 s |
| `index_calculus/theorem1_planted/impl_a/` | Theorem 1 (planted diagonal, every curve, every m): six curves with `ℓ^2 | N`, 231/240 recovered, 9 singular `B` detected, 0 wrong | `python3 toy_l97.py 97 40` | `PASS toy_l97` | `toy_out.txt` | 4 s |
| `index_calculus/theorem1_planted/impl_a/` | Adversarial oracle (orthogonal to a hidden character): unplanted matrix never lifts (20/20), planted recovers `d mod ℓ^2` | `python3 run_adv.py 80`; `python3 run_adv.py 100` | `PASS run_adv` | `adv_out.txt` | 4 s each |
| `index_calculus/theorem1_planted/impl_a/` | Sparse Wiedemann–Dixon solve of `B = T' - νI` | `python3 wied_dixon.py` | `PASS wied_dixon` | `wied_dixon_out.txt` | 1 s |
| `index_calculus/theorem1_planted/impl_b/` | Independent implementation: abstract groups and curves with `#E = ℓ^2`, policies `first`, `adv`, `hunter`; about 9,400 nonsingular planted rounds, all recovered, 0 wrong | `python3 run_pipe.py KIND L ROUNDS SEED POLICY F M`, e.g. `python3 run_pipe.py cyc 67 200 1 first 4 30` (one line per configuration in the output files) | `RESULT ... wrong=0` | `pipe_out.txt`, `curve_out.txt`, `pipe_small_out.txt` | under 1 s per configuration |
| `index_calculus/theorem1_planted/impl_b/` | Lemma P1 (the oracle's answers do not depend on ν) and Lemma S1 with planted rows (chi-square) | `python3 p1_test.py`; `SEED=11 python3 s1_shift_test.py 150000` (also `SEED=12`, `SEED=13`) | `M=1000003: accept rate ...`; `joint ... z=...` | `p1_out.txt`, `s1_shift_out.txt` | 1 s; 12 s per seed |
| `index_calculus/theorem1_planted/impl_b/` | Wiedemann–Dixon modulo `ℓ^3`, `f` up to 800: `3f` products per lifting level | `python3 wied.py` | `PASS wied` | `wied_out.txt` | 4 s |

The seeds of the recorded `run_pipe.py` runs were not recorded; a re-run with another seed gives different counts with the same verdict (`wrong=0`, `howell_fail=0`).

## Other

| Folder | Claim (paper) | Command | Expected last line | Recorded output | Time |
|---|---|---|---|---|---|
| `crossover/` | Crossover lower bounds of Section "Limitations" (`log2 L >= 5.15e11` with `c1 = 1410`, `6.8e16` for the edge network, and the others) | `python3 crossover.py` | `PASS crossover` | `crossover_out.txt` | under 1 s |
| `lean_audit/` | Independent brute force of the Lean statement `lexLeast` (audit examples E1, E2, E4 of `lean/ECDLP/L105_Examples.lean`) | `python3 brute.py; python3 -c "from brute import lexleast; print('E1', lexleast(2,13,1,1,8,1)); print('E2', lexleast(2,13,1,1,8,12)); print('E4', lexleast(2,13,1,1,0,1))"` | `E4 (None, 0)` | `brute_out.txt` | under 1 s |

## Provenance

The scripts were written by the research agents. Some file names (`l47_base.py`, `toy_l62.py`, `toy_l97.py`) and some recorded outputs keep internal run labels such as `L33` or `L47`. Edits made when copying: internal labels were removed from docstrings and comments; in `coverage/curves_a0/a0_*.py` the path `'../L41'` became `'../dilates'`; folder names were changed to match the paper's theorem numbers. `crossover/crossover.py` was written for this repository from the formula in the paper's Limitations section.
