# Claims and evidence

Each claim of the paper (Theorems 1–6 and their lemmas) with its status and where the evidence is. Paths are relative to the repository root. Commands are in `docs/REPRODUCE.md`.

Status labels:

- **LEAN**: a Lean 4 theorem in `lean/`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` (`lean/Verify.lean`). Named hypotheses, if any, are listed.
- **PROVED-paper + reviewed**: proof written in the paper and read by an independent adversarial reviewer (an AI agent, not a human referee).
- **CHECKED**: a script in `scripts/` recomputes the claim on small instances and can fail. Evidence, not proof.
- **CITED**: taken from a published or preprint source.

## Inputs taken as given

| Claim | Status | Evidence |
|---|---|---|
| (E): the Engine Lemma and Engine Theorem of the Anthropic 3-SAT preprint | CITED. Used only by Theorem 2(i) and the y-digit search; not by Theorems 1 and 3–6 or the Lean theorem | paper, Section "The engine" |
| The counting engine's correctness and running time (Rudich and Rousseau) | LEAN (imported, vendored subset) | `lean/vendor/rudich-factoring/` |
| Semaev's theorem (Theorem S) | CITED (Semaev 2004); CHECKED over F_{p^2}, 15,500 cases | `scripts/coverage/semaev/check_semaev.py` |

## Theorem 2: decompositions in time p^{o(1)}

| Claim | Status | Evidence |
|---|---|---|
| Theorem 2(ii), search over the x-string with sign bits: one machine per m, time C_k 2^{L/k} for every k, every m, engine included | LEAN, **no hypotheses** (`ECDLP.subexponentialRate`, `ECDLP.L104R.subexponentialRate_all`); statement audited, kernel-decided examples for p = 13 | `lean/Challenge.lean`, `lean/Solution.lean`, `lean/ECDLP/L104_Final.lean`, `lean/ECDLP/L105_Examples.lean`; `scripts/lean_audit/` |
| Theorem 2(i), counting with any prefix of the full string | PROVED-paper + reviewed, conditional on (E) | paper, Section "Theorem 2" |
| Deterministic y-digit search (Lemma "prefixes of the full string"); cost τ (Lemma "cost") | PROVED-paper, one review, revised after it | paper, Section "Network" |
| Group law ⇔ integer constraint system; count equality | LEAN (`stepC_iff`, `chain_iff`, `chain_unique`, `mul_modEq_iff`, `zero_iff_window`, `card_int_eq_card_generic`) | `lean/ECDLP/L30_*.lean` |
| Search from counts | LEAN (`search_spec`, `search_abstract`) | `lean/ECDLP/L31_Search.lean` |
| Gadget acceptance ⇔ integer identity | LEAN (`Par.accept_iff`, `NPar.good_iff`) | `lean/ECDLP/L34_*.lean` |
| Forced networks; gadget as network | LEAN (`forced_value`, `pforced_value`, `gadget_value`, `system_value`) | `lean/ECDLP/L35_Forced.lean`, `L56_PForced.lean`, `L38_*.lean` |
| Edge network value = decomposition count; search returns lexLeast (Proposition "edge") | LEAN (`edge_value`, `main_count_edge`, `net_eq_ncard_edge`, `search_computes_lexLeast_exists_edge`, `edgeCount_real_eq_Zc`) | `lean/ECDLP/L56_EdgeCount.lean`, `L56_EFinal.lean`, `L93_Count.lean` |
| Engine size and cluster conditions for the edge network (U ≤ 183168 mL′, gP ≤ 185244 mL′) | LEAN (`exists_cluster`, `ecdlp_engine_conditions`, `wt_htot`) | `lean/ECDLP/L57_*.lean`, `L94_Final.lean` |
| Engine value and cost on this network; frame invariant | LEAN (`engFullHF_val`, `engFullHF_cost`, `frameIn_fr`) | `lean/ECDLP/L104_Engine.lean`, `L96_F.lean` |
| Hand-optimised network: value = count | CHECKED (168 + 172 instances against brute force, gadgets exhaustive for p = 7, 13) | `scripts/network/`, `scripts/size_bounds/run_exact_clean.py` |
| Hand-optimised network: size bounds U ≤ 1410 mL, gP ≤ 2464 mL | PROVED-paper + reviewed; CHECKED (closed forms exact, bounds hold) | `scripts/size_bounds/verify_bounds.py` |
| Extension to all tuples (doublings, cancellations, R = O; words in {A, D, C, S}) | Word classification PROVED-paper; counts CHECKED (312 instances); size bound argued | `scripts/full_semaev/` |

## Theorem 3: coverage over the models of one curve

| Claim | Status | Evidence |
|---|---|---|
| Theorem 3 (fraction c_m(κ) of points decompose on a random model E_u) | PROVED-paper + reviewed; skeleton in LEAN with hypotheses `DilationNondeg` (Lemma N′) and `FactorBaseVar` (Lemma F) | `lean/ECDLP/L49_*.lean` (`dilEquiv`, `dlp_transfer`, `corollary4_coverage`) |
| Lemma W (weights) | PROVED-paper + reviewed; CHECKED | `scripts/coverage/energy/check_weight.py` |
| Lemma "squares" | PROVED-paper + reviewed; CHECKED (161,084 cases) | `scripts/coverage/curves_a0/check_roots.py` |
| Lemma N′ (root count) and the energy proposition | PROVED-paper + reviewed; CHECKED | `scripts/coverage/dilates/` |
| Lemma F | PROVED-paper + reviewed; CHECKED (ratio ≤ 13) | `scripts/coverage/curves_a0/lemmaF_check.py` |
| A = 0 needs X < p/3 (full orbit: 243 values of s at p = 1033, B = 3) | PROVED-paper + reviewed; CHECKED | `scripts/coverage/curves_a0/a0_*.py` |
| Constant c_m(κ) | CHECKED | `scripts/coverage/semaev/check_cm.py` |
| Average-over-curves variant (Remark after Theorem 4) | Skeleton LEAN with hypothesis `SemaevNondeg` (`sq_card_le_sums_mul_energy`, `las_vegas_success`, `coverage_oracle`) | `lean/ECDLP/L40_*.lean`, `L43_*.lean`, `L46_*.lean` |

## Theorems 1 and 4–6: ECDLP

The oracle of all four is the Lean theorem of Theorem 2(ii); none uses (E).

| Claim | Status | Evidence |
|---|---|---|
| Theorem 1: every curve, every fixed m, p^{2/m+o(1)}, by a planted diagonal | PROVED-paper + reviewed (one independent review; one error in the probability bookkeeping found and corrected); toy CHECKED by two implementations (about 9,800 planted rounds with B invertible, 0 wrong; adversarial and stateful oracles) | `scripts/index_calculus/theorem1_planted/` |
| Theorem 4: cyclic group of prime or squarefree order, p^{2/m+o(1)} | PROVED-paper + reviewed; the toy runs below include prime-order and cyclic squarefree groups | `scripts/index_calculus/every_order_toy/`, `scripts/index_calculus/theorem5/` |
| Theorem 5: every curve, p^{3/m+o(1)} | PROVED-paper + reviewed; toy CHECKED (70/70) | `scripts/index_calculus/theorem5/` |
| Theorem 6: p^{2/m+o(1)} for squarefree exponent or m ≤ 8 | PROVED-paper + reviewed; toy CHECKED by two implementations (210/210, 144/144); negative control without Pohlig–Hellman fails as expected | `scripts/index_calculus/theorem6/`, `scripts/index_calculus/theorem6_kernel_sampling/` |

## Scope

| Claim | Status | Evidence |
|---|---|---|
| Crossover with Pollard rho: log2 L ≥ 5.15·10^11 (c1 = 1410), 1.29·10^11 (744), 8.05·10^9 (182), 2.01·10^9 (V7, under Hypothesis H), 6.8·10^16 (edge network), 6.2·10^35 (main-text pieces) | PROVED-paper (lower bounds for these designs, any C_0); arithmetic CHECKED | `scripts/crossover/crossover.py` |
| Any statement about a deployed curve at its actual size | Not claimed | — |
| Appendix results (network V7, genus 2) | PROVED-paper + reviewed; scripts not included in this repository | paper, appendix |
