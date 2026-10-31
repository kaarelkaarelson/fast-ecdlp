import ECDLPArtifact

/-! Axiom check for the main theorem and every theorem named in the paper's Lean table.
Expected output for each line: `[propext, Classical.choice, Quot.sound]`. -/

-- Main theorem: the statement of `Challenge.lean`, proved in `Solution.lean` for every m.
example : ∀ m : ℕ, type_of% (ECDLP.subexponentialRate m) := ECDLP.L104R.subexponentialRate_all
#print axioms ECDLP.subexponentialRate
#print axioms ECDLP.L104R.subexponentialRate_all

-- Cases m = 0 and m = 1; pipeline for m ≥ 2
#print axioms ECDLP.L77.subexponentialRate_zero_enc
#print axioms ECDLP.L102.subexponentialRate_one
#print axioms ECDLP.L93.edgeCount_real_eq_Zc
#print axioms ECDLP.L92.count_le
#print axioms ECDLP.L92.zc_lt_len
#print axioms ECDLP.L96.frameIn_fr
#print axioms ECDLP.L104.engFullHF_val
#print axioms ECDLP.L104.engFullHF_cost

-- Group law ↔ integer constraint system; count equality (L30)
#print axioms ECDLP.L30.stepC_iff
#print axioms ECDLP.L30.chain_iff
#print axioms ECDLP.L30.chain_unique
#print axioms ECDLP.L30.mul_modEq_iff
#print axioms ECDLP.L30.zero_iff_window
#print axioms ECDLP.L30.card_int_eq_card_generic

-- Search from counts (L31)
#print axioms ECDLP.L31.search_spec
#print axioms ECDLP.L31.search_abstract

-- Gadgets and contraction (L34, L35_Forced, L56_PForced, L38)
#print axioms ECDLP.L34.Par.accept_iff
#print axioms ECDLP.L34.NPar.good_iff
#print axioms ECDLP.L35.Forced.forced_value
#print axioms ECDLP.L56.PForced.pforced_value
#print axioms ECDLP.L38.gadget_value
#print axioms ECDLP.L38.system_value

-- Network value = decomposition count; search returns lexLeast (L44, L56)
#print axioms ECDLP.L44.okC_iff
#print axioms ECDLP.L56.edge_value
#print axioms ECDLP.L56.main_count_edge
#print axioms ECDLP.L56.net_eq_ncard_edge
#print axioms ECDLP.L56.search_computes_lexLeast_exists_edge

-- Engine size and cluster conditions (L57, L94)
#print axioms ECDLP.L57.exists_cluster
#print axioms ECDLP.L57.ecdlp_engine_conditions
#print axioms ECDLP.L94.wt_htot

-- Coverage chain, average over curves (L40, L46; hypothesis SemaevNondeg)
#print axioms ECDLP.L40.sq_card_le_sums_mul_energy
#print axioms ECDLP.L46.las_vegas_success
#print axioms ECDLP.L46.coverage_oracle

-- Coverage chain, Theorems 1 and 3 (L49; hypotheses DilationNondeg, FactorBaseVar)
#print axioms ECDLP.L49.dilEquiv
#print axioms ECDLP.L49.dlp_transfer
#print axioms ECDLP.L49.corollary4_coverage

-- Statement audit examples (L105): lexLeast 2 decided in the kernel for p = 13
#print axioms two_iff
#print axioms E1
#print axioms E2
#print axioms E4
