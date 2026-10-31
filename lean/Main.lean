import ECDLPArtifact

/-!
# Main results, with readable names

Start here. Each name below is an alias for a theorem proved in `ECDLP/`; the module names there
(`L30_…`, `L104_…`) are the ones cited in the paper. `Verify.lean` prints the axioms of all of them.

The statement to audit is `Challenge.lean`; `Solution.lean` proves it.
-/

namespace FastECDLP

/-! ## The main Lean theorem (Theorem 2(ii) of the paper)

For every `m`, one Turing machine finds the lexicographically least decomposition
`R = P₁ + ⋯ + P_m` with `x(Pᵢ) < ⌈p^{1/m}⌉` within `C_k · 2^{L/k}` steps for every `k`. -/
alias decomposition_search := ECDLP.L104R.subexponentialRate_all

/-! ## Ingredients -/

/-- The constraint system of one chord step is the group law. -/
alias group_law_step_iff := ECDLP.L30.stepC_iff
/-- The chained constraint system is the sum of the points. -/
alias group_law_chain_iff := ECDLP.L30.chain_iff
/-- Integer solutions of the constraint system are exactly the generic decompositions. -/
alias constraint_count_eq_decomposition_count := ECDLP.L30.card_int_eq_card_generic

/-- Prefix search over counts returns an element of the set. -/
alias search_from_counts := ECDLP.L31.search_spec

/-- A multiplication gadget accepts exactly when the integer identity holds. -/
alias gadget_accept_iff := ECDLP.L34.Par.accept_iff
/-- The value of a gadget as a network. -/
alias gadget_value := ECDLP.L38.gadget_value

/-- The value of the edge network is the number of decompositions with the given prefix. -/
alias network_value_eq_count := ECDLP.L56.net_eq_ncard_edge
/-- The same for the instances the algorithm actually builds. -/
alias network_count_eq_decomposition_count := ECDLP.L93.edgeCount_real_eq_Zc
/-- The network satisfies the counting engine's size and cluster conditions. -/
alias network_meets_engine_conditions := ECDLP.L57.ecdlp_engine_conditions

/-! ## Coverage (with the deep inputs as named hypotheses) -/

/-- Rank-free Las Vegas step of index calculus. -/
alias las_vegas_success := ECDLP.L46.las_vegas_success
/-- Transfer of the discrete logarithm to an isomorphic model. -/
alias dlog_transfer_to_isomorphic_model := ECDLP.L49.dlp_transfer

end FastECDLP
