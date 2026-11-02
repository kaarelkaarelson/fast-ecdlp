import ECDLPv2.L109_CountChallenge
import ECDLPv2.L132_Final
import ECDLPv2.L114_Main
import ECDLPv2.L114_Rel
import ECDLPv2.L114_Crt
import ECDLPv2.L114_Plant
import ECDLPv2.L116_Alg
import ECDLPv2.L116_Chernoff
import ECDLPv2.L116_Main
import ECDLPv2.L118_Tot
import ECDLPv2.L119_Gen
import ECDLPv2.L119_WAlg
import ECDLPv2.L119_WMain
import ECDLPv2.L149_Sched
import ECDLPv2.L173_E0Quarter

/-! Axiom check for the theorems added in version 2 of the paper.
Expected output for each line: `[propext, Classical.choice, Quot.sound]`. -/

-- Counting form of Theorem 2: the statement of `ECDLP/L109_CountChallenge.lean`, proved for every m.
example : ∀ m : ℕ, type_of% (ECDLP109.countingRate m) := ECDLP.L132.countingRate_all
#print axioms ECDLP.L132.countingRate_all

-- Index-calculus reduction behind Theorem 1 (L114)
#print axioms ECDLP.L114.relation_lattice
#print axioms ECDLP.L114.recover_from_span
#print axioms ECDLP.L114.crt_correct
#print axioms ECDLP.L114.planted_kernel
#print axioms ECDLP.L114.block_isUnit
#print axioms ECDLP.L114.runFinal_sound
#print axioms ECDLP.L114.runFinal_complete

-- Relation rows for an adaptive oracle; Chernoff cap (L116, and L119 for k generators)
#print axioms ECDLP.L116.algSpec_row_rel
#print axioms ECDLP.L116.cap_bound
#print axioms ECDLP.L119.algSpec_row_rel
#print axioms ECDLP.L119.round_failure_leW

-- Lemma gen: random elements generate any finite abelian group (L119); two-point form (L116, L118)
#print axioms ECDLP.L119.gen_log_explicit
#print axioms ECDLP.L116.gen_two_explicit
#print axioms ECDLP.L118.totient_ge

-- Crossover arithmetic of the engine schedules (Section "Where the guarantee starts to win"): G1 (e0 = 1/2) and the
-- faster base case (e0 = 1/4 + 1/(2 K0)). Arithmetic only; see the module headers for what is assumed.
#print axioms L149.G1_arith_paper
#print axioms L149.E0Q_arith_free
#print axioms L149.E0Q_arith_paper
