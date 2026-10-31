import ECDLP.L69_Shape
import ECDLP.L69_Bdd
import ECDLP.L64_Edge

/-!
# L72 / Clus: the cluster-map expression with `g` in a variable, its value, bounds, and the cluster parts of
`CoarsenBddHyp` (item 1)

`clusM gx gE btE`: `min (g-1) (g * acc(a) / tot)` with `acc`, `tot` the cumulative / total node weights (the expression
`btE` evaluates the weight of the node in variable `20` to `wt`).  It is L64's `clusE` with the literal `g' - 1`
replaced by `gx - 1`, so that the literal-free copy (`gx = var 6`) exists.
* `eval_clusM`: value `= ECDLP.L57.clus wt g' _`.
* `bdd_clusM`: value bounds.
* `clus_wt_sum_le`: the weight of one cluster is `<= W/g + wmax`.
* `coarsenBdd_of_cluster`: `CoarsenBddHyp` (all of its fields) from the bounds of the inner expressions and weight data.
-/
noncomputable section
namespace ECDLP.L72
open Finset Factoring.Aux Ex SB ECDLP.L57 ECDLP.L56 ECDLP.L64 ECDLP.L58

def accM (btE : Ex) : Ex := nsum 24 (.var 16) (.lett 20 (.var 24) btE)
def totM (gE btE : Ex) : Ex := nsum 24 gE (.lett 20 (.var 24) btE)
def clusM (gx gE btE : Ex) : Ex :=
  .ifLt (.sub gx (.lit 1)) (.div (.mul gx (accM btE)) (totM gE btE)) (.sub gx (.lit 1))
    (.div (.mul gx (accM btE)) (totM gE btE))

section eval
variable {g B : ℕ} {σ₀ σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {gE btE : Ex} {wt : Fin g → ℕ}

/-- hypotheses: the expressions at a context `σ₀` -/
structure ClusHyp (B g : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (gE btE : Ex) (wt : Fin g → ℕ) : Prop where
  hB : B ≤ 20
  hgE : ∀ σ, Ag B σ₀ σ → Ex.eval σ A gE = g
  hbt : ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ 20 = k → Ex.eval σ A btE = wt k

variable (H : ClusHyp B g σ₀ A gE btE wt) (hσ : Ag B σ₀ σ)
include H hσ

theorem eval_slotM (j : ℕ) (hj : j < g) (σ' : ℕ → ℕ) (hσ' : Ag B σ₀ σ') (hs : σ' 24 = j) :
    Ex.eval σ' A (.lett 20 (.var 24) btE) = wf wt j := by
  simp only [Ex.eval]
  rw [H.hbt _ (hσ'.upd (by have := H.hB; omega) _) ⟨j, hj⟩ (by simp [hs])]
  simp [wf, hj]

theorem eval_accM {a : Fin g} (ha : σ 16 = a) : Ex.eval σ A (accM btE) = ∑ j ∈ range a.val, wf wt j := by
  simp only [accM, eval_nsum, Ex.eval, ha]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  exact eval_slotM H hσ j (lt_trans hj' a.2) _ (hσ.upd (by have := H.hB; omega) _) (by simp)

theorem eval_totM : Ex.eval σ A (totM gE btE) = ∑ i, wt i := by
  simp only [totM, eval_nsum, H.hgE σ hσ]
  have h1 : ∑ x ∈ range g, Ex.eval (Function.update σ 24 x) A (.lett 20 (.var 24) btE) = ∑ x ∈ range g, wf wt x :=
    sum_congr rfl fun j hj => eval_slotM H hσ j (mem_range.1 hj) _ (hσ.upd (by have := H.hB; omega) _) (by simp)
  rw [h1, ← Fin.sum_univ_eq_sum_range (wf wt) g]
  exact sum_congr rfl fun i _ => by simp [wf]

theorem eval_clusM {gx : Ex} {g' : ℕ} (hgx : Ex.eval σ A gx = g') (hg' : 0 < g') {a : Fin g} (ha : σ 16 = a) :
    Ex.eval σ A (clusM gx gE btE) = (clus wt g' hg' a).val := by
  simp only [clusM, Ex.eval, hgx, eval_accM H hσ ha, eval_totM H hσ]
  simp only [clus]
  split_ifs with h <;> omega

end eval

theorem sum_wf_range {g : ℕ} (wt : Fin g → ℕ) : ∑ j ∈ range g, wf wt j = ∑ i, wt i := by
  rw [← Fin.sum_univ_eq_sum_range (wf wt) g]; exact sum_congr rfl fun i _ => by simp [wf]

section bdd
variable {g B V : ℕ} {σ₀ σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {gE btE : Ex} {wt : Fin g → ℕ}
variable (H : ClusHyp B g σ₀ A gE btE wt) (hσ : Ag B σ₀ σ)
include H hσ

theorem acc_le_tot {a : Fin g} (ha : σ 16 = a) : Ex.eval σ A (accM btE) ≤ ∑ i, wt i := by
  rw [eval_accM H hσ ha, ← sum_wf_range]
  exact sum_le_sum_of_subset (range_mono a.2.le)

/-- the bounds of the cluster map -/
theorem bdd_clusM {gx : Ex} {g' : ℕ} (hgx : Ex.eval σ A gx = g') (hBgx : Bdd V σ A gx) (hV1 : 1 ≤ V)
    (hgV : g ≤ V) (hbb : ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ 20 = k → Bdd V σ A btE)
    (hgb : Bdd V σ A gE) (hW : ∑ i, wt i ≤ V) (hgW : g' * ∑ i, wt i ≤ V) {a : Fin g} (ha : σ 16 = a) :
    Bdd V σ A (clusM gx gE btE) := by
  have hB := H.hB
  have hslot : ∀ σ'', Ag B σ₀ σ'' → ∀ j < g, σ'' 24 = j → Bdd V σ'' A (.lett 20 (.var 24) btE) := by
    intro σ'' hσ'' j hj hs
    refine ⟨B_var (by rw [hs]; omega), ?_⟩
    show Bdd V (Function.update σ'' 20 (σ'' 24)) A btE
    exact hbb _ ((hσ''.upd (by omega) _)) ⟨j, hj⟩ (by simpa using hs)
  have hacc : Bdd V σ A (accM btE) := by
    refine B_nsum (B_var (by rw [ha]; exact le_trans a.2.le hgV)) (fun j hj => ?_) ?_
    · have hj' : j < g := lt_trans (by simpa [Ex.eval, ha] using hj) a.2
      exact hslot _ (hσ.upd (by omega) _) j hj' (by simp)
    · have : ∑ i ∈ range (Ex.eval σ A (.var 16)), Ex.eval (Function.update σ 24 i) A (.lett 20 (.var 24) btE) =
          ∑ j ∈ range a.val, wf wt j := by
        have := eval_accM H hσ ha
        simp only [accM, eval_nsum] at this; exact this
      rw [this]
      exact le_trans (sum_le_sum_of_subset (range_mono a.2.le)) (by rw [sum_wf_range]; exact hW)
  have htot : Bdd V σ A (totM gE btE) := by
    refine B_nsum hgb (fun j hj => ?_) ?_
    · have hj' : j < g := by simpa [H.hgE σ hσ] using hj
      exact hslot _ (hσ.upd (by omega) _) j hj' (by simp)
    · have := eval_totM H hσ
      simp only [totM, eval_nsum] at this; rw [this]; exact hW
  have hdiv : Bdd V σ A (.div (.mul gx (accM btE)) (totM gE btE)) := by
    refine B_div (B_mul hBgx hacc ?_) htot
    rw [hgx]
    exact le_trans (Nat.mul_le_mul_left _ (acc_le_tot H hσ ha)) hgW
  exact B_ifLt' (B_sub hBgx (B_lit hV1)) hdiv (fun _ => B_sub hBgx (B_lit hV1)) (fun _ => hdiv)

end bdd

/-! ### The weight of one cluster -/

section wsum
variable {g : ℕ}

/-- **The weight of one cluster** is at most `W / g' + wmax` (the proof of L64's `clus_fits`, exposed). -/
theorem clus_wt_sum_le (wt : Fin g → ℕ) (wmax : ℕ) (hmax : ∀ a, wt a ≤ wmax) (g' : ℕ) (hg : 0 < g')
    (γ : Fin g') : ∑ a : Fin g, (if clus wt g' hg a = γ then wt a else 0) ≤ (∑ a, wt a) / g' + wmax := by
  set W := ∑ a, wt a with hWdef
  have hWn : W = ∑ i ∈ range g, wf wt i := by
    rw [hWdef, ← Fin.sum_univ_eq_sum_range (wf wt) g]
    refine sum_congr rfl fun a _ => ?_
    simp [wf]
  have hfmax : ∀ i, wf wt i ≤ wmax := by
    intro i; unfold wf; split_ifs with h
    · exact hmax _
    · exact Nat.zero_le _
  have s2 : ∑ a : Fin g, (if clus wt g' hg a = γ then wt a else 0) =
      ∑ i ∈ (range g).filter (fun i => wf wt i ≠ 0 ∧ g' * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i := by
    rw [sum_filter, ← Fin.sum_univ_eq_sum_range
      (fun i => if wf wt i ≠ 0 ∧ g' * (∑ j ∈ range i, wf wt j) / W = γ.val then wf wt i else 0) g]
    refine sum_congr rfl fun a _ => ?_
    have hwa : wf wt a.val = wt a := by simp [wf]
    rw [hwa]
    by_cases h0 : wt a = 0
    · simp [h0]
    · have hlt : (∑ j ∈ range a.val, wf wt j) < W := by
        have h1 : ∑ j ∈ range (a.val + 1), wf wt j ≤ ∑ i ∈ range g, wf wt i :=
          sum_le_sum_of_subset (range_mono (by omega))
        rw [sum_range_succ, hwa] at h1
        have := Nat.pos_of_ne_zero h0
        omega
      have hfl : g' * (∑ j ∈ range a.val, wf wt j) / W < g' := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        exact Nat.mul_lt_mul_of_pos_left hlt hg
      have hcl : (clus wt g' hg a).val = g' * (∑ j ∈ range a.val, wf wt j) / W := by
        unfold clus; simp only; rw [← hWdef]; omega
      have : (clus wt g' hg a = γ) ↔ (g' * (∑ j ∈ range a.val, wf wt j) / W = γ.val) := by
        rw [Fin.ext_iff, hcl]
      simp only [this, ne_eq, h0, not_false_eq_true, true_and]
  have s3 := cluster_sum (wf wt) g g' wmax W hg hWn hfmax γ.val
  have s4 : (∑ i ∈ (range g).filter (fun i => wf wt i ≠ 0 ∧ g' * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i)
      ≤ W / g' + wmax := by
    rw [← Nat.add_mul_div_left W wmax hg, Nat.le_div_iff_mul_le hg]
    linarith
  exact s2 ▸ s4

end wsum

end ECDLP.L72
