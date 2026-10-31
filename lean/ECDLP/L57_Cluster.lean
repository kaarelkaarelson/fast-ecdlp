import FactoringAux.Cluster
import Mathlib.Algebra.BigOperators.Fin

/-!
# L57 / Cluster: the generic cluster lemma (cumulative-weight assignment)

For a network `N` on `Fin n` and node weights `wt` with `rowsum a ≤ wt a ≤ wmax`, the assignment
`χ a = min (g-1) ⌊g · acc a / W⌋` (`acc a` = total weight of the earlier nodes, `W` the total weight) makes every
cluster weigh at most `W / g + wmax`.  Hence the coarsened network `Fits (W / g + wmax)` (the exact predicate
`Net.Fits` consumed by Rudich's engine, `good_exists`/`lemma1`) and its total is at most `W`.
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux

/-- Core arithmetic: the nonzero-weight items with the same `⌊g · acc / W⌋` weigh `≤ (W + g wmax) / g`. -/
theorem cluster_sum (f : ℕ → ℕ) (n g wmax W : ℕ) (hg : 0 < g) (hW : W = ∑ i ∈ range n, f i)
    (hf : ∀ i, f i ≤ wmax) (c : ℕ) :
    g * ∑ i ∈ (range n).filter (fun i => f i ≠ 0 ∧ g * (∑ j ∈ range i, f j) / W = c), f i ≤ W + g * wmax := by
  set C := (range n).filter (fun i => f i ≠ 0 ∧ g * (∑ j ∈ range i, f j) / W = c) with hC
  by_cases hne : C.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  set lo := C.min' hne with hlo
  set hi := C.max' hne with hhi
  have hloC : lo ∈ C := C.min'_mem hne
  have hhiC : hi ∈ C := C.max'_mem hne
  have hlohi : lo ≤ hi := C.min'_le _ hhiC
  simp only [hC, mem_filter, mem_range] at hloC hhiC
  have hWpos : 0 < W := by
    have : f hi ≤ W := by
      rw [hW]; exact single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_range.2 hhiC.1)
    have := Nat.pos_of_ne_zero hhiC.2.1
    omega
  have hsub : C ⊆ Ico lo (hi + 1) := by
    intro i hi'
    rw [mem_Ico]
    exact ⟨C.min'_le _ hi', Nat.lt_succ_of_le (C.le_max' _ hi')⟩
  have h1 : ∑ i ∈ C, f i ≤ ∑ i ∈ Ico lo (hi + 1), f i :=
    sum_le_sum_of_subset hsub
  have h2 := Finset.sum_range_add_sum_Ico f (show lo ≤ hi + 1 by omega)
  rw [Finset.sum_range_succ] at h2
  have h3 : c * W ≤ g * ∑ j ∈ range lo, f j := by
    have := Nat.div_mul_le_self (g * ∑ j ∈ range lo, f j) W
    rw [hloC.2.2] at this; exact this
  have h4 : g * ∑ j ∈ range hi, f j < (c + 1) * W := by
    exact (Nat.div_lt_iff_lt_mul hWpos).1 (by rw [hhiC.2.2]; omega)
  have h5 : g * f hi ≤ g * wmax := Nat.mul_le_mul_left _ (hf hi)
  have h6 : g * (∑ i ∈ C, f i) + g * ∑ j ∈ range lo, f j ≤
      g * ∑ j ∈ range hi, f j + g * f hi := by
    rw [← mul_add, ← mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have h7 : (c + 1) * W = c * W + W := by ring
  omega

variable {R : Type*} [CommRing R] {n : ℕ}

/-- node weights as a function on `ℕ` -/
def wf (wt : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then wt ⟨i, h⟩ else 0

/-- the cumulative-weight cluster of a node -/
def clus (wt : Fin n → ℕ) (g : ℕ) (hg : 0 < g) (a : Fin n) : Fin g :=
  ⟨min (g - 1) (g * (∑ j ∈ range a.val, wf wt j) / (∑ i, wt i)), by omega⟩

/-- **Generic cluster lemma.**  If `rowsum a ≤ wt a ≤ wmax` for every node, the cumulative-weight clustering into
`g` clusters gives a coarsened network that `Fits (W / g + wmax)` and has total `≤ W`, `W = Σ wt`. -/
theorem exists_cluster (N : Net R n) (wt : Fin n → ℕ) (hrow : ∀ a, ∑ b, N.cc a b ≤ wt a) (wmax : ℕ)
    (hmax : ∀ a, wt a ≤ wmax) (g : ℕ) (hg : 0 < g) :
    ∃ χ : Fin n → Fin g, (N.coarsen χ).Fits ((∑ a, wt a) / g + wmax) ∧
      (N.coarsen χ).total ≤ ∑ a, wt a := by
  refine ⟨clus wt g hg, ?_, ?_⟩
  · intro γ
    refine (Net.coarsen_rowsum_le N (clus wt g hg) γ).trans ?_
    set W := ∑ a, wt a with hWdef
    have hWn : W = ∑ i ∈ range n, wf wt i := by
      rw [hWdef, ← Fin.sum_univ_eq_sum_range (wf wt) n]
      refine sum_congr rfl fun a _ => ?_
      simp [wf]
    have hfmax : ∀ i, wf wt i ≤ wmax := by
      intro i; unfold wf; split_ifs with h
      · exact hmax _
      · exact Nat.zero_le _
    -- step 1: replace row sums by weights
    have s1 : ∑ a, (if clus wt g hg a = γ then ∑ b, N.cc a b else 0) ≤
        ∑ a : Fin n, (if clus wt g hg a = γ then wt a else 0) :=
      sum_le_sum fun a _ => by split_ifs; exacts [hrow a, le_rfl]
    -- step 2: the nonzero-weight members have the exact floor
    have s2 : ∑ a : Fin n, (if clus wt g hg a = γ then wt a else 0) =
        ∑ i ∈ (range n).filter (fun i => wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i := by
      rw [sum_filter, ← Fin.sum_univ_eq_sum_range
        (fun i => if wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val then wf wt i else 0) n]
      refine sum_congr rfl fun a _ => ?_
      have hwa : wf wt a.val = wt a := by simp [wf]
      rw [hwa]
      by_cases h0 : wt a = 0
      · simp [h0]
      · have hlt : (∑ j ∈ range a.val, wf wt j) < W := by
          have h1 : ∑ j ∈ range (a.val + 1), wf wt j ≤ ∑ i ∈ range n, wf wt i :=
            sum_le_sum_of_subset (range_mono (by omega))
          rw [sum_range_succ, hwa] at h1
          have := Nat.pos_of_ne_zero h0
          omega
        have hfl : g * (∑ j ∈ range a.val, wf wt j) / W < g := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          exact Nat.mul_lt_mul_of_pos_left hlt hg
        have hcl : (clus wt g hg a).val = g * (∑ j ∈ range a.val, wf wt j) / W := by
          unfold clus; simp only; rw [← hWdef]; omega
        have : (clus wt g hg a = γ) ↔ (g * (∑ j ∈ range a.val, wf wt j) / W = γ.val) := by
          rw [Fin.ext_iff, hcl]
        simp only [this, ne_eq, h0, not_false_eq_true, true_and]
    have s3 := cluster_sum (wf wt) n g wmax W hg hWn hfmax γ.val
    have s4 : (∑ i ∈ (range n).filter (fun i => wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i)
        ≤ W / g + wmax := by
      rw [← Nat.add_mul_div_left W wmax hg, Nat.le_div_iff_mul_le hg]
      linarith
    exact s1.trans (s2 ▸ s4)
  · refine (Net.coarsen_total_le N _).trans ?_
    exact sum_le_sum fun a _ => hrow a

end ECDLP.L57
end

#print axioms ECDLP.L57.exists_cluster
