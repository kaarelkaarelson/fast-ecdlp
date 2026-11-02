import Mathlib
import ECDLPv2.L116_Rank2

/-!
# L116 / Cor: explicit corollary `P(two uniform elements generate A) ≥ (5/16) φ(|A|)/|A|`
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L116

open Finset

/-- Weierstrass product inequality. -/
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℚ)
    (h0 : ∀ i ∈ S, 0 ≤ x i) (h1 : ∀ i ∈ S, x i ≤ 1) :
    1 - ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 - x i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hxa0 := h0 a (mem_insert_self _ _)
    have hxa1 := h1 a (mem_insert_self _ _)
    have hsum : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

/-- telescoping bound on `∑_{n=5}^{M-1} 1/(n(n-1))`. -/
theorem tele_sum (M : ℕ) : ∑ n ∈ Finset.Ico 5 (M + 5), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) = 1 / 4 - 1 / ((M : ℚ) + 4) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show M + 1 + 5 = (M + 5) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    have h4 : (M : ℚ) + 4 ≠ 0 := by positivity
    have h5 : (M : ℚ) + 5 ≠ 0 := by positivity
    rw [show ((M : ℚ) + 5 - 1) = (M : ℚ) + 4 by ring]
    field_simp
    ring

/-- the second factor of `pf`. -/
def gq (ℓ : ℕ) : ℚ := 1 - 1 / ((ℓ : ℚ) * ((ℓ : ℚ) - 1))

theorem pf_eq {ℓ : ℕ} (h : 2 ≤ ℓ) : pf ℓ = (1 - ((ℓ : ℚ))⁻¹) * gq ℓ := by
  unfold pf gq
  have : (2 : ℚ) ≤ ℓ := by exact_mod_cast h
  have h1 : (ℓ : ℚ) ≠ 0 := by positivity
  have h2 : (ℓ : ℚ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem gq_nonneg {ℓ : ℕ} (h : 2 ≤ ℓ) : 0 ≤ gq ℓ := by
  unfold gq
  have : (2 : ℚ) ≤ ℓ := by exact_mod_cast h
  have : (1 : ℚ) ≤ (ℓ : ℚ) * ((ℓ : ℚ) - 1) := by nlinarith
  have := div_le_one_of_le₀ this (by linarith)
  linarith

theorem gq_le_one {ℓ : ℕ} (h : 2 ≤ ℓ) : gq ℓ ≤ 1 := by
  unfold gq
  have : (2 : ℚ) ≤ ℓ := by exact_mod_cast h
  have : (0 : ℚ) < (ℓ : ℚ) * ((ℓ : ℚ) - 1) := by nlinarith
  have := one_div_pos.2 this
  linarith

/-- the product of `gq` over any set of primes is at least `5/16`. -/
theorem prod_gq_ge (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) : (5 : ℚ) / 16 ≤ ∏ ℓ ∈ S, gq ℓ := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not S (fun ℓ => ℓ < 5) (fun ℓ => gq ℓ)
  rw [← hsplit]
  have hsmall : (5 : ℚ) / 12 ≤ ∏ ℓ ∈ S.filter (fun ℓ => ℓ < 5), gq ℓ := by
    have hsub : S.filter (fun ℓ => ℓ < 5) ⊆ {2, 3} := by
      intro ℓ hℓ
      rw [mem_filter] at hℓ
      have hp := hS ℓ hℓ.1
      have := hℓ.2
      interval_cases ℓ <;> first | (simp; done) | (exfalso; revert hp; norm_num)
    have hprod : ∏ ℓ ∈ ({2, 3} : Finset ℕ), gq ℓ = 5 / 12 := by
      simp [gq]; norm_num
    rw [← hprod]
    have hT0 : 0 ≤ ∏ ℓ ∈ S.filter (fun ℓ => ℓ < 5), gq ℓ :=
      Finset.prod_nonneg fun ℓ hℓ => gq_nonneg (hS ℓ (mem_filter.1 hℓ).1).two_le
    have hsd := Finset.prod_sdiff (f := gq) hsub
    have hle1 : ∏ ℓ ∈ ({2, 3} : Finset ℕ) \ S.filter (fun ℓ => ℓ < 5), gq ℓ ≤ 1 := by
      refine Finset.prod_le_one₀ (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_)
      · have := (mem_sdiff.1 hℓ).1; simp at this
        exact gq_nonneg (by rcases this with rfl | rfl <;> norm_num)
      · have := (mem_sdiff.1 hℓ).1; simp at this
        exact gq_le_one (by rcases this with rfl | rfl <;> norm_num)
    rw [← hsd]
    nlinarith
  have hbig : (3 : ℚ) / 4 ≤ ∏ ℓ ∈ S.filter (fun ℓ => ¬ ℓ < 5), gq ℓ := by
    set T := S.filter (fun ℓ => ¬ ℓ < 5) with hT
    have hT5 : ∀ ℓ ∈ T, 5 ≤ ℓ := by
      intro ℓ hℓ; rw [hT, mem_filter] at hℓ; omega
    have h1 := one_sub_sum_le_prod T (fun ℓ => 1 / ((ℓ : ℚ) * ((ℓ : ℚ) - 1)))
      (fun ℓ hℓ => by
        have : (5 : ℚ) ≤ ℓ := by exact_mod_cast hT5 ℓ hℓ
        apply div_nonneg zero_le_one; nlinarith)
      (fun ℓ hℓ => by
        have : (5 : ℚ) ≤ ℓ := by exact_mod_cast hT5 ℓ hℓ
        rw [div_le_one (by nlinarith)]; nlinarith)
    have h2 : ∑ ℓ ∈ T, (1 : ℚ) / ((ℓ : ℚ) * ((ℓ : ℚ) - 1)) ≤ 1 / 4 := by
      obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ ℓ ∈ T, ℓ < M + 5 := ⟨T.sup id, fun ℓ hℓ => by
        have := Finset.le_sup (f := id) hℓ; simp at this; omega⟩
      calc ∑ ℓ ∈ T, (1 : ℚ) / ((ℓ : ℚ) * ((ℓ : ℚ) - 1))
          ≤ ∑ n ∈ Finset.Ico 5 (M + 5), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro ℓ hℓ; rw [mem_Ico]; exact ⟨hT5 ℓ hℓ, hM ℓ hℓ⟩
            · intro n hn _
              rw [mem_Ico] at hn
              have : (5 : ℚ) ≤ n := by exact_mod_cast hn.1
              apply div_nonneg zero_le_one; nlinarith
        _ ≤ 1 / 4 := by
            rw [tele_sum]
            have : (0 : ℚ) ≤ 1 / ((M : ℚ) + 4) := by positivity
            linarith
    unfold gq
    linarith
  calc (5 : ℚ) / 16 = 5 / 12 * (3 / 4) := by norm_num
    _ ≤ _ := mul_le_mul hsmall hbig (by norm_num) (Finset.prod_nonneg fun ℓ hℓ => gq_nonneg (hS ℓ (mem_filter.1 hℓ).1).two_le)

end ECDLP.L116
