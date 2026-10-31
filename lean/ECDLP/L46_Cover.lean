import Mathlib
import ECDLP.L46_Avg

/-!
# L46 (1)+(2c): the average-over-curves coverage theorem with the single hypothesis `SemaevNondeg`

* `Gen_eq` : L43's `Gen` = number of `R ∈ W.Point` having an ordered generic factor-base
  decomposition (`Dec`, Mathlib's group law).
* `Gen_le` : `Gen ≤ 1 + #{R ≠ 0 | GenSet (coord R) nonempty}` with L30's `GenSet`.
* `coverage_semaev` : outside a small set of `(A,B)`, the number of affine `R` with a generic
  decomposition is `≥ (|F|^{n+1}/2)² / (Kc · M) - 1`, assuming only `SemaevNondeg`.
-/
namespace ECDLP.L46

open Finset ECDLP.L40 ECDLP.L43

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem fb_eq_fbase (A B : K) (T : Finset K) :
    fb A B T = fbase (shortW A B) (fun x => x ∈ T) := by
  classical
  ext P
  simp only [fb, fbase, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rintro rfl; exact h1 rfl
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases P with
    | zero => exact absurd rfl h1
    | some x y h => simp [xc]

/-- L43's `Gen` counts exactly the group elements with an ordered generic decomposition. -/
theorem Gen_eq (T : Finset K) (n : ℕ) (A B : K) :
    Gen T n A B = (univ.filter (fun R : (shortW A B).Point =>
      (Dec (shortW A B) (fun x => x ∈ T) n R).Nonempty)).card := by
  classical
  unfold Gen sums
  rw [fb_eq_fbase]
  congr 1
  ext R
  simp only [mem_image, mem_filter, Fintype.mem_piFinset, mem_univ, true_and, Dec, Finset.Nonempty]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    exact ⟨t, ⟨h1, h2, h3⟩⟩
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨t, ⟨h1, h2⟩, h3⟩

/-- `Gen` against L30's `GenSet` (the set counted by the network): `R = 0` is the only
element not covered by `GenSet`. -/
theorem Gen_le (T : Finset K) (n : ℕ) (A B : K) :
    Gen T n A B ≤ (univ.filter (fun R : (shortW A B).Point => R ≠ 0 ∧
      (ECDLP.L30.GenSet (shortW A B) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).Nonempty)).card
      + 1 := by
  classical
  rw [Gen_eq]
  have : univ.filter (fun R : (shortW A B).Point =>
      (Dec (shortW A B) (fun x => x ∈ T) n R).Nonempty) ⊆
      insert 0 (univ.filter (fun R : (shortW A B).Point => R ≠ 0 ∧
      (ECDLP.L30.GenSet (shortW A B) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).Nonempty)) := by
    intro R hR
    simp only [mem_filter, mem_univ, true_and] at hR
    by_cases h0 : R = 0
    · simp [h0]
    · refine mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, h0, ?_⟩)
      rw [← card_pos, ← card_dec_eq_card_genSet _ n h0]
      exact card_pos.2 hR
  exact (card_le_card this).trans (card_insert_le _ _)

/-- **Coverage theorem (average over curves), single hypothesis `SemaevNondeg`.** -/
theorem coverage_semaev (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) (T : Finset K) (hX : 0 < T.card)
    (n D : ℕ) (hXn : 12 * n ≤ T.card) (Kc : ℝ) (hKc : 0 < Kc)
    (hS : SemaevNondeg (n + 1) T D) :
    ∃ Bad : Finset (K × K),
      (Bad.card : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 * (1 / Kc + 4 / T.card) + Fintype.card K ∧
      ∀ p : K × K, p ∉ Bad →
        disc p.1 p.2 ≠ 0 ∧ (T.card : ℝ) < 2 * (fb p.1 p.2 T).card ∧
        (((fb p.1 p.2 T).card : ℝ) ^ (n + 1) / 2) ^ 2 / (Kc * Mconst K n T D) ≤
          ((univ.filter (fun R : (shortW p.1 p.2).Point => R ≠ 0 ∧
            (ECDLP.L30.GenSet (shortW p.1 p.2) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).Nonempty)).card
            + 1 : ℕ) := by
  obtain ⟨Bad, hB, hBad⟩ := theorem3 hK h3 T hX n hXn (Mconst K n T D) Kc
    (Mconst_pos n T D hX) hKc (avg_of_semaev hK T n D hS)
  refine ⟨Bad, hB, fun p hp => ?_⟩
  obtain ⟨hd, hF, -, -, hcov⟩ := hBad p hp
  refine ⟨hd, hF, hcov.trans ?_⟩
  exact_mod_cast Gen_le T n p.1 p.2

end ECDLP.L46
