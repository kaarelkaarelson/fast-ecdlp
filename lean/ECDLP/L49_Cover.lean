import Mathlib
import ECDLP.L49_Main

/-!
# L49 (4): coverage over dilations (fixed curve, random isomorphic model)

`coverage_dilation`: for a fixed nonsingular `E: y² = x³+Ax+B` over a finite field `K`
(`char ≠ 2`), outside a set `Bad ⊆ Kˣ` of size `≤ |Kˣ|(1/Kc + 4c/X)` of dilation parameters `u`,
the number of affine `R ∈ E_u` with a generic decomposition into `n+1` factor-base points
(`x ∈ T`; L30's `GenSet`) is, plus one, at least `(f_u^{n+1}/2)² / (Kc·M)`.
Hypotheses: exactly `DilationNondeg` and `FactorBaseVar`.
-/
namespace ECDLP.L49

open Finset ECDLP.L40 ECDLP.L43 ECDLP.L46

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem card_low_le (A B : K) (T : Finset K) (hX : 0 < T.card) (c : ℝ)
    (hF : FactorBaseVar A B T c) :
    (((univ : Finset Kˣ).filter (fun u : Kˣ => 2 * ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ)
        ≤ (T.card : ℝ))).card : ℝ) ≤ 4 * c * (Fintype.card Kˣ : ℝ) / (T.card : ℝ) := by
  set X : ℝ := (T.card : ℝ) with hXdef
  have hX' : 0 < X := by rw [hXdef]; exact_mod_cast hX
  set S := (univ : Finset Kˣ).filter (fun u : Kˣ => 2 * ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) ≤ X)
  have h1 : (S.card : ℝ) * (X ^ 2 / 4) ≤ ∑ u : Kˣ,
      (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X) ^ 2 := by
    calc (S.card : ℝ) * (X ^ 2 / 4) = ∑ _u ∈ S, X ^ 2 / 4 := by simp
      _ ≤ ∑ u ∈ S, (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X) ^ 2 := by
          refine sum_le_sum (fun u hu => ?_)
          have := (mem_filter.1 hu).2
          nlinarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have h2 := h1.trans hF
  rw [le_div_iff₀ hX']
  have : (S.card : ℝ) * X ^ 2 ≤ 4 * (c * X * Fintype.card Kˣ) := by linarith
  have h3 : ((S.card : ℝ) * X - 4 * c * Fintype.card Kˣ) * X ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **Coverage over dilations (fixed curve, random isomorphic model).** -/
theorem coverage_dilation (hK : ringChar K ≠ 2) (A B : K) (hd : disc A B ≠ 0) (T : Finset K)
    (hX : 0 < T.card) (n D' : ℕ) (hXn : 12 * n ≤ T.card) (Kc c : ℝ) (hKc : 0 < Kc)
    (hN : DilationNondeg A B (n + 1) T D') (hF : FactorBaseVar A B T c) :
    ∃ Bad : Finset Kˣ,
      (Bad.card : ℝ) ≤ (Fintype.card Kˣ : ℝ) * (1 / Kc + 4 * c / T.card) ∧
      ∀ u : Kˣ, u ∉ Bad →
        (T.card : ℝ) < 2 * (fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card ∧
        (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) ^ (n + 1) / 2) ^ 2
            / (Kc * Mdil K n T D') ≤ Gen T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ∧
        Gen T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ≤
          ((univ.filter (fun R : (shortW ((u : K) ^ 4 * A) ((u : K) ^ 6 * B)).Point => R ≠ 0 ∧
            (ECDLP.L30.GenSet (shortW ((u : K) ^ 4 * A) ((u : K) ^ 6 * B)) (fun x => x ∈ T)
              (ECDLP.L30.coord _ R) n).Nonempty)).card + 1 : ℕ) := by
  classical
  set q : ℝ := (Fintype.card Kˣ : ℝ) with hq
  set Md := Mdil K n T D' with hMd
  have hM : 0 < Md := Mdil_pos n T D' hX
  let E' : Kˣ → ℝ := fun u => (Eng T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) : ℝ)
  let low := (univ : Finset Kˣ).filter (fun u : Kˣ =>
    2 * ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) ≤ T.card)
  let high := (univ : Finset Kˣ).filter (fun u : Kˣ => Kc * Md < E' u)
  refine ⟨low ∪ high, ?_, ?_⟩
  · have hl : (low.card : ℝ) ≤ 4 * c * q / T.card := card_low_le A B T hX c hF
    have hh : (high.card : ℝ) ≤ q / Kc := by
      have := markov_count E' (fun u => by positivity) Md Kc hM hKc
        (by simpa [E', hMd] using avg_energy_dil hK A B hd T n D' hN)
      simpa [high, hq] using this
    calc ((low ∪ high).card : ℝ) ≤ low.card + high.card := by
          exact_mod_cast card_union_le _ _
      _ ≤ 4 * c * q / T.card + q / Kc := by linarith
      _ = q * (1 / Kc + 4 * c / T.card) := by ring
  · intro u hu
    simp only [mem_union, not_or, low, high, mem_filter, mem_univ, true_and, not_lt, not_le] at hu
    obtain ⟨hlow, hhigh⟩ := hu
    set A' := (u : K) ^ 4 * A
    set B' := (u : K) ^ 6 * B
    have hF' : (T.card : ℝ) < 2 * (fb A' B' T).card := hlow
    have hE : (Eng T n A' B' : ℝ) ≤ Kc * Md := hhigh
    refine ⟨hF', ?_⟩
    have hfx : 6 * n < (fb A' B' T).card := by
      have : T.card < 2 * (fb A' B' T).card := by exact_mod_cast hF'
      omega
    have hgc := generic_coverage (n := n) (fb A' B' T) (xc (shortW A' B'))
      (fun a => card_fibre_le_two _ _ a)
    have hgc' : (((fb A' B' T).card ^ (n + 1) - 3 * n * (fb A' B' T).card ^ n : ℕ) : ℝ) ^ 2
        ≤ (Gen T n A' B' : ℝ) * Eng T n A' B' := by
      exact_mod_cast hgc
    have hmain := (half_le _ n hfx).trans hgc'
    have hcov : (((fb A' B' T).card : ℝ) ^ (n + 1) / 2) ^ 2 / (Kc * Md) ≤ Gen T n A' B' := by
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ (Gen T n A' B' : ℝ) * Eng T n A' B' := hmain
        _ ≤ (Gen T n A' B' : ℝ) * (Kc * Md) := mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring
    exact ⟨hcov, by exact_mod_cast Gen_le T n A' B'⟩

end ECDLP.L49
