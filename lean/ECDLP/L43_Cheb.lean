import Mathlib

/-!
# L43 (2),(3): factor-base size (Chebyshev over curves) and Markov

`K` a finite field of odd characteristic, `T ⊆ K`, `X = |T|`,
`f(A,B) = ∑_{x∈T} (1 + χ(x³+Ax+B))` (integer valued, `χ` = quadratic character).
-/
namespace ECDLP.L43

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- the factor-base size `f(A,B)` -/
noncomputable def fsize (T : Finset K) (A B : K) : ℤ :=
  ∑ x ∈ T, (1 + quadraticChar K (x ^ 3 + A * x + B))

theorem sum_chi_shift (hK : ringChar K ≠ 2) (c : K) :
    ∑ B : K, quadraticChar K (c + B) = 0 := by
  rw [← quadraticChar_sum_zero hK]
  exact Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun _ => rfl)

theorem sum_chi_sq_le (c : K) : ∑ B : K, quadraticChar K (c + B) ^ 2 ≤ Fintype.card K := by
  calc ∑ B : K, quadraticChar K (c + B) ^ 2 ≤ ∑ _B : K, (1 : ℤ) := by
        refine sum_le_sum (fun B _ => ?_)
        by_cases h : c + B = 0
        · simp [h]
        · rcases quadraticChar_dichotomy h with h2 | h2 <;> simp [h2]
    _ = Fintype.card K := by simp

/-- the linear change of variables `(A,B) ↦ (l_x, l_x')` -/
noncomputable def lin (x x' : K) (h : x ≠ x') : K × K ≃ K × K where
  toFun p := (x ^ 3 + p.1 * x + p.2, x' ^ 3 + p.1 * x' + p.2)
  invFun q := (((q.1 - q.2) - (x ^ 3 - x' ^ 3)) / (x - x'),
    q.1 - x ^ 3 - ((q.1 - q.2) - (x ^ 3 - x' ^ 3)) / (x - x') * x)
  left_inv p := by
    have : x - x' ≠ 0 := sub_ne_zero.2 h
    ext
    · simp only; field_simp; ring
    · simp only; field_simp; ring
  right_inv q := by
    have : x - x' ≠ 0 := sub_ne_zero.2 h
    ext
    · simp only; field_simp; ring
    · simp only; field_simp; ring

theorem pair_sum_offdiag (hK : ringChar K ≠ 2) (x x' : K) (h : x ≠ x') :
    ∑ p : K × K, quadraticChar K (x ^ 3 + p.1 * x + p.2) *
      quadraticChar K (x' ^ 3 + p.1 * x' + p.2) = 0 := by
  rw [Fintype.sum_equiv (lin x x' h) (fun p => quadraticChar K (x ^ 3 + p.1 * x + p.2) *
      quadraticChar K (x' ^ 3 + p.1 * x' + p.2)) (fun q => quadraticChar K q.1 * quadraticChar K q.2)
      (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, quadraticChar_sum_zero hK, zero_mul]

theorem pair_sum_diag (hK : ringChar K ≠ 2) (x : K) :
    ∑ p : K × K, quadraticChar K (x ^ 3 + p.1 * x + p.2) ^ 2 ≤ (Fintype.card K : ℤ) ^ 2 := by
  rw [Fintype.sum_prod_type]
  calc _ ≤ ∑ _a : K, (Fintype.card K : ℤ) := by
        refine sum_le_sum (fun a _ => ?_)
        have := sum_chi_sq_le (K := K) (x ^ 3 + a * x)
        simpa using this
    _ = _ := by simp [sq]

theorem pair_sum_f (T : Finset K) :
    ∑ p : K × K, (fsize T p.1 p.2 - (T.card : ℤ)) ^ 2 =
      ∑ x ∈ T, ∑ x' ∈ T, ∑ p : K × K, quadraticChar K (x ^ 3 + p.1 * x + p.2) *
        quadraticChar K (x' ^ 3 + p.1 * x' + p.2) := by
  have : ∀ p : K × K, fsize T p.1 p.2 - (T.card : ℤ) = ∑ x ∈ T, quadraticChar K (x ^ 3 + p.1 * x + p.2) := by
    intro p; simp [fsize, sum_add_distrib]
  simp_rw [this, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]

/-- second moment: `∑_{(A,B)} (f - X)² ≤ X q²` -/
theorem second_moment (hK : ringChar K ≠ 2) (T : Finset K) :
    ∑ p : K × K, (fsize T p.1 p.2 - (T.card : ℤ)) ^ 2 ≤ (T.card : ℤ) * (Fintype.card K : ℤ) ^ 2 := by
  rw [pair_sum_f]
  calc _ ≤ ∑ x ∈ T, (Fintype.card K : ℤ) ^ 2 := by
        refine sum_le_sum (fun x hx => ?_)
        rw [← add_sum_erase _ _ hx]
        have h0 : ∑ x' ∈ T.erase x, ∑ p : K × K, quadraticChar K (x ^ 3 + p.1 * x + p.2) *
            quadraticChar K (x' ^ 3 + p.1 * x' + p.2) = 0 :=
          sum_eq_zero (fun x' hx' => pair_sum_offdiag hK x x' (Ne.symm (ne_of_mem_erase hx')))
        rw [h0, add_zero]
        simpa [sq] using pair_sum_diag hK x
    _ = _ := by simp

/-- **Chebyshev****: `#{(A,B) : 2 f(A,B) ≤ X} · X ≤ 4 q²`. -/
theorem factor_base_chebyshev (hK : ringChar K ≠ 2) (T : Finset K) :
    ((univ.filter (fun p : K × K => 2 * fsize T p.1 p.2 ≤ (T.card : ℤ))).card : ℤ) * (T.card : ℤ)
      ≤ 4 * (Fintype.card K : ℤ) ^ 2 := by
  set X : ℤ := (T.card : ℤ) with hXdef
  set N := (univ.filter (fun p : K × K => 2 * fsize T p.1 p.2 ≤ X)).card
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · simp [X, h0]
  have hX : (0 : ℤ) < X := by rw [hXdef]; exact_mod_cast hpos
  have h1 : (N : ℤ) * (X ^ 2) ≤ 4 * ∑ p : K × K, (fsize T p.1 p.2 - X) ^ 2 := by
    calc (N : ℤ) * X ^ 2 = ∑ _p ∈ univ.filter (fun p : K × K => 2 * fsize T p.1 p.2 ≤ X), X ^ 2 := by
          simp [N]
      _ ≤ ∑ p ∈ univ.filter (fun p : K × K => 2 * fsize T p.1 p.2 ≤ X),
            4 * (fsize T p.1 p.2 - X) ^ 2 := by
          refine sum_le_sum (fun p hp => ?_)
          have := (mem_filter.1 hp).2
          nlinarith
      _ = 4 * ∑ p ∈ univ.filter (fun p : K × K => 2 * fsize T p.1 p.2 ≤ X),
            (fsize T p.1 p.2 - X) ^ 2 := by rw [mul_sum]
      _ ≤ _ := by
          have := sum_le_sum_of_subset_of_nonneg (f := fun p : K × K => (fsize T p.1 p.2 - X) ^ 2)
            (filter_subset (fun p : K × K => 2 * fsize T p.1 p.2 ≤ X) (univ : Finset (K × K)))
            (fun _ _ _ => sq_nonneg _)
          linarith
  have h2 := second_moment hK T
  have h3 : (N : ℤ) * X ^ 2 ≤ 4 * (X * (Fintype.card K : ℤ) ^ 2) := by
    refine h1.trans ?_; gcongr
  have : ((N : ℤ) * X - 4 * (Fintype.card K : ℤ) ^ 2) * X ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **Markov over curves.** -/
theorem markov_count {α : Type*} [Fintype α] (E : α → ℝ) (hE : ∀ a, 0 ≤ E a) (M K : ℝ)
    (hM : 0 < M) (hK : 0 < K) (hsum : ∑ a, E a ≤ M * Fintype.card α) :
    (((univ : Finset α).filter (fun a => K * M < E a)).card : ℝ) ≤ Fintype.card α / K := by
  classical
  rw [le_div_iff₀ hK]
  set S := (univ : Finset α).filter (fun a => K * M < E a)
  have h1 : (S.card : ℝ) * (K * M) ≤ ∑ a ∈ S, E a := by
    rw [← nsmul_eq_mul]
    calc S.card • (K * M) = ∑ _a ∈ S, K * M := by simp
      _ ≤ _ := sum_le_sum (fun a ha => (mem_filter.1 ha).2.le)
  have h2 : ∑ a ∈ S, E a ≤ ∑ a, E a := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => hE a)
  have : (S.card : ℝ) * K * M ≤ Fintype.card α * M := by nlinarith
  exact le_of_mul_le_mul_right this hM

end ECDLP.L43
