import Mathlib
import ECDLP.L40_Generic
import ECDLP.L43_Cheb
import ECDLP.L43_Curve

/-!
# L43 (4): coverage assembly over a finite field `K` of odd characteristic

For `(A,B) ∈ K²` let `F_{A,B}` = nonzero points of `y² = x³+Ax+B` with `x ∈ T` (`fb A B T`),
`E(A,B) = energy (n+1) F_{A,B}` in the group `(shortW A B).Point` (Mathlib's group law),
`G(A,B)` = set of group elements with a *generic* decomposition into `n+1` factor-base points.
Hypothesis `hT1` (the average energy bound, an assumption here): `∑_{Δ≠0} E(A,B) ≤ M q²`.
-/
namespace ECDLP.L43

open Finset ECDLP.L40

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- number of singular `(A,B)` is at most `q` (char ≠ 2, 3) -/
theorem card_disc_zero_le (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) :
    (univ.filter (fun p : K × K => disc p.1 p.2 = 0)).card ≤ Fintype.card K := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero _ h3
  have : univ.filter (fun p : K × K => disc p.1 p.2 = 0) ⊆
      (univ : Finset K).image (fun t => (-3 * t ^ 2, 2 * t ^ 3)) := by
    intro ⟨A, B⟩ hp
    have hp : 4 * A ^ 3 + 27 * B ^ 2 = 0 := (mem_filter.1 hp).2
    simp only [mem_image, mem_univ, true_and, Prod.mk.injEq]
    by_cases hA : A = 0
    · subst hA
      have : B = 0 := by
        have : 27 * B ^ 2 = 0 := by linear_combination hp
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h h27
        · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
      exact ⟨0, by simp [this]⟩
    · refine ⟨-3 * B / (2 * A), ?_, ?_⟩
      · field_simp; linear_combination (-1 : K) * hp
      · field_simp; linear_combination (-B) * hp
  exact (card_le_card this).trans (card_image_le.trans (by simp))


/-- energy of the factor base of `y² = x³+Ax+B` in Mathlib's group of points -/
noncomputable def Eng (T : Finset K) (n : ℕ) (A B : K) : ℕ := energy (n + 1) (fb A B T)

/-- number of group elements with a generic decomposition into `n+1` factor-base points -/
noncomputable def Gen (T : Finset K) (n : ℕ) (A B : K) : ℕ :=
  (sums ((Fintype.piFinset (fun _ : Fin (n + 1) => fb A B T)).filter
    (fun t => Generic (xc (shortW A B)) t))).card

/-- the arithmetic step: `f ≥ 6n+1` gives `(f^{n+1}/2)² ≤ (f^{n+1} - 3 n f^n)²` -/
theorem half_le (f n : ℕ) (h : 6 * n < f) :
    ((f : ℝ) ^ (n + 1) / 2) ^ 2 ≤ (((f ^ (n + 1) - 3 * n * f ^ n : ℕ)) : ℝ) ^ 2 := by
  have hle : 3 * n * f ^ n ≤ f ^ (n + 1) := by
    rw [pow_succ]; nlinarith [Nat.zero_le (f ^ n)]
  rw [Nat.cast_sub hle]
  push_cast
  have h1 : (6 * n : ℝ) ≤ f := by exact_mod_cast h.le
  have h2 : (0 : ℝ) ≤ (f : ℝ) ^ n := by positivity
  have h3 : (f : ℝ) ^ (n + 1) / 2 ≤ (f : ℝ) ^ (n + 1) - 3 * n * (f : ℝ) ^ n := by
    rw [pow_succ]; nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  have h4 : (0 : ℝ) ≤ (f : ℝ) ^ (n + 1) / 2 := by positivity
  exact pow_le_pow_left₀ h4 h3 2

/-- **assembly**.**  Let `T ⊆ K`, `X = |T| ≥ 12 n`, and assume the average energy bound
`∑_{Δ≠0} E_{n+1}(F_{A,B}) ≤ M q²` (hypothesis `hT1`).  Then outside a set `Bad ⊆ K²` of size
`≤ q²(1/Kc + 4/X) + q`, the curve is nonsingular, `|F| > X/2`, `E ≤ Kc·M`, and the generic
coverage satisfies `(|F|^{n+1}/2)² ≤ |G|·E`, hence `|G| ≥ (|F|^{n+1}/2)²/(Kc·M)`. -/
theorem theorem3 (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) (T : Finset K) (hX : 0 < T.card)
    (n : ℕ) (hXn : 12 * n ≤ T.card) (M Kc : ℝ) (hM : 0 < M) (hKc : 0 < Kc)
    (hT1 : ∑ p : K × K, (if disc p.1 p.2 = 0 then (0 : ℝ) else (Eng T n p.1 p.2 : ℝ))
        ≤ M * (Fintype.card K : ℝ) ^ 2) :
    ∃ Bad : Finset (K × K),
      (Bad.card : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 * (1 / Kc + 4 / T.card) + Fintype.card K ∧
      ∀ p : K × K, p ∉ Bad →
        disc p.1 p.2 ≠ 0 ∧ (T.card : ℝ) < 2 * (fb p.1 p.2 T).card ∧
        (Eng T n p.1 p.2 : ℝ) ≤ Kc * M ∧
        (((fb p.1 p.2 T).card : ℝ) ^ (n + 1) / 2) ^ 2 ≤ (Gen T n p.1 p.2 : ℝ) * Eng T n p.1 p.2 ∧
        (((fb p.1 p.2 T).card : ℝ) ^ (n + 1) / 2) ^ 2 / (Kc * M) ≤ Gen T n p.1 p.2 := by
  classical
  set q : ℝ := (Fintype.card K : ℝ) with hq
  let E' : K × K → ℝ := fun p => if disc p.1 p.2 = 0 then 0 else (Eng T n p.1 p.2 : ℝ)
  let sing := (univ : Finset (K × K)).filter (fun p => disc p.1 p.2 = 0)
  let low := (univ : Finset (K × K)).filter (fun p => 2 * fsize T p.1 p.2 ≤ (T.card : ℤ))
  let high := (univ : Finset (K × K)).filter (fun p => Kc * M < E' p)
  refine ⟨sing ∪ low ∪ high, ?_, ?_⟩
  · have hs : (sing.card : ℝ) ≤ q := by
      have h : sing.card ≤ Fintype.card K := card_disc_zero_le hK h3
      rw [hq]; exact_mod_cast h
    have hl : (low.card : ℝ) ≤ 4 * q ^ 2 / T.card := by
      have h : (low.card : ℤ) * (T.card : ℤ) ≤ 4 * (Fintype.card K : ℤ) ^ 2 :=
        factor_base_chebyshev hK T
      have hX' : (0 : ℝ) < T.card := by exact_mod_cast hX
      rw [le_div_iff₀ hX', hq]
      exact_mod_cast h
    have hh : (high.card : ℝ) ≤ q ^ 2 / Kc := by
      have := markov_count E' (fun p => by simp only [E']; split_ifs <;> positivity) M Kc hM hKc
        (by simpa [E', Fintype.card_prod, sq] using hT1)
      simpa [high, Fintype.card_prod, sq, hq] using this
    calc ((sing ∪ low ∪ high).card : ℝ) ≤ sing.card + low.card + high.card := by
          exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ q + 4 * q ^ 2 / T.card + q ^ 2 / Kc := by linarith
      _ = q ^ 2 * (1 / Kc + 4 / T.card) + q := by ring
  · intro p hp
    simp only [mem_union, not_or, sing, low, high, mem_filter, mem_univ, true_and, not_lt,
      not_le] at hp
    obtain ⟨⟨hd, hlow⟩, hhigh⟩ := hp
    have hcard : ((fb p.1 p.2 T).card : ℤ) = fsize T p.1 p.2 := card_fb hK p.1 p.2 hd T
    have hF : (T.card : ℝ) < 2 * (fb p.1 p.2 T).card := by
      have : (T.card : ℤ) < 2 * ((fb p.1 p.2 T).card : ℤ) := by rw [hcard]; exact hlow
      exact_mod_cast this
    have hE : (Eng T n p.1 p.2 : ℝ) ≤ Kc * M := by
      have := hhigh; simp only [E', hd, ite_false] at this; exact this
    have hfx : 6 * n < (fb p.1 p.2 T).card := by
      have : (T.card : ℤ) < 2 * ((fb p.1 p.2 T).card : ℤ) := by rw [hcard]; exact hlow
      omega
    have hgc := generic_coverage (n := n) (fb p.1 p.2 T) (xc (shortW p.1 p.2))
      (fun a => card_fibre_le_two _ _ a)
    have hgc' : (((fb p.1 p.2 T).card ^ (n + 1) - 3 * n * (fb p.1 p.2 T).card ^ n : ℕ) : ℝ) ^ 2
        ≤ (Gen T n p.1 p.2 : ℝ) * Eng T n p.1 p.2 := by
      exact_mod_cast hgc
    have hmain := (half_le _ n hfx).trans hgc'
    refine ⟨hd, hF, hE, hmain, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ (Gen T n p.1 p.2 : ℝ) * Eng T n p.1 p.2 := hmain
      _ ≤ (Gen T n p.1 p.2 : ℝ) * (Kc * M) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring

end ECDLP.L43
