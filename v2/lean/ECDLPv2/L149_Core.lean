import Mathlib

/-! # L149: Lean-checked arithmetic of the G1 schedule (20 levels + top level -> crossover log2 L_c).

Everything here is *arithmetic* about an explicit integer-exponent schedule; it does NOT prove that
Theorem A holds for that schedule (assumption R1) nor any V8x property.  Exponents x_l = log2 K_l are naturals,
K_l = 2^x_l, g_l = 2^(x_l+s_l), x_{l+1} = 2(x_l+s_l).  Powers 2^t of astronomic size are never evaluated: they are
capped by monotonicity (2^-x <= 2^-min(x,60), 2^-(x+s) <= 2^-min(x+s,100)).
-/

namespace L149

/-- rational upper bounds: ln 2 < 0.6931471808 (Mathlib), 1/sqrt 2 <= 0.707106781187 -/
def LN2U : ℚ := 6931471808 / 10 ^ 10
def RHOU : ℚ := 707106781187 / 10 ^ 12
/-- pieces constant bound: c + 5 <= 2^18 -/
def CC : ℕ := 2 ^ 18 - 5

lemma ln2_le : Real.log 2 ≤ (LN2U : ℝ) := by
  have := Real.log_two_lt_d9
  have h : (LN2U : ℝ) = 0.6931471808 := by unfold LN2U; norm_num
  rw [h]; exact this.le

lemma rho_le : 1 / Real.sqrt 2 ≤ (RHOU : ℝ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  have hr : (RHOU : ℝ) = 707106781187 / 10 ^ 12 := by unfold RHOU; push_cast; norm_num
  rw [hr, div_le_iff₀ hp]
  by_contra h
  push_neg at h
  nlinarith

/-- one level: Bool checker over ℚ/ℕ -/
def stepB (tight : Bool) (x s : ℕ) (z Ein Eout : ℚ) : Bool :=
  let m := min (x + s) 100
  let t := min x 60
  decide (0 < z) && decide (z ≤ 1) &&
  decide (LN2U * (1 + 2 * x + s) ≤ z ^ 2 * 2 ^ (s + 1)) &&
  decide (19 + 2 * x ≤ 4 * (x + s)) && decide (2 ≤ x) &&
  decide (1 ≤ z ^ 2 * 2 ^ (2 * m)) &&
  decide ((if tight then (RHOU + 2 * z + 1 / 2 ^ m) * Ein + 2 / 2 ^ t + (CC : ℚ) / 2 ^ (4 * m)
           else (RHOU + 3 * z) * Ein + 3 / 2 ^ t) ≤ Eout) &&
  decide (Eout ≤ 1) && decide (0 ≤ Ein)

/-- the recursion of the error bound over the whole schedule; returns final (x_n, E_n) -/
def chainB (tight : Bool) : ℕ → ℚ → List (ℕ × ℚ × ℚ) → Option (ℕ × ℚ)
  | x, E, [] => some (x, E)
  | x, E, (s, z, E') :: tl =>
      if stepB tight x s z E E' then chainB tight (2 * (x + s)) E' tl else none

/-- semantic content of one level (real-number statements) -/
structure StepOK (tight : Bool) (x s : ℕ) (z Ein Eout : ℚ) : Prop where
  zpos : 0 < z
  zle : z ≤ 1
  case2 : Real.log 2 * (1 + 2 * (x : ℝ) + s) ≤ (z : ℝ) ^ 2 * 2 ^ (s + 1)
  c4 : ∀ c : ℕ, c ≤ CC → 2 * ((c + 5) * (2 ^ x) ^ 2) ≤ (2 ^ (x + s)) ^ 4
  invg : (1 : ℚ) / 2 ^ (x + s) ≤ z
  xge : 2 ≤ x
  erec : ∀ e : ℝ, e ≤ Ein →
    (if tight then (1 / Real.sqrt 2 + 2 * z + 1 / 2 ^ (x + s)) * e + 2 / 2 ^ x + (CC : ℝ) / 2 ^ (4 * (x + s))
     else (1 / Real.sqrt 2 + 3 * z) * e + 3 / 2 ^ x) ≤ Eout
  Ele : Eout ≤ 1
  Ein0 : 0 ≤ Ein

lemma pow_cap {a : ℚ} (h1 : 0 < a) (n m : ℕ) (hm : m ≤ n) (ha : 1 ≤ a) : a ^ m ≤ a ^ n :=
  pow_le_pow_right₀ ha hm

lemma stepB_sound (tight : Bool) (x s : ℕ) (z Ein Eout : ℚ) (h : stepB tight x s z Ein Eout = true) :
    StepOK tight x s z Ein Eout := by
  unfold stepB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, hz1⟩, hc2⟩, hc4⟩, hx⟩, hg⟩, hr⟩, hE⟩, hE0⟩ := h
  have hm : min (x + s) 100 ≤ x + s := min_le_left _ _
  have ht : min x 60 ≤ x := min_le_left _ _
  have h2m : (2:ℚ) ^ (min (x + s) 100) ≤ 2 ^ (x + s) := pow_le_pow_right₀ (by norm_num) hm
  have h2t : (2:ℚ) ^ (min x 60) ≤ 2 ^ x := pow_le_pow_right₀ (by norm_num) ht
  have h2pos : ∀ n : ℕ, (0:ℚ) < 2 ^ n := fun n => by positivity
  have hinvg : (1:ℚ) / 2 ^ (x + s) ≤ z := by
    have h1 : (1:ℚ) / 2 ^ (x + s) ≤ 1 / 2 ^ (min (x + s) 100) :=
      one_div_le_one_div_of_le (h2pos _) h2m
    have h3 : (1:ℚ) / 2 ^ (min (x + s) 100) ≤ z := by
      have hpos := h2pos (min (x + s) 100)
      have : (1:ℚ) ≤ (z * 2 ^ (min (x + s) 100)) ^ 2 := by
        calc (1:ℚ) ≤ z ^ 2 * 2 ^ (2 * min (x + s) 100) := hg
          _ = (z * 2 ^ (min (x + s) 100)) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm (min (x+s) 100) 2]
      have h4 : 1 ≤ z * 2 ^ (min (x + s) 100) := by nlinarith [mul_pos hz hpos]
      rw [div_le_iff₀ hpos]; exact h4
    exact h1.trans h3
  refine ⟨hz, hz1, ?_, ?_, hinvg, hx, ?_, hE, hE0⟩
  · have := ln2_le
    have hq : (LN2U : ℝ) * (1 + 2 * (x : ℝ) + s) ≤ (z : ℝ) ^ 2 * 2 ^ (s + 1) := by exact_mod_cast hc2
    have hpos : (0:ℝ) ≤ 1 + 2 * (x : ℝ) + s := by positivity
    nlinarith
  · intro c hc
    have h18 : c + 5 ≤ 2 ^ 18 := by unfold CC at hc; omega
    calc 2 * ((c + 5) * (2 ^ x) ^ 2) ≤ 2 * (2 ^ 18 * (2 ^ x) ^ 2) := by gcongr
      _ = 2 ^ (19 + 2 * x) := by ring
      _ ≤ 2 ^ (4 * (x + s)) := Nat.pow_le_pow_right (by norm_num) hc4
      _ = (2 ^ (x + s)) ^ 4 := by rw [← pow_mul, mul_comm]
  · intro e he
    have hrho := rho_le
    have hz' : (0:ℝ) < z := by exact_mod_cast hz
    have hE0' : (0:ℝ) ≤ Ein := by exact_mod_cast hE0
    have hrp : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
    have h2R : ∀ n : ℕ, (0:ℝ) < 2 ^ n := fun n => by positivity
    have hmR : (2:ℝ) ^ (min (x + s) 100) ≤ 2 ^ (x + s) := pow_le_pow_right₀ (by norm_num) hm
    have htR : (2:ℝ) ^ (min x 60) ≤ 2 ^ x := pow_le_pow_right₀ (by norm_num) ht
    have m4 : (2:ℝ) ^ (4 * min (x + s) 100) ≤ 2 ^ (4 * (x + s)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hA : ∀ k : ℝ, 0 ≤ k → (1 / Real.sqrt 2 + k * z) * e ≤ ((RHOU:ℝ) + k * z) * Ein := by
      intro k hk
      have h1 : (1 / Real.sqrt 2 + k * z) * e ≤ (1 / Real.sqrt 2 + k * z) * Ein :=
        mul_le_mul_of_nonneg_left he (by positivity)
      have h2 : (1 / Real.sqrt 2 + k * z) * Ein ≤ ((RHOU:ℝ) + k * z) * Ein :=
        mul_le_mul_of_nonneg_right (by linarith) hE0'
      exact h1.trans h2
    have hB : ∀ k : ℝ, 0 ≤ k → k / 2 ^ x ≤ k / 2 ^ (min x 60) := fun k hk =>
      div_le_div_of_nonneg_left hk (h2R _) htR
    cases tight
    · simp only [Bool.false_eq_true, ite_false] at hr ⊢
      have hr' : ((RHOU:ℝ) + 3 * z) * Ein + 3 / 2 ^ (min x 60) ≤ Eout := by
        have := (Rat.cast_le (K := ℝ)).mpr hr
        push_cast at this; exact this
      have := hA 3 (by norm_num)
      have := hB 3 (by norm_num)
      linarith
    · simp only [ite_true] at hr ⊢
      have hr' : ((RHOU:ℝ) + 2 * z + 1 / 2 ^ (min (x + s) 100)) * Ein + 2 / 2 ^ (min x 60)
          + (CC:ℝ) / 2 ^ (4 * min (x + s) 100) ≤ Eout := by
        have := (Rat.cast_le (K := ℝ)).mpr hr
        push_cast at this; exact this
      have h1 : 1 / (2:ℝ) ^ (x + s) ≤ 1 / 2 ^ (min (x + s) 100) :=
        div_le_div_of_nonneg_left (by norm_num) (h2R _) hmR
      have h3 : (CC:ℝ) / 2 ^ (4 * (x + s)) ≤ (CC:ℝ) / 2 ^ (4 * min (x + s) 100) :=
        div_le_div_of_nonneg_left (by positivity) (h2R _) m4
      have hA2 := hA 2 (by norm_num)
      have hB2 := hB 2 (by norm_num)
      have h4 : (1 / Real.sqrt 2 + 2 * z + 1 / 2 ^ (x + s)) * e
          ≤ ((RHOU:ℝ) + 2 * z + 1 / 2 ^ (min (x + s) 100)) * Ein := by
        have h5 : (1 / Real.sqrt 2 + 2 * z + 1 / 2 ^ (x + s)) * e
            ≤ (1 / Real.sqrt 2 + 2 * z + 1 / 2 ^ (x + s)) * Ein :=
          mul_le_mul_of_nonneg_left he (by positivity)
        have h6 : (1 / Real.sqrt 2 + 2 * z + 1 / 2 ^ (x + s)) * Ein
            ≤ ((RHOU:ℝ) + 2 * z + 1 / 2 ^ (min (x + s) 100)) * Ein :=
          mul_le_mul_of_nonneg_right (by linarith) hE0'
        exact h5.trans h6
      linarith

/-- chain semantics -/
def ChainOK (tight : Bool) : ℕ → ℚ → List (ℕ × ℚ × ℚ) → ℕ → ℚ → Prop
  | x, E, [], xn, En => x = xn ∧ E = En
  | x, E, (s, z, E') :: tl, xn, En => StepOK tight x s z E E' ∧ ChainOK tight (2 * (x + s)) E' tl xn En

lemma chainB_sound (tight : Bool) : ∀ (l : List (ℕ × ℚ × ℚ)) (x : ℕ) (E : ℚ) (xn : ℕ) (En : ℚ),
    chainB tight x E l = some (xn, En) → ChainOK tight x E l xn En
  | [], x, E, xn, En, h => by
      simp only [chainB, Option.some.injEq, Prod.mk.injEq] at h
      exact h
  | (s, z, E') :: tl, x, E, xn, En, h => by
      simp only [chainB] at h
      split_ifs at h with hb
      exact ⟨stepB_sound tight x s z E E' hb, chainB_sound tight tl _ _ _ _ h⟩

end L149
