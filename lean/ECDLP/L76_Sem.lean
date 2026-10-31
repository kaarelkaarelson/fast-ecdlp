import ECDLP.L51_Strings
import ECDLP.L70_Good

/-!
# L76 / Sem: the flags of the input layer are exactly `Δ ≠ 0 ∧ Nonsingular` (for an odd prime)
`flagD = [1 ≤ (4a³+27b²) mod p]`, `flagE1 = [x³+ax+b ≤ y² (mod p)]`, `flagE2 = [y² ≤ x³+ax+b (mod p)]`.
-/
namespace ECDLP.L76
open ECDLP.L51 WeierstrassCurve

theorem wc_Δ (p a b : ℕ) : (Wc p a b).Δ = -16 * (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem sixteen_ne (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : (16 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) ^ 4 = 0 := by push_cast; norm_num; exact h
  have h3 : ((2 : ℕ) : ZMod p) = 0 := pow_eq_zero_iff (by norm_num) |>.1 h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem delta_ne_iff (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (a b : ℕ) :
    (Wc p a b).Δ ≠ 0 ↔ ((4 * a ^ 3 + 27 * b ^ 2 : ℕ) : ZMod p) ≠ 0 := by
  rw [wc_Δ]
  have h16 := sixteen_ne p hp3
  push_cast
  constructor
  · intro h h0; apply h; rw [h0]; ring
  · intro h h0
    have : (-16 : ZMod p) ≠ 0 := by simpa using h16
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact this h1
    · exact h h1

theorem nonsing_iff (p : ℕ) [Fact p.Prime] (a b x y : ℕ) (hΔ : (Wc p a b).Δ ≠ 0) :
    (Wc p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p) ↔ ((y * y : ℕ) : ZMod p) = ((x ^ 3 + a * x + b : ℕ) : ZMod p) := by
  haveI : (Wc p a b).IsElliptic := ⟨isUnit_iff_ne_zero.2 hΔ⟩
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  simp only [Wc]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem nat_mod_zero_iff (p n : ℕ) [Fact p.Prime] : (1 ≤ n % p) ↔ ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; omega

theorem flags_iff (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (a b xR yR : ℕ) :
    ((if 1 ≤ (4 * a ^ 3 + 27 * b ^ 2) % p then 1 else 0 : ℕ) = 1 ∧
      (if (xR ^ 3 + a * xR + b) % p ≤ (yR * yR) % p then 1 else 0 : ℕ) = 1 ∧
      (if (yR * yR) % p ≤ (xR ^ 3 + a * xR + b) % p then 1 else 0 : ℕ) = 1) ↔
    ((Wc p a b).Δ ≠ 0 ∧ (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p)) := by
  have hD := delta_ne_iff p hp3 a b
  have hD' : (1 ≤ (4 * a ^ 3 + 27 * b ^ 2) % p) ↔ (Wc p a b).Δ ≠ 0 := by
    rw [hD]; exact nat_mod_zero_iff p _
  have hE : ((yR * yR : ℕ) : ZMod p) = ((xR ^ 3 + a * xR + b : ℕ) : ZMod p) ↔
      (yR * yR) % p = (xR ^ 3 + a * xR + b) % p := ZMod.natCast_eq_natCast_iff' _ _ p
  by_cases h1 : 1 ≤ (4 * a ^ 3 + 27 * b ^ 2) % p
  · have hΔ : (Wc p a b).Δ ≠ 0 := hD'.1 h1
    rw [nonsing_iff p a b xR yR hΔ, hE]
    simp only [h1, if_true, hΔ, ne_eq, not_false_eq_true, true_and]
    by_cases hA : (xR ^ 3 + a * xR + b) % p ≤ (yR * yR) % p <;> by_cases hB : (yR * yR) % p ≤ (xR ^ 3 + a * xR + b) % p <;>
      simp [hA, hB] <;> omega
  · have : ¬ ((Wc p a b).Δ ≠ 0) := fun h => h1 (hD'.2 h)
    simp [h1, this]

end ECDLP.L76
