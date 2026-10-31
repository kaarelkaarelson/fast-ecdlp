import ECDLP.L70_Capstone

/-!
# L80 / Poly: polynomial bounds are sub-exponential, in the exact form the capstones use
`poly_subexp d : ∀ k ≥ 1, ∃ C, ∀ L, (L+1)^d ≤ C * 2^(L/k)`.
-/
namespace ECDLP.L80
open Factoring.Aux

theorem poly_subexp (d : ℕ) (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℕ, ∀ L : ℕ, (L + 1) ^ d ≤ C * 2 ^ (L / k) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, fun L => by simp [Nat.one_le_two_pow]⟩
  · have hkd : 0 < k * d := Nat.mul_pos hk hd
    refine ⟨2 * (k * d) ^ d, fun L => ?_⟩
    have h1 : L + 1 ≤ (k * d) * 2 ^ ((L + 1) / (k * d)) := le_two_pow_div (L + 1) (k * d) hkd
    have h2 : (L + 1) ^ d ≤ ((k * d) * 2 ^ ((L + 1) / (k * d))) ^ d := Nat.pow_le_pow_left h1 d
    have h3 : ((k * d) * 2 ^ ((L + 1) / (k * d))) ^ d = (k * d) ^ d * 2 ^ (d * ((L + 1) / (k * d))) := by
      rw [mul_pow, ← pow_mul, mul_comm ((L + 1) / (k * d)) d]
    have h4 : d * ((L + 1) / (k * d)) ≤ (L + 1) / k := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.mul_div_le _ _
    have h5 : (L + 1) / k ≤ L / k + 1 := by
      calc (L + 1) / k ≤ (L + k) / k := Nat.div_le_div_right (by omega)
        _ = L / k + 1 := by rw [Nat.add_div_right _ (by omega)]
    have h6 : 2 ^ (d * ((L + 1) / (k * d))) ≤ 2 * 2 ^ (L / k) := by
      calc 2 ^ (d * ((L + 1) / (k * d))) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ (L / k) := by ring
    calc (L + 1) ^ d ≤ (k * d) ^ d * 2 ^ (d * ((L + 1) / (k * d))) := by rw [← h3]; exact h2
      _ ≤ (k * d) ^ d * (2 * 2 ^ (L / k)) := Nat.mul_le_mul_left _ h6
      _ = 2 * (k * d) ^ d * 2 ^ (L / k) := by ring

end ECDLP.L80
