import ECDLP.L63_Size
import ECDLP.L65_Fam

/-!
# L65 / Params: the explicit parameters in terms of `X`, for every `p` (also tiny `Nat.size p`)

`n` is any number with `Nat.size p + 4 ≤ 4 n` (e.g. the input length, which is at least `size p` and `≥ 1`), `X = 2^(sOf n)`,
`n ≤ 4 X^4`.  Then `L'' := size p + 4 ≤ 16 X^4`, `D² ≤ L''`, `A ≤ 3 X`, `A D ≤ 12 X^3`.
-/
namespace ECDLP.L65
open ECDLP.L59 Factoring.Aux

theorem small_params (L : ℕ) (hL : L < 4) : DP L = 2 ∧ AP L = 2 := by
  have hlog : Nat.log 2 L < 2 := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp
    · exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).2 (by omega)
  have hj : jm1 L = 0 := by unfold jm1; omega
  refine ⟨?_, ?_⟩
  · simp [DP, kP, hj]
  · simp [AP, hj]

theorem DD_le (L : ℕ) : DP L * DP L ≤ L + 4 := by
  by_cases h : 4 ≤ L
  · have := D_sq_le L h; omega
  · obtain ⟨h1, _⟩ := small_params L (by omega); rw [h1]; omega

theorem AD_le_X (L n : ℕ) (hn : L + 4 ≤ 4 * n) : AP L * DP L ≤ 12 * Xs n ^ 3 := by
  have hX := Xs_pos n
  have hnX := Xs_n_le n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  suffices h : (AP L * DP L) ^ 4 ≤ (12 * Xs n ^ 3) ^ 4 from
    le_of_pow_le_pow_left₀ (by norm_num) (Nat.zero_le _) h
  have h12 : (12 * Xs n ^ 3) ^ 4 = 20736 * (Xs n ^ 4) ^ 3 := by ring
  rw [h12]
  have hL16 : L + 4 ≤ 16 * Xs n ^ 4 := by omega
  by_cases h : 4 ≤ L
  · have h1 := AD_four_le L h
    have h2 : L ^ 3 ≤ (16 * Xs n ^ 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h3 : (16 * Xs n ^ 4) ^ 3 = 4096 * (Xs n ^ 4) ^ 3 := by ring
    omega
  · obtain ⟨h1, h2⟩ := small_params L (by omega)
    rw [h1, h2]
    have : 1 ≤ (Xs n ^ 4) ^ 3 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hX)
    omega

theorem A_le_X (L n : ℕ) (hn : L + 4 ≤ 4 * n) : AP L ≤ 3 * Xs n := by
  have hX := Xs_pos n
  have hnX := Xs_n_le n
  suffices h : (AP L) ^ 4 ≤ (3 * Xs n) ^ 4 from
    le_of_pow_le_pow_left₀ (by norm_num) (Nat.zero_le _) h
  have h12 : (3 * Xs n) ^ 4 = 81 * Xs n ^ 4 := by ring
  rw [h12]
  have hL16 : L + 4 ≤ 16 * Xs n ^ 4 := by omega
  have : 1 ≤ Xs n ^ 4 := Nat.one_le_pow _ _ hX
  by_cases h : 4 ≤ L
  · have := A_four_le L h; omega
  · obtain ⟨h1, h2⟩ := small_params L (by omega)
    rw [h2]; omega

end ECDLP.L65
