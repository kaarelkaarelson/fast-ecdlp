import ECDLP.L57_Main

/-!
# L57 / Par: efficient gadget parameters exist (and satisfy the size conditions of L54/L56)

`par_efficient Z`: for every `Z ≥ 1` (the bit length each shared slot must hold) there is an `NPar` (`k` odd, `D = 2^k`,
`A·A = 2D`, `A·h = D`) and digit bits `b` with `Z ≤ b D`, `b ≤ D`, `D² ≤ 16 Z`, and with the ring-exponent multiplier
`w = 5` all three numeric facts behind `SizeOK` (`1 ≤ D w`, `2D ≤ A·A`, `12 D 4^b ≤ 2^{D w}`).
-/
noncomputable section
namespace ECDLP.L57
open Finset ECDLP.L34 ECDLP.L38

theorem par_efficient (Z : ℕ) (hZ : 1 ≤ Z) :
    ∃ N0 : NPar, 1 ≤ N0.b ∧ Z ≤ N0.b * 2 ^ N0.k ∧ N0.b ≤ 2 ^ N0.k ∧
      2 ^ N0.k * 2 ^ N0.k ≤ 16 * Z ∧ 1 ≤ 2 ^ N0.k * 5 ∧ 2 * 2 ^ N0.k ≤ N0.A * N0.A ∧
      12 * (2 ^ N0.k * (2 ^ N0.b * 2 ^ N0.b)) ≤ 2 ^ (2 ^ N0.k * 5) := by
  classical
  have hex : ∃ j, Z ≤ 2 ^ (4 * j + 2) := ⟨Z, by
    have h1 := Nat.lt_two_pow_self (n := Z)
    exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  set j := Nat.find hex with hj
  have hjs : Z ≤ 2 ^ (4 * j + 2) := Nat.find_spec hex
  have hjm : j = 0 ∨ (0 < j ∧ 2 ^ (4 * (j - 1) + 2) < Z) := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact Or.inl h
    · right
      have := Nat.find_min hex (show j - 1 < j by omega)
      exact ⟨h, by omega⟩
  set D := 2 ^ (2 * j + 1) with hD
  have hDD : D * D = 2 ^ (4 * j + 2) := by rw [hD, ← pow_add]; congr 1; ring
  have hD2 : 2 ≤ D := by
    rw [hD]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  set b := (Z + D - 1) / D with hb
  have hDpos : 0 < D := by omega
  have hbZ : Z ≤ b * D := by
    have h2 := Nat.div_add_mod (Z + D - 1) D
    have h3 := Nat.mod_lt (Z + D - 1) hDpos
    have e := mul_comm ((Z + D - 1) / D) D
    rw [hb]; omega
  have hZD : Z ≤ D * D := by rw [hDD]; exact hjs
  have hbD : b ≤ D := by
    rw [hb, Nat.div_le_iff_le_mul_add_pred hDpos]
    omega
  have hb1 : 1 ≤ b := by
    rw [hb, Nat.le_div_iff_mul_le hDpos]; omega
  have hA' : 2 ^ (j + 1) * 2 ^ (j + 1) = 2 ^ ((2 * j + 1) + 1) := by
    rw [← pow_add]; congr 1; ring
  have hAh' : 2 ^ (j + 1) * 2 ^ j = 2 ^ (2 * j + 1) := by
    rw [← pow_add]; congr 1; ring
  let P0 : Par := { k := 2 * j + 1, A := 2 ^ (j + 1), w := 0, b := b, hA := hA' }
  let N0 : NPar := { toPar := P0, h := 2 ^ j, hAh := hAh' }
  refine ⟨N0, hb1, hbZ, hbD, ?_, ?_, ?_, ?_⟩
  · show D * D ≤ 16 * Z
    rw [hDD]
    rcases hjm with h | h
    · rw [h]; omega
    · obtain ⟨hj0, h⟩ := h
      have : 2 ^ (4 * j + 2) = 16 * 2 ^ (4 * (j - 1) + 2) := by
        have : 4 * j + 2 = 4 * (j - 1) + 2 + 4 := by omega
        rw [this, pow_add]; ring
      omega
  · show 1 ≤ D * 5; omega
  · show 2 * D ≤ 2 ^ (j + 1) * 2 ^ (j + 1)
    rw [hA', pow_succ]; omega
  · show 12 * (D * (2 ^ b * 2 ^ b)) ≤ 2 ^ (D * 5)
    have hk : 2 * j + 1 ≤ D := (Nat.lt_two_pow_self).le
    have h12 : 12 * (D * (2 ^ b * 2 ^ b)) ≤ 2 ^ (2 * j + 1 + 2 * b + 4) := by
      have e : 2 ^ (2 * j + 1 + 2 * b + 4) = 16 * (D * (2 ^ b * 2 ^ b)) := by
        rw [pow_add, pow_add, ← hD, two_mul, pow_add]; ring
      rw [e]
      have : 0 ≤ D * (2 ^ b * 2 ^ b) := Nat.zero_le _
      omega
    exact h12.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

end ECDLP.L57
end
