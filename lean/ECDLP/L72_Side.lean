import ECDLP.L69_Tau

/-!
# L72 / Side: the side condition on `r` for `ok_U0`, and arithmetic of the edge family

`Ub r n = Uc r * X^4 <= 2^(Sb n)` as soon as `r + 1 <= 2^19000`; hence `EdgeReq r V ..` gives `Ub r n <= V`.
-/
namespace ECDLP.L72
open Factoring.Aux ECDLP.L65 ECDLP.L60

theorem pow_le_two_pow_mul (X : ℕ) : X ^ 4 ≤ 2 ^ (4 * X) := by
  have h : X < 2 ^ X := Nat.lt_two_pow_self
  calc X ^ 4 ≤ (2 ^ X) ^ 4 := Nat.pow_le_pow_left h.le 4
    _ = 2 ^ (4 * X) := by rw [← pow_mul]; ring_nf

theorem Ub_le_two_pow (r n : ℕ) (hr : r + 1 ≤ 2 ^ 19000) : Ub r n ≤ 2 ^ Sb n := by
  have hX := Xs_pos n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  have h1 : Xs n ≤ Xs n ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : Xs n ^ 4 ≤ 2 ^ (4 * Xs n ^ 3) :=
    le_trans (pow_le_two_pow_mul _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : Uc r ≤ 2 ^ 19021 := by
    unfold Uc
    calc 1544832 * (r + 1) ≤ 2 ^ 21 * 2 ^ 19000 := Nat.mul_le_mul (by norm_num) hr
      _ = 2 ^ 19021 := by rw [← pow_add]
  calc Ub r n = Uc r * Xs n ^ 4 := rfl
    _ ≤ 2 ^ 19021 * 2 ^ (4 * Xs n ^ 3) := Nat.mul_le_mul h3 h2
    _ = 2 ^ (19021 + 4 * Xs n ^ 3) := by rw [← pow_add]
    _ ≤ 2 ^ Sb n := Nat.pow_le_pow_right (by norm_num) (by unfold Sb Scn; omega)

/-- **`ok_U0`**: the total-bits bound is below the value bound, from the family's requirement. -/
theorem ok_U0 {r V m K0 ℓ n : ℕ} (hr : r + 1 ≤ 2 ^ 19000) (h : EdgeReq r V m K0 ℓ n) : Ub r n ≤ V :=
  le_trans (Ub_le_two_pow r n hr) h.hset

end ECDLP.L72
#print axioms ECDLP.L72.ok_U0
