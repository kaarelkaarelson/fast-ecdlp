import ECDLP.L80_BW

/-!
# L80 / BWle: `bWof L <= 3 L + 3` for `L >= 2` (so the pinned width always fits in `len >= L + 2` bits)
-/
namespace ECDLP.L80
open ECDLP.L59

theorem DP_le (L : ℕ) (hL : 2 ≤ L) : DP L ≤ L := by
  unfold DP kP jm1
  set T := (Nat.log 2 L + 2) / 4 with hT
  rcases Nat.lt_or_ge 1 T with h | h
  · have h1 : 4 * 16 ^ (T - 1) ≤ L := (T_iff L (T - 1) (by omega)).2 (by omega)
    calc 2 ^ (2 * (T - 1) + 1) ≤ 2 ^ (4 * (T - 1) + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 16 ^ (T - 1) := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ L := h1
  · have : 2 * (T - 1) + 1 = 1 := by omega
    rw [this]; omega

theorem bWof_le (L : ℕ) (hL : 2 ≤ L) : ECDLP.L72.bWof L ≤ 3 * L + 3 := by
  unfold ECDLP.L72.bWof
  show bP L * 2 ^ kP L ≤ _
  have hD := DP_le L hL
  have e : 2 ^ kP L = DP L := rfl
  rw [e]
  unfold bP
  have h1 : Bits L / DP L * DP L ≤ Bits L := Nat.div_mul_le_self _ _
  unfold Bits at h1 ⊢
  nlinarith [h1, hD, Nat.add_mul (Bits L / DP L) 1 (DP L)]

theorem three_lt_pow (L : ℕ) (hL : 2 ≤ L) : 3 * L + 3 < 2 ^ (L + 2) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih => rw [pow_succ]; omega

end ECDLP.L80
