import ECDLPv2.L115_Long

/-!
# L115 / Poly: the polynomial cost bound of the tail
`tail_le : finB K ((K+1)^2) + (K+1)(2(K+1)+2) + 16 ≤ 2000 (K+4)^5`; hence `≤ 64000 (V+1)^5` when `K + 2 ≤ V`.
-/
set_option linter.unusedVariables false
namespace ECDLP.L115

theorem tail_le' (K a : ℕ) (ha : a = K + 4) : finB K ((K + 1) * (K + 1)) + ((K + 1) * (2 * (K + 1) + 2) + 14) + 2 ≤ 2000 * a ^ 5 := by
  unfold finB
  have h1 : K ≤ a := by omega
  have h3 : K + 3 ≤ a := by omega
  have h4 : (K + 1) * (K + 1) ≤ a ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h5 : (K + 1) * (K + 1) + 1 ≤ a ^ 2 := by subst ha; nlinarith
  have h6 : (K + 3) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h3 2
  have h7 : ((K + 1) * (K + 1) + 1) * (K + 3) ^ 2 ≤ a ^ 4 := by
    calc _ ≤ a ^ 2 * a ^ 2 := Nat.mul_le_mul h5 h6
      _ = a ^ 4 := by ring
  have h8 : K * (200 * (((K + 1) * (K + 1) + 1) * (K + 3) ^ 2) + 7) ≤ a * (200 * a ^ 4 + 7) :=
    Nat.mul_le_mul h1 (by omega)
  have h9 : (K + 1) * (K + 1) * (200 * ((K + 1) * (K + 1) + 1) + 7) ≤ a ^ 2 * (200 * a ^ 2 + 7) :=
    Nat.mul_le_mul h4 (by omega)
  have ha4 : 4 ≤ a := by omega
  have p2 : a ^ 2 ≤ a ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p4 : a ^ 4 ≤ a ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p1 : a ≤ a ^ 5 := by calc a = a ^ 1 := (pow_one a).symm
                                 _ ≤ a ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e1 : a * (200 * a ^ 4 + 7) = 200 * a ^ 5 + 7 * a := by ring
  have e2 : a ^ 2 * (200 * a ^ 2 + 7) = 200 * a ^ 4 + 7 * a ^ 2 := by ring
  have h10 : (K + 1) * (2 * (K + 1) + 2) ≤ 2 * a ^ 2 + 2 * a := by subst ha; nlinarith
  rw [e1] at h8
  rw [e2] at h9
  clear h5 h6 h7 h1 h3
  linarith

theorem tail_le (K : ℕ) : finB K ((K + 1) * (K + 1)) + ((K + 1) * (2 * (K + 1) + 2) + 14) + 2 ≤ 2000 * (K + 4) ^ 5 :=
  tail_le' K (K + 4) rfl

theorem tail_V (K V : ℕ) (h : K + 2 ≤ V) : finB K ((K + 1) * (K + 1)) + ((K + 1) * (2 * (K + 1) + 2) + 14) + 2 ≤ 64000 * (V + 1) ^ 5 := by
  refine le_trans (tail_le K) ?_
  have : (K + 4) ^ 5 ≤ (2 * (V + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  rw [mul_pow] at this
  nlinarith

end ECDLP.L115
