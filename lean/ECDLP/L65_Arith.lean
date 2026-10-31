import ECDLP.L60_Main

/-!
# L65 / Arith: the generic arithmetic behind `NetFamily.Spec` for a family with total bits `U`,
per-cluster overhead `Wm` and setting bits `S`

The top width of the clustered network is `(K U + g P)/K^3` with `P = U/g + Wm` (the label returned by
`edgeNet_good_code`: `(K0 U0 + G P0)/K0^3` with `P0 = U0/G + wmax`).
-/
namespace ECDLP.L65

/-- `g * (u / g) ≤ u` -/
theorem mul_div_le' (g u : ℕ) : g * (u / g) ≤ u := Nat.mul_div_le u g

/-- the top width -/
def ltopOf (U Wm K g : ℕ) : ℕ := (K * U + g * (U / g + Wm)) / K ^ 3

theorem gP_le (U Wm g : ℕ) : g * (U / g + Wm) ≤ U + g * Wm := by
  have := mul_div_le' g U
  rw [Nat.mul_add]; omega

theorem ltop_bound (U Wm K g : ℕ) (hK : 1 ≤ K) : K ^ 2 * ltopOf U Wm K g ≤ 2 * U + g * Wm := by
  unfold ltopOf
  set X := K * U + g * (U / g + Wm) with hX
  have h1 : K ^ 3 * (X / K ^ 3) ≤ X := Nat.mul_div_le X _
  have h2 : K ^ 2 * (X / K ^ 3) ≤ X / K := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc K ^ 2 * (X / K ^ 3) * K = K ^ 3 * (X / K ^ 3) := by ring
      _ ≤ X := h1
  have h3 : X / K ≤ U + g * (U / g + Wm) := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : K * U = U * K := by ring
    have : g * (U / g + Wm) ≤ g * (U / g + Wm) * K := Nat.le_mul_of_pos_right _ (by omega)
    show K * U + g * (U / g + Wm) ≤ _
    nlinarith
  have := gP_le U Wm g
  omega

/-- the exponents of the value bounds (without the polynomial part) -/
def eOf (U Wm S K g : ℕ) : ℕ :=
  S + (U / g + Wm) + (U / g + Wm) * (2 * g / K) + ltopOf U Wm K g * K

theorem eOf_bound (U Wm S K g : ℕ) (hK2 : 2 ≤ K) (hKg : K ≤ g) :
    K * eOf U Wm S K g ≤ 5 * U + K * (S + Wm) + 3 * (g * Wm) := by
  have hg : 0 < g := by omega
  have hl := ltop_bound U Wm K g (by omega)
  have hKU : K * (U / g) ≤ U := le_trans (Nat.mul_le_mul_right _ hKg) (mul_div_le' g U)
  have hP2 : (U / g + Wm) * (2 * g / K) * K ≤ (U / g + Wm) * (2 * g) := by
    calc (U / g + Wm) * (2 * g / K) * K = (U / g + Wm) * ((2 * g / K) * K) := by ring
      _ ≤ (U / g + Wm) * (2 * g) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  have hgP := gP_le U Wm g
  have e0 : K * eOf U Wm S K g = K * S + K * (U / g + Wm) + K * ((U / g + Wm) * (2 * g / K)) +
      K ^ 2 * ltopOf U Wm K g := by unfold eOf; ring
  have e1 : K * ((U / g + Wm) * (2 * g / K)) ≤ 2 * (g * (U / g + Wm)) := by
    calc K * ((U / g + Wm) * (2 * g / K)) = (U / g + Wm) * (2 * g / K) * K := by ring
      _ ≤ (U / g + Wm) * (2 * g) := hP2
      _ = 2 * (g * (U / g + Wm)) := by ring
  have e2 : K * (U / g + Wm) ≤ U + K * Wm := by rw [Nat.mul_add]; omega
  have e3 : K * (S + Wm) = K * S + K * Wm := by ring
  rw [e0]
  omega

end ECDLP.L65
