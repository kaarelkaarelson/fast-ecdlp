import ECDLP.L75_IbB

/-!
# L75 / Ib2: the `ib` message with a LOG-FREE inverse: `tInv = q - 2^M / A^2`

`Par.tInv = 2^((2M-1)(k+1))` needs `k` as a slot.  Since `2^M = -1` and `A*A = 2^(k+1) <= 2^M`, the inverse of `A*A`
in `Z/(2^M+1)` is `-(2^M / (A*A))`; so `tInv.val = (2^M + 1) - 2^M / (A*A)` (`tInv_val`), an expression in the slots
`2^M` and `A` only.  The exponent of the root, `w (2^(k+1) - 1)`, is `(M / (A h)) (A A - 1)` (slot `M`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L68 (ibE hatE pwE sumE mulE eval_fv rp_ibOut rp_mul rp_hat Rp)

section arith
variable (P : Par)

theorem tInv_val (hM : P.k + 1 ≤ P.M) :
    (P.tInv).val = (2 ^ P.M + 1) - 2 ^ P.M / (P.A * P.A) := by
  have hAA : P.A * P.A = 2 ^ (P.k + 1) := P.hA
  have hQ : 2 ^ P.M / (P.A * P.A) = 2 ^ (P.M - (P.k + 1)) := by
    rw [hAA, Nat.pow_div hM (by norm_num)]
  have hM1 : 1 ≤ P.M := by omega
  have hQpos : 1 ≤ 2 ^ (P.M - (P.k + 1)) := Nat.one_le_two_pow
  have hQle : 2 ^ (P.M - (P.k + 1)) ≤ 2 ^ P.M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : 2 ^ (P.M - (P.k + 1)) * 2 ^ (P.k + 1) = 2 ^ P.M := by
    rw [← pow_add]; congr 1; omega
  have hq0 : (((2 ^ P.M + 1 : ℕ)) : P.Rg) = 0 := ZMod.natCast_self _
  have hneg := two_pow_eq_neg_one P.M
  have hinv := P.tInv_mul hM1
  have key : P.tInv = -((2 ^ (P.M - (P.k + 1)) : ℕ) : P.Rg) := by
    have h1 : -((2 ^ (P.M - (P.k + 1)) : ℕ) : P.Rg) * ((2 ^ (P.k + 1) : ℕ) : P.Rg) = 1 := by
      rw [neg_mul, ← Nat.cast_mul, hprod]
      push_cast
      rw [hneg]; simp
    calc P.tInv = P.tInv * (-((2 ^ (P.M - (P.k + 1)) : ℕ) : P.Rg) * ((2 ^ (P.k + 1) : ℕ) : P.Rg)) := by
          rw [h1, mul_one]
      _ = -((2 ^ (P.M - (P.k + 1)) : ℕ) : P.Rg) * (P.tInv * ((2 ^ (P.k + 1) : ℕ) : P.Rg)) := by ring
      _ = _ := by rw [hinv, mul_one]
  rw [hQ, key]
  have : -((2 ^ (P.M - (P.k + 1)) : ℕ) : P.Rg) = (((2 ^ P.M + 1 - 2 ^ (P.M - (P.k + 1)) : ℕ)) : P.Rg) := by
    rw [Nat.cast_sub (by omega), hq0]; ring
  rw [this, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

end arith

section rp
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vq : ℕ}

/-- `ibE` with the inverse given as an expression `tE` -/
def ibE2 (vq vA x1 : ℕ) (e0 tE k u : Ex) : Ex := mulE vq tE (hatE vq vA x1 e0 k u)

theorem rp_ibOut2 (N : NPar) (hM : 1 ≤ N.M) {vq vA x1 : ℕ} (hq : σ vq = 2 ^ N.M + 1) (hvq : vq < x1) (hvA : vA < x1)
    (hA : σ vA = N.A) {e0 tE k u : Ex} (h0 : Ex.FV (· < x1) e0) (hk : Ex.FV (· < x1) k)
    (hE : Ex.eval σ A e0 = N.w * (2 ^ (N.k + 1) - 1)) (hT : Ex.eval σ A tE = N.tInv.val)
    {j : ℕ} (hK : Ex.eval σ A k = j) (Z : ℕ → N.Rg)
    (hu : ∀ i < N.A, Rp (Function.update σ x1 i) A u (Z i)) :
    Rp σ A (ibE2 vq vA x1 e0 tE k u) (ibOut N.A N.ωi N.tInv Z j) := by
  have hq2 := ECDLP.L68.q_gt N hM
  have h1 := rp_hat (q := 2 ^ N.M + 1) (A := A) hq hq2 hvq hvA hA h0 hk
    (E := N.w * (2 ^ (N.k + 1) - 1)) hE hK Z hu
  have h2 : Rp σ A tE N.tInv := hT
  have := rp_mul hq h2 h1
  have e1 : N.ωi = (2 : ZMod (2 ^ N.M + 1)) ^ (N.w * (2 ^ (N.k + 1) - 1)) := by
    unfold Par.ωi Par.ω; rw [pow_mul]
  unfold ibOut
  rw [e1]
  exact this

end rp
end ECDLP.L75
end
