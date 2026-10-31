import ECDLP.L63_Local

/-!
# L63 / Cost: size and evaluation cost (`τ`) of the bit-reading expressions
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51

/-- number of nodes of an expression -/
def sz : Ex → ℕ
  | .lit _ => 1
  | .var _ => 1
  | .rd _ i => sz i + 1
  | .add e f => sz e + sz f + 1
  | .sub e f => sz e + sz f + 1
  | .mul e f => sz e + sz f + 1
  | .div e f => sz e + sz f + 1
  | .mod e f => sz e + sz f + 1
  | .ifLt e f u v => sz e + sz f + sz u + sz v + 1
  | .lett _ e b => sz e + sz b + 1
  | .sum _ n m b => sz n + sz m + sz b + 1
  | .prod _ n m b => sz n + sz m + sz b + 1
  | .blk _ e => sz e + 1
  | .iter _ _ n i b => sz n + sz i + sz b + 1

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem cost_numBitW (w t : ℕ) (i : Ex) : cost σ A (numBitW w t i) ≤ 2 * cost σ A i + 40 := by
  simp only [numBitW, bitRd, cost, eval]
  by_cases h : eval σ A i < σ w <;> by_cases h2 : 0 < A t (eval σ A i + 1) <;> simp [h, h2] <;> omega

theorem cost_c0B_var (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (x : ℕ) : cost σ A (c0B (.var x)) ≤ 80 := by
  have := cost_numBitW (σ := σ) (A := A) 0 0 (.add (.var x) (.lit 1))
  simp only [c0B, numBit]
  refine this.trans ?_
  simp [cost, eval]

theorem sz_numBitW (w t : ℕ) (i : Ex) : sz (numBitW w t i) = 2 * sz i + 10 := by
  simp only [numBitW, bitRd, sz]; omega

theorem eval_numBitW_le (w t : ℕ) (i : Ex) : eval σ A (numBitW w t i) ≤ 1 := by
  rw [eval_numBitW]; cases (numCells (A t) 1 (σ w)).testBit _ <;> simp

theorem foldProd_two_le (f : ℕ → ℕ) (j : ℕ) : foldProd f 2 j ≤ 1 := by
  cases j with
  | zero => simp [foldProd]
  | succ j => rw [foldProd]; omega

/-- **τ of a constant bit**: the cost of `cvBitE c (var x)` is `≤ 130 σ x + 300`. -/
theorem cost_cvBitE_var (c : Cst) (x : ℕ) : cost σ A (cvBitE c (.var x)) ≤ 130 * σ x + 300 := by
  have h1 := cost_numBitW (σ := σ) (A := A) 0 0 (.var x)
  have h2 := cost_c0B_var σ A x
  have e1 : ∀ w t : ℕ, cost σ A (numBitW w t (.var x)) ≤ 42 := fun w t => by
    have := cost_numBitW (σ := σ) (A := A) w t (.var x); simp only [cost] at this; omega
  cases c with
  | one =>
    by_cases h : σ x < 1 <;> simp [cvBitE, cost, eval, h] <;> omega
  | cp => exact (e1 0 0).trans (by omega)
  | ca => exact (e1 0 1).trans (by omega)
  | cb => exact (e1 0 2).trans (by omega)
  | cX => exact (e1 0 3).trans (by omega)
  | cRx => exact (e1 0 4).trans (by omega)
  | cRy => exact (e1 0 5).trans (by omega)
  | cOp => exact (e1 4 7).trans (by omega)
  | cN =>
    have h3 := cost_numBitW (σ := σ) (A := A) 0 0 (.sub (.var x) (.lit 2))
    simp only [cost, eval] at h3
    by_cases h : σ x < 1 <;> by_cases h' : σ x < 2 <;> simp [cvBitE, cost, eval, h, h', numBit] <;> omega
  | cc0 => exact h2.trans (by omega)
  | cc1 =>
    simp only [cvBitE, cost, eval]
    have hF := foldProd_two_le (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) (σ x)
    have hE : eval σ A (c0B (.var x)) ≤ 1 := eval_numBitW_le 0 0 _
    have key : ∀ j ∈ range (σ x), (cost (Function.update σ 7 j) A (c0B (.var 7)) +
        eval (Function.update σ 7 j) A (c0B (.var 7)) *
          (2 * foldProd (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) 2 j + 6) +
        7 * (foldProd (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) 2 j *
          eval (Function.update σ 7 j) A (c0B (.var 7))) + 30) ≤ 125 := by
      intro j _
      have a1 := cost_c0B_var (Function.update σ 7 j) A 7
      have a2 : eval (Function.update σ 7 j) A (c0B (.var 7)) ≤ 1 := eval_numBitW_le 0 0 _
      have a3 := foldProd_two_le (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) j
      have a4 : eval (Function.update σ 7 j) A (c0B (.var 7)) *
          (2 * foldProd (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) 2 j + 6) ≤ 8 := by
        calc _ ≤ 1 * (2 * 1 + 6) := Nat.mul_le_mul a2 (by omega)
          _ = 8 := rfl
      have a5 : foldProd (fun i => eval (Function.update σ 7 i) A (c0B (.var 7))) 2 j *
          eval (Function.update σ 7 j) A (c0B (.var 7)) ≤ 1 := by
        calc _ ≤ 1 * 1 := Nat.mul_le_mul a3 a2
          _ = 1 := rfl
      omega
    have hs := Finset.sum_le_card_nsmul _ _ 125 key
    simp only [card_range, smul_eq_mul] at hs
    omega

theorem ite_one' (c : Prop) [Decidable c] : (if c then (1 : ℕ) else 1) = 1 := ite_self 1

/-- **τ of a prefix constraint**: with all of `σ x, σ y, σ 2` at most `V`, each of `xcDefE`, `xcBitE`, `sgE`
costs `≤ 200 (V+1)²`. -/
theorem cost_prefix_var {x y V : ℕ} (hx : σ x ≤ V) (hy : σ y ≤ V) (h2 : σ 2 ≤ V) :
    cost σ A (xcDefE (.var x) (.var y)) ≤ 200 * (V + 1) ^ 2 ∧
    cost σ A (xcBitE (.var x) (.var y)) ≤ 200 * (V + 1) ^ 2 ∧
    cost σ A (sgE (.var x)) ≤ 200 * (V + 1) ^ 2 := by
  have m1 : (σ 2 + 1) * (2 * σ x + 6) ≤ (V + 1) * (2 * V + 6) := Nat.mul_le_mul (by omega) (by omega)
  have m2 : (V + 1) * (2 * V + 6) ≤ 6 * (V + 1) ^ 2 := by nlinarith
  have sq : V + 1 ≤ (V + 1) ^ 2 := by nlinarith
  have sq1 : 1 ≤ (V + 1) ^ 2 := by nlinarith
  have s3 : σ 2 - (σ y + 1) ≤ V := by omega
  refine ⟨?_, ?_, ?_⟩
  · by_cases a : σ y < σ 2 <;> by_cases b : σ x * (σ 2 + 1) + (σ 2 - (σ y + 1)) < σ 1 <;>
      simp [xcDefE, pfDef, pidx, qOf, cost, eval, a, b] <;> nlinarith
  · by_cases hA : 0 < A 6 (σ x * (σ 2 + 1) + (σ 2 - (σ y + 1)) + 1) <;>
      simp [xcBitE, pfBit, pidx, qOf, bitRd, cost, eval, hA] <;> nlinarith
  · by_cases hA : 0 < A 6 (σ x * (σ 2 + 1) + σ 2 + 1) <;> by_cases b : σ x * (σ 2 + 1) + σ 2 < σ 1 <;>
      simp [sgE, pidx, cost, eval, hA, b] <;> nlinarith

/-- **Expression size**: the expressions have constant size (independent of `p`, `L`, `m`). -/
theorem sz_cvBitE_var (c : Cst) (x : ℕ) : sz (cvBitE c (.var x)) ≤ 60 := by
  cases c <;> simp [cvBitE, numBit, numBitW, c0B, bitRd, sz]

theorem sz_prefix_var (x y : ℕ) :
    sz (xcDefE (.var x) (.var y)) ≤ 60 ∧ sz (xcBitE (.var x) (.var y)) ≤ 60 ∧ sz (sgE (.var x)) ≤ 60 := by
  simp [xcDefE, xcBitE, sgE, pfDef, pfBit, pidx, qOf, bitRd, sz]

end ECDLP.L63
end
