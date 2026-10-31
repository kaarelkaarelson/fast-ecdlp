import ECDLP.L44_Str
import ECDLP.L51_Net
import FactoringAux.EngineIn

/-!
# L63 / Read: the instance data as public inputs of the engine, and bit-reading expressions

Layout (analogue of `Ex.nBit`, Rudich `EngineIn.lean`): `σ 0 = L` (bits per number), `σ 1 = |π|`, `σ 2 = ℓ`,
`σ 3 = bW` (the width of a pinned constant), `σ 4 = 2L+1`; arrays `0..5` hold the bits of `p, a, b, X, xR, yR`
(little endian, cells `1..L`, nonzero = 1), array `7` (width `σ 4`) the bits of `2p²` (the constant `O·p`; a product,
so it is a public input computed by the driver), array `6` holds the prefix (cell `q+1` nonzero iff `π[q] = true`).
`X = Bd p n = ⌈p^{1/m}⌉` is a public input too (it is a function of `p, m`, computed by the driver in
polynomial time; an expression cannot compute it because values cost unary time).

* `numBit t i`: bit `i` of the number in array `t`;
* `cvBitE c j`: bit `j` of L44's constant `I.cv c` (`I = instOf p a b xR yR n`);
* `xcDefE`, `xcBitE`: the `x`-bit constraints of the prefix (`xcOf`);  `sgE`: the sign code (`sgOf`).
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51

/-- bit `i` of the number in array `t` (cells `1 … σ 0`) -/
def numBitW (w t : ℕ) (i : Ex) : Ex := .ifLt i (.var w) (bitRd t (.add i (.lit 1))) (.lit 0)

/-- bit `i` of the number in array `t` of width `σ 0` -/
def numBit (t : ℕ) (i : Ex) : Ex := numBitW 0 t i

theorem numBit_zero (i : Ex) : numBit 0 i = nBit i := rfl

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_numBitW (w t : ℕ) (i : Ex) :
    eval σ A (numBitW w t i) = ((numCells (A t) 1 (σ w)).testBit (eval σ A i)).toNat := by
  rw [numBitW, eval_ifLt', show eval σ A (.var w) = σ w from rfl]
  by_cases h : eval σ A i < σ w
  · rw [if_pos h, eval_bitRd, testBit_numCells _ _ _ _ h]
    simp only [eval, Nat.add_comm 1]
    by_cases h' : A t (eval σ A i + 1) = 0 <;> simp [h']
  · rw [if_neg h, Nat.testBit_lt_two_pow (lt_of_lt_of_le (numCells_lt _ _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

theorem eval_numBit (t : ℕ) (i : Ex) :
    eval σ A (numBit t i) = ((numCells (A t) 1 (σ 0)).testBit (eval σ A i)).toNat := eval_numBitW 0 t i

/-- the instance data are the numbers in the arrays -/
structure Reads (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (p a b X xR yR : ℕ) (π : List Bool) (ℓ bW : ℕ) : Prop where
  hp : numCells (A 0) 1 (σ 0) = p
  ha : numCells (A 1) 1 (σ 0) = a
  hb : numCells (A 2) 1 (σ 0) = b
  hX : numCells (A 3) 1 (σ 0) = X
  hxR : numCells (A 4) 1 (σ 0) = xR
  hyR : numCells (A 5) 1 (σ 0) = yR
  hOp : numCells (A 7) 1 (σ 4) = 2 * p * p
  hlen : σ 1 = π.length
  hl : σ 2 = ℓ
  hbW : σ 3 = bW
  hpi : ∀ (q : ℕ) (h : q < π.length), (A 6 (q + 1) ≠ 0 ↔ π[q] = true)

/-! ## bit lemmas -/

theorem testBit_one' (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  cases j with
  | zero => simp
  | succ j => rw [Nat.testBit_succ]; simp

theorem testBit_two_mul' (p j : ℕ) :
    (2 * p).testBit j = if j = 0 then false else p.testBit (j - 1) := by
  cases j with
  | zero => simp [Nat.testBit_zero]
  | succ j => rw [Nat.testBit_succ]; simp [Nat.mul_div_cancel_left]

theorem testBit_four_mul_add_one (p j : ℕ) :
    (4 * p + 1).testBit j = if j = 0 then true else if j = 1 then false else p.testBit (j - 2) := by
  rcases j with _ | _ | j
  · simp [Nat.testBit_zero]; omega
  · rw [Nat.testBit_succ]; simp [Nat.testBit_zero]; omega
  · rw [Nat.testBit_succ, Nat.testBit_succ]
    have : (4 * p + 1) / 2 / 2 = p := by omega
    rw [this]; simp

theorem testBit_succ_one (c j : ℕ) :
    (c + 1).testBit j = xor (c.testBit j) (decide (∀ i < j, c.testBit i = true)) := by
  induction j generalizing c with
  | zero =>
    rw [Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · have : (c + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (c + 1) % 2 ≠ 1 := by omega
      simp [h, this]
  | succ j ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · have e : (c + 1) / 2 = c / 2 := by omega
      rw [e]
      have : ¬ (∀ i < j + 1, c.testBit i = true) := fun H => by
        have := H 0 (by omega); rw [Nat.testBit_zero] at this; simp at this; omega
      rw [decide_eq_false this, Bool.xor_false]
    · have e : (c + 1) / 2 = c / 2 + 1 := by omega
      rw [e, ih]
      congr 1
      refine decide_eq_decide.mpr ?_
      constructor
      · intro H i hi
        rcases i with _ | i
        · rw [Nat.testBit_zero]; simp; omega
        · rw [Nat.testBit_succ]; exact H i (by omega)
      · intro H i hi
        have := H (i + 1) (by omega)
        rwa [Nat.testBit_succ] at this

end ECDLP.L63
end
