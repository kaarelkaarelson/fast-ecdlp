import ECDLP.L63_Read

/-!
# L63 / Cv: the constants of the network are computed from the bits of the public inputs
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 Cst

/-- bit `i` of `⌊p/2⌋` (`= (p-1)/2` for odd `p`) -/
def c0B (i : Ex) : Ex := numBit 0 (.add i (.lit 1))

/-- bit `j` of the constant `c` of L44 (`j` an expression; `var 7` is used as a bound variable for `cc1`) -/
def cvBitE : Cst → Ex → Ex
  | .one, j => .ifLt j (.lit 1) (.lit 1) (.lit 0)
  | .cp, j => numBit 0 j
  | .ca, j => numBit 1 j
  | .cb, j => numBit 2 j
  | .cOp, j => numBitW 4 7 j
  | .cX, j => numBit 3 j
  | .cN, j => .ifLt j (.lit 1) (.lit 1) (.ifLt j (.lit 2) (.lit 0) (numBit 0 (.sub j (.lit 2))))
  | .cRx, j => numBit 4 j
  | .cRy, j => numBit 5 j
  | .cc0, j => c0B j
  | .cc1, j => .mod (.add (c0B j) (.prod 7 j (.lit 2) (c0B (.var 7)))) (.lit 2)

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem foldProd_bits (f : ℕ → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1) (j : ℕ) :
    foldProd f 2 j = if ∀ i < j, f i = 1 then 1 else 0 := by
  induction j with
  | zero => simp [foldProd]
  | succ j ih =>
    rw [foldProd, ih]
    by_cases h : ∀ i < j, f i = 1
    · rcases hf j with h0 | h1
      · have : ¬ ∀ i < j + 1, f i = 1 := fun H => by have := H j (by omega); omega
        rw [if_pos h, if_neg this, h0]
      · have : ∀ i < j + 1, f i = 1 := fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
          · exact h i h'
          · subst h'; exact h1
        rw [if_pos h, if_pos this, h1]
    · have : ¬ ∀ i < j + 1, f i = 1 := fun H => h fun i hi => H i (by omega)
      rw [if_neg h, if_neg this]; simp

theorem toNat_testBit_eq_iff {v : ℕ} {j : ℕ} {b : Bool} :
    (v.testBit j).toNat = b.toNat ↔ v.testBit j = b := by
  cases h : v.testBit j <;> cases b <;> simp

theorem eval_c0B {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p : ℕ} (hp : numCells (A 0) 1 (σ 0) = p) (k : Ex) :
    eval σ A (c0B k) = ((p / 2).testBit (eval σ A k)).toNat := by
  rw [c0B, eval_numBit, hp]
  simp [Nat.testBit_succ, eval]

/-- **The constants are computed from the public bits.** For odd `p`. -/
theorem eval_cvBitE {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW n : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (hX : X = Bd p n) (hodd : p % 2 = 1) (c : Cst) (j : Ex) :
    eval σ A (cvBitE c j) = (((instOf p a b xR yR n).cv c).toNat.testBit (eval σ A j)).toNat := by
  have e0 : ∀ t, ∀ i : Ex, eval σ A (numBit t i) = ((numCells (A t) 1 (σ 0)).testBit (eval σ A i)).toNat :=
    eval_numBit
  cases c with
  | one =>
    simp only [cvBitE, eval, Inst.cv_one]
    rw [show ((1 : ℤ).toNat) = 1 from rfl, testBit_one']
    by_cases h : eval σ A j = 0 <;> simp [h]
  | cp => rw [cvBitE, e0, hr.hp]; simp [instOf]
  | ca => rw [cvBitE, e0, hr.ha]; simp [instOf]
  | cb => rw [cvBitE, e0, hr.hb]; simp [instOf]
  | cX => rw [cvBitE, e0, hr.hX, hX]; simp [instOf]
  | cRx => rw [cvBitE, e0, hr.hxR]; simp [instOf]
  | cRy => rw [cvBitE, e0, hr.hyR]; simp [instOf]
  | cOp =>
    have : ((instOf p a b xR yR n).cv .cOp).toNat = 2 * p * p := by
      have h : (instOf p a b xR yR n).cv .cOp = ((2 * p * p : ℕ) : ℤ) := by simp [instOf]
      rw [h, Int.toNat_natCast]
    rw [this, cvBitE, eval_numBitW, hr.hOp]
  | cN =>
    have : ((instOf p a b xR yR n).cv .cN).toNat = 4 * p + 1 := by simp [instOf]; omega
    rw [this, testBit_four_mul_add_one]
    simp only [cvBitE, eval, e0, hr.hp]
    by_cases h0 : eval σ A j = 0
    · simp [h0]
    · by_cases h1 : eval σ A j = 1
      · simp [h1]
      · simp [h0, h1, show ¬ eval σ A j < 1 by omega, show ¬ eval σ A j < 2 by omega]
  | cc0 =>
    have : ((instOf p a b xR yR n).cv .cc0).toNat = p / 2 := by simp [instOf]; omega
    rw [this]
    simp only [cvBitE, c0B, e0, hr.hp, eval]
    rw [Nat.testBit_succ]
  | cc1 =>
    have : ((instOf p a b xR yR n).cv .cc1).toNat = p / 2 + 1 := by simp [instOf]; omega
    rw [this, testBit_succ_one]
    have hb : ∀ i, eval (Function.update σ 7 i) A (c0B (.var 7)) = 0 ∨
        eval (Function.update σ 7 i) A (c0B (.var 7)) = 1 := by
      intro i
      rw [c0B, eval_numBit]
      cases (numCells (A 0) 1 (Function.update σ 7 i 0)).testBit _ <;> simp
    simp only [cvBitE, eval]
    rw [foldProd_bits _ hb, eval_c0B hr.hp]
    have hin : ∀ i, eval (Function.update σ 7 i) A (c0B (.var 7)) = ((p / 2).testBit i).toNat := by
      intro i
      rw [eval_c0B (by simpa using hr.hp)]
      simp [eval]
    have hif : (if ∀ i < eval σ A j, eval (Function.update σ 7 i) A (c0B (.var 7)) = 1 then 1 else 0 : ℕ) =
        (decide (∀ i < eval σ A j, (p / 2).testBit i = true)).toNat := by
      have : (∀ i < eval σ A j, eval (Function.update σ 7 i) A (c0B (.var 7)) = 1) ↔
          ∀ i < eval σ A j, (p / 2).testBit i = true := by
        refine forall₂_congr fun i _ => ?_
        rw [hin]; cases (p / 2).testBit i <;> decide
      by_cases h : ∀ i < eval σ A j, (p / 2).testBit i = true
      · rw [if_pos (this.2 h), decide_eq_true h]; rfl
      · rw [if_neg ((not_congr this).2 h), decide_eq_false h]; rfl
    rw [hif]
    cases (p / 2).testBit (eval σ A j) <;> cases decide (∀ i < eval σ A j, (p / 2).testBit i = true) <;> simp

end ECDLP.L63
end
