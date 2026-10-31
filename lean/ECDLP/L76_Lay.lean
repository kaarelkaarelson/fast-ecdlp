import ECDLP.L63_Main
import ECDLP.L76_Mul

/-!
# L76 / Lay: a layout as a parameter, and L63's read expressions and memory spec for it

`Lay` names every array that L63's bit-reading expressions read and gives the *numbers* `L` (width), `2L+1`, `|π|`, `ℓ` as expressions.
L72's layout `Reads72` (everything in arrays `0..11`, width `σ 0`, `|π|` and `ℓ` stored as bit arrays 9 and 10) is the instance `lay72`
(`L76_Lay2.lean`), with `|π|, ℓ` read by the Horner expression `valE`.  Everything below is L63's `Read/Cv/Pre/Local` with the literal indices
replaced by the fields of `Lay` (the proofs are L63's).
-/
noncomputable section
namespace ECDLP.L76
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 Cst

/-- **A layout**: where L63's bit-reading expressions find the numbers.  Arrays are named by index; the *numbers* `L` (width of
`p,a,b,X,xR,yR`), `2L+1`, `|π|`, `ℓ` are given by expressions (`wE, w2E, piE, ellE`), so a layout may keep them in variables or read them
from bit arrays. -/
structure Lay where
  aP : ℕ
  aA : ℕ
  aB : ℕ
  aX : ℕ
  aR : ℕ
  aY : ℕ
  aPre : ℕ
  aOp : ℕ
  wE : Ex
  w2E : Ex
  piE : Ex
  ellE : Ex
  vb : ℕ

/-- bit `i` of the number in array `t` of width `w` (an expression) -/
def nbitW (w : Ex) (t : ℕ) (i : Ex) : Ex := .ifLt i w (bitRd t (.add i (.lit 1))) (.lit 0)

/-- **The number stored in array `t` (cells `1..w`) as an expression**: Horner scan from the top bit (the partial values never exceed
the final value, so the unary evaluation cost is `w · value`). `x, y` are the two binders of `iter`. -/
def valE (w : Ex) (t : ℕ) (x y : ℕ) : Ex :=
  .iter x y w (.lit 0) (.add (.mul (.var y) (.lit 2)) (nbitW w t (.sub (.sub w (.lit 1)) (.var x))))

variable (Y : Lay)

/-- the bound variable does not affect the width -/
def Lay.Ok : Prop := ∀ (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (i : ℕ), eval (Function.update σ Y.vb i) A Y.wE = eval σ A Y.wE

/-- bit `i` of the number in array `t` of width `wE` -/
def nbit (t : ℕ) (i : Ex) : Ex := nbitW Y.wE t i

/-- bit `i` of `⌊p/2⌋` -/
def c0B (i : Ex) : Ex := nbit Y Y.aP (.add i (.lit 1))

def cvBitE : Cst → Ex → Ex
  | .one, j => .ifLt j (.lit 1) (.lit 1) (.lit 0)
  | .cp, j => nbit Y Y.aP j
  | .ca, j => nbit Y Y.aA j
  | .cb, j => nbit Y Y.aB j
  | .cOp, j => nbitW Y.w2E Y.aOp j
  | .cX, j => nbit Y Y.aX j
  | .cN, j => .ifLt j (.lit 1) (.lit 1) (.ifLt j (.lit 2) (.lit 0) (nbit Y Y.aP (.sub j (.lit 2))))
  | .cRx, j => nbit Y Y.aR j
  | .cRy, j => nbit Y Y.aY j
  | .cc0, j => c0B Y j
  | .cc1, j => .mod (.add (c0B Y j) (.prod Y.vb j (.lit 2) (c0B Y (.var Y.vb)))) (.lit 2)

/-- index of bit `q` of point `i` in the string -/
def pidx (i q : Ex) : Ex := .add (.mul i (.add Y.ellE (.lit 1))) q
def pfDef (k : Ex) : Ex := .ifLt k Y.piE (.lit 1) (.lit 0)
def pfBit (k : Ex) : Ex := bitRd Y.aPre (.add k (.lit 1))
def qOf (jj : Ex) : Ex := .sub Y.ellE (.add jj (.lit 1))
def xcDefE (i jj : Ex) : Ex := .ifLt jj Y.ellE (pfDef Y (pidx Y i (qOf Y jj))) (.lit 0)
def xcBitE (i jj : Ex) : Ex := pfBit Y (pidx Y i (qOf Y jj))
def sgE (i : Ex) : Ex :=
  .ifLt (pidx Y i Y.ellE) Y.piE
    (.ifLt (.lit 0) (.rd Y.aPre (.add (pidx Y i Y.ellE) (.lit 1))) (.lit 1) (.lit 2)) (.lit 0)

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- the instance numbers are the numbers in the arrays -/
structure Reads (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (p a b X xR yR : ℕ) (π : List Bool) (ℓ : ℕ) : Prop where
  hp : numCells (A Y.aP) 1 (eval σ A Y.wE) = p
  ha : numCells (A Y.aA) 1 (eval σ A Y.wE) = a
  hb : numCells (A Y.aB) 1 (eval σ A Y.wE) = b
  hX : numCells (A Y.aX) 1 (eval σ A Y.wE) = X
  hxR : numCells (A Y.aR) 1 (eval σ A Y.wE) = xR
  hyR : numCells (A Y.aY) 1 (eval σ A Y.wE) = yR
  hOp : numCells (A Y.aOp) 1 (eval σ A Y.w2E) = 2 * p * p
  hlen : eval σ A Y.piE = π.length
  hl : eval σ A Y.ellE = ℓ
  hpi : ∀ (q : ℕ) (h : q < π.length), (A Y.aPre (q + 1) ≠ 0 ↔ π[q] = true)

theorem eval_nbitW (w : Ex) (t : ℕ) (i : Ex) :
    eval σ A (nbitW w t i) = ((numCells (A t) 1 (eval σ A w)).testBit (eval σ A i)).toNat := by
  rw [nbitW, eval_ifLt']
  by_cases h : eval σ A i < eval σ A w
  · rw [if_pos h, eval_bitRd, testBit_numCells _ _ _ _ h]
    simp only [eval, Nat.add_comm 1]
    by_cases h' : A t (eval σ A i + 1) = 0 <;> simp [h']
  · rw [if_neg h, Nat.testBit_lt_two_pow (lt_of_lt_of_le (numCells_lt _ _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

/-- **the number in an array, read by an expression** (width in the variable `k`) -/
theorem eval_valE (k t x y : ℕ) (hxk : x ≠ k) (hyk : y ≠ k) (hxy : x ≠ y) :
    eval σ A (valE (.var k) t x y) = numCells (A t) 1 (σ k) := by
  set n := σ k with hn
  have hstep : ∀ j s, j < n → eval (Function.update (Function.update σ x j) y s) A
      (.add (.mul (.var y) (.lit 2)) (nbitW (.var k) t (.sub (.sub (.var k) (.lit 1)) (.var x)))) =
      s * 2 + bt (A t) (n - j) := by
    intro j s hj
    rw [eval, eval, eval_nbitW]
    simp only [eval, Function.update_self, Function.update_of_ne (Ne.symm hxk), Function.update_of_ne (Ne.symm hyk), Function.update_of_ne hxy]
    rw [← hn]
    have e1 : n - 1 - j < n := by omega
    rw [testBit_numCells _ _ _ _ e1]
    have e2 : 1 + (n - 1 - j) = n - j := by omega
    rw [e2]
    unfold bt
    by_cases h : A t (n - j) = 0 <;> simp [h]
  have key : ∀ j, j ≤ n → iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A
      (.add (.mul (.var y) (.lit 2)) (nbitW (.var k) t (.sub (.sub (.var k) (.lit 1)) (.var x))))) 0 j =
      V (A t) n / 2 ^ (n - j) := by
    intro j
    induction j with
    | zero => intro _; simp [iterF, Nat.div_eq_of_lt (V_lt _ _)]
    | succ j ih =>
      intro hj
      rw [iterF, ih (by omega), hstep j _ (by omega), T_step (A t) n j (by omega)]
      ring
  show iterF _ _ (eval σ A (.var k)) = _
  have := key n le_rfl
  simpa [eval, hn] using this

theorem eval_nbit (t : ℕ) (i : Ex) :
    eval σ A (nbit Y t i) = ((numCells (A t) 1 (eval σ A Y.wE)).testBit (eval σ A i)).toNat :=
  eval_nbitW _ t i

theorem eval_c0B {p : ℕ} (hp : numCells (A Y.aP) 1 (eval σ A Y.wE) = p) (k : Ex) :
    eval σ A (c0B Y k) = ((p / 2).testBit (eval σ A k)).toNat := by
  rw [c0B, eval_nbit, hp]
  simp [Nat.testBit_succ, eval]

/-- **The constants are computed from the public bits.** For odd `p`. -/
theorem eval_cvBitE (hY : Y.Ok) {p a b X xR yR : ℕ} {π : List Bool} {ℓ n : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (hX : X = Bd p n) (hodd : p % 2 = 1) (c : Cst) (j : Ex) :
    eval σ A (cvBitE Y c j) = (((instOf p a b xR yR n).cv c).toNat.testBit (eval σ A j)).toNat := by
  cases c with
  | one =>
    simp only [cvBitE, eval, Inst.cv_one]
    rw [show ((1 : ℤ).toNat) = 1 from rfl, ECDLP.L63.testBit_one']
    by_cases h : eval σ A j = 0 <;> simp [h]
  | cp => rw [cvBitE, eval_nbit, hr.hp]; simp [instOf]
  | ca => rw [cvBitE, eval_nbit, hr.ha]; simp [instOf]
  | cb => rw [cvBitE, eval_nbit, hr.hb]; simp [instOf]
  | cX => rw [cvBitE, eval_nbit, hr.hX, hX]; simp [instOf]
  | cRx => rw [cvBitE, eval_nbit, hr.hxR]; simp [instOf]
  | cRy => rw [cvBitE, eval_nbit, hr.hyR]; simp [instOf]
  | cOp =>
    have : ((instOf p a b xR yR n).cv .cOp).toNat = 2 * p * p := by
      have h : (instOf p a b xR yR n).cv .cOp = ((2 * p * p : ℕ) : ℤ) := by simp [instOf]
      rw [h, Int.toNat_natCast]
    rw [this, cvBitE, eval_nbitW, hr.hOp]
  | cN =>
    have : ((instOf p a b xR yR n).cv .cN).toNat = 4 * p + 1 := by simp [instOf]; omega
    rw [this, ECDLP.L63.testBit_four_mul_add_one]
    simp only [cvBitE, eval, eval_nbit, hr.hp]
    by_cases h0 : eval σ A j = 0
    · simp [h0]
    · by_cases h1 : eval σ A j = 1
      · simp [h1]
      · simp [h0, h1, show ¬ eval σ A j < 1 by omega, show ¬ eval σ A j < 2 by omega]
  | cc0 =>
    have : ((instOf p a b xR yR n).cv .cc0).toNat = p / 2 := by simp [instOf]; omega
    rw [this]
    simp only [cvBitE, c0B, eval_nbit, hr.hp, eval]
    rw [Nat.testBit_succ]
  | cc1 =>
    have : ((instOf p a b xR yR n).cv .cc1).toNat = p / 2 + 1 := by simp [instOf]; omega
    rw [this, ECDLP.L63.testBit_succ_one]
    have hvb : ∀ i, eval (Function.update σ Y.vb i) A Y.wE = eval σ A Y.wE := fun i => hY σ A i
    have hb : ∀ i, eval (Function.update σ Y.vb i) A (c0B Y (.var Y.vb)) = 0 ∨
        eval (Function.update σ Y.vb i) A (c0B Y (.var Y.vb)) = 1 := by
      intro i
      rw [c0B, eval_nbit]
      cases (numCells (A Y.aP) 1 (eval (Function.update σ Y.vb i) A Y.wE)).testBit _ <;> simp
    simp only [cvBitE, eval]
    rw [ECDLP.L63.foldProd_bits _ hb, eval_c0B Y hr.hp]
    have hin : ∀ i, eval (Function.update σ Y.vb i) A (c0B Y (.var Y.vb)) = ((p / 2).testBit i).toNat := by
      intro i
      rw [eval_c0B Y (σ := Function.update σ Y.vb i) (A := A) (p := p) (by rw [hvb]; exact hr.hp)]
      simp [eval]
    have hif : (if ∀ i < eval σ A j, eval (Function.update σ Y.vb i) A (c0B Y (.var Y.vb)) = 1 then 1 else 0 : ℕ) =
        (decide (∀ i < eval σ A j, (p / 2).testBit i = true)).toNat := by
      have : (∀ i < eval σ A j, eval (Function.update σ Y.vb i) A (c0B Y (.var Y.vb)) = 1) ↔
          ∀ i < eval σ A j, (p / 2).testBit i = true := by
        refine forall₂_congr fun i _ => ?_
        rw [hin]; cases (p / 2).testBit i <;> decide
      by_cases h : ∀ i < eval σ A j, (p / 2).testBit i = true
      · rw [if_pos (this.2 h), decide_eq_true h]; rfl
      · rw [if_neg ((not_congr this).2 h), decide_eq_false h]; rfl
    rw [hif]
    cases (p / 2).testBit (eval σ A j) <;> cases decide (∀ i < eval σ A j, (p / 2).testBit i = true) <;> simp

end ECDLP.L76
end
