import ECDLP.L44_Sys
import Mathlib.Tactic.DeriveFintype

/-!
# L44 / Forms: slots, constants, quadratic forms of L30's integer system

Slots: the variables of `IntAssign` (`Var`), their slack slots `sl`, `u_i`, the sign slack `tg_i`, and pinned
constants (`Cst`).  Forms are written as lists of triples `(ε, l, r)`.
-/
noncomputable section
namespace ECDLP.L44
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38

/-- value of a form on an integer valuation -/
def HVz {ι : Type} (F : Form ι) (W : ι → ℤ) : ℤ := ∑ t : Fin F.n, F.ε t * (W (F.l t) * W (F.r t))

theorem HV_eq_HVz {ι : Type} [Fintype ι] [DecidableEq ι] (F : Form ι) (V : ι → ℕ) :
    HV F V = HVz F (fun i => (V i : ℤ)) := rfl

/-- form from a list of terms -/
def mkF {ι : Type} (L : List (ℤ × ι × ι)) : Form ι where
  n := L.length
  l i := (L.get i).2.1
  r i := (L.get i).2.2
  ε i := (L.get i).1

theorem HVz_mkF {ι : Type} (L : List (ℤ × ι × ι)) (W : ι → ℤ) :
    HVz (mkF L) W = (L.map fun e => e.1 * (W e.2.1 * W e.2.2)).sum := by
  induction L with
  | nil =>
    refine (Finset.sum_eq_zero fun t _ => absurd t.2 (by simp [mkF])).trans ?_
    simp
  | cons a L ih =>
    unfold HVz at ih ⊢
    simp only [mkF] at ih ⊢
    refine (Fin.sum_univ_succ (n := L.length) _).trans ?_
    have h1 : ∀ i : Fin L.length, (a :: L).get i.succ = L.get i := fun i => rfl
    simp only [h1, List.map_cons, List.sum_cons]
    exact congrArg₂ (· + ·) rfl ih

theorem mass_mkF {ι : Type} (L : List (ℤ × ι × ι)) :
    (mkF L).mass = (L.map fun e => e.1.natAbs).sum := by
  induction L with
  | nil =>
    refine (Finset.sum_eq_zero fun t _ => absurd t.2 (by simp [mkF])).trans ?_
    simp
  | cons a L ih =>
    unfold Form.mass at ih ⊢
    simp only [mkF] at ih ⊢
    refine (Fin.sum_univ_succ (n := L.length) _).trans ?_
    have h1 : ∀ i : Fin L.length, (a :: L).get i.succ = L.get i := fun i => rfl
    simp only [h1, List.map_cons, List.sum_cons]
    exact congrArg₂ (· + ·) rfl ih

/-- variables of `IntAssign` -/
inductive Var (n : ℕ)
  | x (i : Fin (n + 1)) | y (i : Fin (n + 1)) | sx (i : Fin (n + 1)) | sy (i : Fin (n + 1))
  | w (k : Fin n) | l (k : Fin n) | qc (i : Fin (n + 1))
  | q0 (k : Fin n) | q1 (k : Fin n) | q2 (k : Fin n) | q3 (k : Fin n)
  deriving DecidableEq, Fintype

/-- pinned constants -/
inductive Cst
  | one | cp | ca | cb | cOp | cX | cN | cRx | cRy | cc0 | cc1
  deriving DecidableEq

instance : Fintype Cst :=
  ⟨⟨↑[Cst.one, .cp, .ca, .cb, .cOp, .cX, .cN, .cRx, .cRy, .cc0, .cc1], by decide⟩,
    fun x => by cases x <;> simp⟩

/-- slots of the packed network -/
inductive Slot (n : ℕ)
  | v (a : Var n)          -- the variable
  | sl (a : Var n)         -- its range slack: `bound - 1 - v`
  | u (i : Fin (n + 1))    -- `x_i²`
  | tg (i : Fin (n + 1))   -- sign slack
  | cst (c : Cst)          -- constant
  deriving DecidableEq, Fintype

/-- the parameters of the instance -/
structure Inst where
  p : ℕ
  a : ℤ
  b : ℤ
  X : ℕ
  O : ℤ
  N : ℤ
  R : ℤ × ℤ

namespace Inst
variable (I : Inst)

/-- value of a constant -/
def cv : Cst → ℤ
  | .one => 1 | .cp => I.p | .ca => I.a | .cb => I.b | .cOp => I.O * I.p | .cX => I.X | .cN => I.N
  | .cRx => I.R.1 | .cRy => I.R.2 | .cc0 => (((I.p - 1) / 2 : ℕ) : ℤ) | .cc1 => (((I.p - 1) / 2 : ℕ) : ℤ) + 1

@[simp] theorem cv_one : I.cv .one = 1 := rfl
@[simp] theorem cv_cp : I.cv .cp = I.p := rfl
@[simp] theorem cv_ca : I.cv .ca = I.a := rfl
@[simp] theorem cv_cb : I.cv .cb = I.b := rfl
@[simp] theorem cv_cOp : I.cv .cOp = I.O * I.p := rfl
@[simp] theorem cv_cX : I.cv .cX = I.X := rfl
@[simp] theorem cv_cN : I.cv .cN = I.N := rfl
@[simp] theorem cv_cRx : I.cv .cRx = I.R.1 := rfl
@[simp] theorem cv_cRy : I.cv .cRy = I.R.2 := rfl
@[simp] theorem cv_cc0 : I.cv .cc0 = (((I.p - 1) / 2 : ℕ) : ℤ) := rfl
@[simp] theorem cv_cc1 : I.cv .cc1 = (((I.p - 1) / 2 : ℕ) : ℤ) + 1 := rfl

end Inst

variable {n : ℕ}

/-- the constant bounding a variable -/
def bnd : Var n → Cst
  | .x _ => .cX | .y _ => .cp | .sx _ => .cp | .sy _ => .cp | .w _ => .cp | .l _ => .cp
  | .qc _ => .cN | .q0 _ => .cN | .q1 _ => .cN | .q2 _ => .cN | .q3 _ => .cN

/-- sign requirement on a point's `y` -/
inductive Sg | none | pos | neg   -- `pos`: `y > (p-1)/2`;  `neg`: `y ≤ (p-1)/2`
  deriving DecidableEq

/-- index of the identities -/
inductive Cn (n : ℕ)
  | rng (a : Var n) | uEq (i : Fin (n + 1)) | curve (i : Fin (n + 1))
  | s0x | s0y | sRx | sRy
  | e0 (k : Fin n) | e1 (k : Fin n) | e2 (k : Fin n) | e3 (k : Fin n)
  | sign (i : Fin (n + 1))
  deriving DecidableEq, Fintype

open Slot Cst

abbrev T (n : ℕ) := List (ℤ × Slot n × Slot n)

/-- the identity `E + O p - q p = 0` tail -/
def tailT (q : Slot n) : T n := [(1, cst cOp, cst one), (-1, q, cst cp)]

/-- the identities. `sg i` is the sign requirement of point `i`. -/
def formL (sg : Fin (n + 1) → Sg) : Cn n → T n
  | .rng a => [(1, v a, cst one), (1, sl a, cst one), (1, cst one, cst one), (-1, cst (bnd a), cst one)]
  | .uEq i => [(1, u i, cst one), (-1, v (.x i), v (.x i))]
  | .curve i => [(1, v (.y i), v (.y i)), (-1, u i, v (.x i)), (-1, cst ca, v (.x i)), (-1, cst cb, cst one)]
      ++ tailT (v (.qc i))
  | .s0x => [(1, v (.sx 0), cst one), (-1, v (.x 0), cst one)]
  | .s0y => [(1, v (.sy 0), cst one), (-1, v (.y 0), cst one)]
  | .sRx => [(1, v (.sx (Fin.last n)), cst one), (-1, cst cRx, cst one)]
  | .sRy => [(1, v (.sy (Fin.last n)), cst one), (-1, cst cRy, cst one)]
  | .e0 j => [(1, v (.w j), v (.x j.succ)), (-1, v (.w j), v (.sx j.castSucc)), (-1, cst one, cst one)]
      ++ tailT (v (.q0 j))
  | .e1 j => [(1, v (.l j), v (.x j.succ)), (-1, v (.l j), v (.sx j.castSucc)), (-1, v (.y j.succ), cst one),
      (1, v (.sy j.castSucc), cst one)] ++ tailT (v (.q1 j))
  | .e2 j => [(1, v (.l j), v (.l j)), (-1, v (.sx j.castSucc), cst one), (-1, v (.x j.succ), cst one),
      (-1, v (.sx j.succ), cst one)] ++ tailT (v (.q2 j))
  | .e3 j => [(1, v (.l j), v (.sx j.castSucc)), (-1, v (.l j), v (.sx j.succ)), (-1, v (.sy j.succ), cst one),
      (-1, v (.sy j.castSucc), cst one)] ++ tailT (v (.q3 j))
  | .sign i => match sg i with
      | .none => []
      | .pos => [(1, v (.y i), cst one), (-1, cst cc1, cst one), (-1, tg i, cst one)]
      | .neg => [(1, v (.y i), cst one), (1, tg i, cst one), (-1, cst cc0, cst one)]

def formF (sg : Fin (n + 1) → Sg) (c : Cn n) : Form (Slot n) := mkF (formL sg c)

theorem mass_le (sg : Fin (n + 1) → Sg) (c : Cn n) : (formF sg c).mass ≤ 6 := by
  unfold formF
  rw [mass_mkF]
  cases c <;> simp [formL, tailT] <;> (try split) <;> simp

end ECDLP.L44
end
