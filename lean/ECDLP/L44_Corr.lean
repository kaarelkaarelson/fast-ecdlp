import ECDLP.L44_Forms
import ECDLP.L30_Final

/-!
# L44 / Corr: the packed system on integer valuations is exactly L30's `IntOK` plus slack/sign bookkeeping

`Vt t`: the canonical valuation of an `IntAssign` (variables, range slacks `bound-1-v`, `u`, sign slack,
constants).  `corr_fwd`: `IntOK ∧ SignOK` implies all identities vanish on `Vt t`.
`corr_bwd`: a nonnegative valuation with pinned constants on which all identities vanish is `Vt` of
`tOf W`, and `tOf W` satisfies `IntOK` and `SignOK`.
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst

variable {n : ℕ} (I : Inst)

/-- `IntOK` for an instance -/
def IOK (t : IntAssign n) : Prop := IntOK I.p I.a I.b I.X I.O I.N I.R t

def Var.get (t : IntAssign n) : Var n → ℤ
  | .x i => (t.P i).1 | .y i => (t.P i).2 | .sx i => (t.S i).1 | .sy i => (t.S i).2
  | .w k => t.w k | .l k => t.l k | .qc i => t.qc i
  | .q0 k => t.q0 k | .q1 k => t.q1 k | .q2 k => t.q2 k | .q3 k => t.q3 k

def tgv : Sg → ℤ → ℤ
  | .none, _ => 0
  | .pos, y => y - I.cv .cc1
  | .neg, y => I.cv .cc0 - y

def SgP : Sg → ℤ → Prop
  | .none, _ => True
  | .pos, y => I.cv .cc1 ≤ y
  | .neg, y => y ≤ I.cv .cc0

/-- sign requirements hold -/
def SignOK (sg : Fin (n + 1) → Sg) (t : IntAssign n) : Prop := ∀ i, SgP I (sg i) (t.P i).2

/-- canonical valuation -/
def Vt (sg : Fin (n + 1) → Sg) (t : IntAssign n) : Slot n → ℤ
  | .v a => Var.get t a
  | .sl a => I.cv (bnd a) - 1 - Var.get t a
  | .u i => t.u i
  | .tg i => tgv I (sg i) (t.P i).2
  | .cst c => I.cv c

/-- read an `IntAssign` off a valuation -/
def tOf (W : Slot n → ℤ) : IntAssign n where
  P i := (W (.v (.x i)), W (.v (.y i)))
  u i := W (.u i)
  qc i := W (.v (.qc i))
  S i := (W (.v (.sx i)), W (.v (.sy i)))
  w k := W (.v (.w k))
  l k := W (.v (.l k))
  q0 k := W (.v (.q0 k))
  q1 k := W (.v (.q1 k))
  q2 k := W (.v (.q2 k))
  q3 k := W (.v (.q3 k))

theorem tOf_Vt (sg : Fin (n + 1) → Sg) (t : IntAssign n) : tOf (Vt I sg t) = t := by
  cases t; rfl

theorem sum_eval (sg : Fin (n + 1) → Sg) (c : Cn n) (W : Slot n → ℤ) :
    HVz (formF sg c) W = ((formL sg c).map fun e => e.1 * (W e.2.1 * W e.2.2)).sum := HVz_mkF _ _

/-! ### forward -/

theorem corr_fwd (sg : Fin (n + 1) → Sg) (t : IntAssign n) (h : IOK I t) (hs : SignOK I sg t)
    (c : Cn n) : HVz (formF sg c) (Vt I sg t) = 0 := by
  obtain ⟨hr, hu, hc, hS, h0, hlast, hk⟩ := h
  rw [formF, HVz_mkF]
  cases c with
  | rng a => cases a <;> simp [formL, Vt, Var.get, bnd, Inst.cv] <;> ring
  | uEq i => simp [formL, Vt, Var.get, hu i, Inst.cv]
  | curve i =>
    have := (hc i).2.2
    simp [formL, tailT, Vt, Var.get, Inst.cv, hu i] at this ⊢
    linarith
  | s0x => simp [formL, Vt, Var.get, h0]
  | s0y => simp [formL, Vt, Var.get, h0]
  | sRx => simp [formL, Vt, Var.get, hlast, Inst.cv]
  | sRy => simp [formL, Vt, Var.get, hlast, Inst.cv]
  | e0 j =>
    have := (hk j).2.2.1.2.2
    simp [formL, tailT, Vt, Var.get, Inst.cv] at this ⊢
    linarith
  | e1 j =>
    have := (hk j).2.2.2.1.2.2
    simp [formL, tailT, Vt, Var.get, Inst.cv] at this ⊢
    linarith
  | e2 j =>
    have := (hk j).2.2.2.2.1.2.2
    simp [formL, tailT, Vt, Var.get, Inst.cv] at this ⊢
    linarith
  | e3 j =>
    have := (hk j).2.2.2.2.2.2.2
    simp [formL, tailT, Vt, Var.get, Inst.cv] at this ⊢
    linarith
  | sign i =>
    have := hs i
    cases hg : sg i <;> simp [formL, hg, Vt, Var.get, tgv] <;> simp [hg, SgP] at this <;> ring_nf

/-! ### backward -/

theorem Var.get_tOf (W : Slot n → ℤ) (a : Var n) : Var.get (tOf W) a = W (.v a) := by
  cases a <;> rfl

theorem corr_bwd (sg : Fin (n + 1) → Sg) (W : Slot n → ℤ) (hnn : ∀ s, 0 ≤ W s)
    (hk : ∀ c, W (.cst c) = I.cv c) (htg : ∀ i, sg i = .none → W (.tg i) = 0)
    (hz : ∀ c, HVz (formF sg c) W = 0) :
    IOK I (tOf W) ∧ SignOK I sg (tOf W) ∧ W = Vt I sg (tOf W) := by
  have z : ∀ c, ((formL sg c).map fun e => e.1 * (W e.2.1 * W e.2.2)).sum = 0 := fun c => by
    rw [← HVz_mkF]; exact hz c
  have hone : W (.cst .one) = 1 := by rw [hk]; rfl
  have hrng : ∀ a, W (.v a) + W (.sl a) + 1 - I.cv (bnd a) = 0 := by
    intro a
    have := z (.rng a)
    simp [formL, hk] at this
    linarith
  have hv0 : ∀ a, 0 ≤ W (.v a) := fun a => hnn _
  have hv1 : ∀ a, W (.v a) < I.cv (bnd a) := fun a => by
    have := hnn (.sl a); have := hrng a; linarith
  have hX : ∀ i, W (.v (.x i)) < I.X := fun i => by simpa [bnd] using hv1 (.x i)
  have hp : ∀ a : Var n, I.cv (bnd a) = I.p → W (.v a) < I.p := fun a h => by
    have := hv1 a; rw [h] at this; exact this
  have hN : ∀ a : Var n, I.cv (bnd a) = I.N → W (.v a) < I.N := fun a h => by
    have := hv1 a; rw [h] at this; exact this
  have hu : ∀ i, W (.u i) = W (.v (.x i)) * W (.v (.x i)) := fun i => by
    have := z (.uEq i)
    simp [formL, hk] at this
    linarith
  have hcur : ∀ i, W (.v (.y i)) * W (.v (.y i)) - W (.u i) * W (.v (.x i)) - I.a * W (.v (.x i)) - I.b
      + I.O * I.p = W (.v (.qc i)) * I.p := fun i => by
    have := z (.curve i)
    simp [formL, tailT, hk] at this
    linarith
  have hs0x := z .s0x
  have hs0y := z .s0y
  have hsRx := z .sRx
  have hsRy := z .sRy
  simp [formL, hk] at hs0x hs0y hsRx hsRy
  have e0 : ∀ j : Fin n, W (.v (.w j)) * W (.v (.x j.succ)) - W (.v (.w j)) * W (.v (.sx j.castSucc)) - 1
      + I.O * I.p = W (.v (.q0 j)) * I.p := fun j => by
    have := z (.e0 j)
    simp [formL, tailT, hk] at this
    linarith
  have e1 : ∀ j : Fin n, W (.v (.l j)) * W (.v (.x j.succ)) - W (.v (.l j)) * W (.v (.sx j.castSucc))
      - W (.v (.y j.succ)) + W (.v (.sy j.castSucc)) + I.O * I.p = W (.v (.q1 j)) * I.p := fun j => by
    have := z (.e1 j)
    simp [formL, tailT, hk] at this
    linarith
  have e2 : ∀ j : Fin n, W (.v (.l j)) * W (.v (.l j)) - W (.v (.sx j.castSucc)) - W (.v (.x j.succ))
      - W (.v (.sx j.succ)) + I.O * I.p = W (.v (.q2 j)) * I.p := fun j => by
    have := z (.e2 j)
    simp [formL, tailT, hk] at this
    linarith
  have e3 : ∀ j : Fin n, W (.v (.l j)) * W (.v (.sx j.castSucc)) - W (.v (.l j)) * W (.v (.sx j.succ))
      - W (.v (.sy j.succ)) - W (.v (.sy j.castSucc)) + I.O * I.p = W (.v (.q3 j)) * I.p := fun j => by
    have := z (.e3 j)
    simp [formL, tailT, hk] at this
    linarith
  have hsg : ∀ i, SgP I (sg i) (W (.v (.y i))) ∧ W (.tg i) = tgv I (sg i) (W (.v (.y i))) := fun i => by
    have h := z (.sign i)
    have h1 := hnn (.tg i)
    cases hg : sg i
    · simp [SgP, tgv, htg i hg]
    · simp [formL, hg, hk] at h
      simp [SgP, tgv]
      constructor <;> linarith
    · simp [formL, hg, hk] at h
      simp [SgP, tgv]
      constructor <;> linarith
  have hQ : ∀ (a q : Var n), W (.v q) * I.p = W (.v q) * I.p → True := fun _ _ _ => trivial
  have hIOK : IOK I (tOf W) := by
    refine ⟨fun i => ⟨hv0 (.x i), hX i, hv0 (.y i), hp (.y i) rfl⟩, hu, fun i => ?_, fun i => ?_, ?_, ?_, fun j => ?_⟩
    · exact ⟨hv0 (.qc i), hN (.qc i) rfl, by simpa [tOf, hu i] using hcur i⟩
    · exact ⟨hv0 (.sx i), hp (.sx i) rfl, hv0 (.sy i), hp (.sy i) rfl⟩
    · refine Prod.ext ?_ ?_
      · simp [tOf]; linarith
      · simp [tOf]; linarith
    · refine Prod.ext ?_ ?_
      · simp [tOf]; linarith
      · simp [tOf]; linarith
    · exact ⟨⟨hv0 (.w j), hp (.w j) rfl⟩, ⟨hv0 (.l j), hp (.l j) rfl⟩,
        ⟨hv0 (.q0 j), hN (.q0 j) rfl, by simp only [tOf]; linear_combination e0 j⟩,
        ⟨hv0 (.q1 j), hN (.q1 j) rfl, by simp only [tOf]; linear_combination e1 j⟩,
        ⟨hv0 (.q2 j), hN (.q2 j) rfl, by simp only [tOf]; linear_combination e2 j⟩,
        ⟨hv0 (.q3 j), hN (.q3 j) rfl, by simp only [tOf]; linear_combination e3 j⟩⟩
  refine ⟨hIOK, fun i => (hsg i).1, ?_⟩
  funext s
  cases s with
  | v a => simp [Vt, Var.get_tOf]
  | sl a => simp only [Vt, Var.get_tOf]; have := hrng a; linarith
  | u i => rfl
  | tg i => exact (hsg i).2
  | cst c => exact hk c

end ECDLP.L44
end
