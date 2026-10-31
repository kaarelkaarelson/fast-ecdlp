import ECDLP.L38_Gadget

/-!
# L38 / Net: the typed forced network of the gadget
-/
noncomputable section
namespace ECDLP.L38
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 Gate

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] (N : NPar) (F : Form ι)
  (ok : ι → Fin N.A → (Fin N.h → Fin (2 ^ N.b)) → Prop)

/-- incoming carry of CAR gate `j` -/
def cinOf (j : Fin (N.A * N.A)) (m : ∀ q : {q // q ∈ paG N (Gate.car j : Gate ι N.A)}, MsgT N q.1) : ℤ :=
  if h : 0 < j.val then
    decC N (m ⟨Gate.car ⟨j.val - 1, by have := j.2; omega⟩, by simp [paG, h]⟩)
  else 0

/-- coefficient (signed representative) received by CAR gate `j` -/
def cfOf (j : Fin (N.A * N.A)) (m : ∀ q : {q // q ∈ paG N (Gate.car j : Gate ι N.A)}, MsgT N q.1) : ℤ :=
  ((m ⟨Gate.ib ⟨j.val % N.A, Nat.mod_lt _ N.toPar.A_pos⟩, by simp [paG]⟩ :
      Fin N.A → N.Rg) ⟨j.val / N.A, Nat.div_lt_of_lt_mul j.2⟩).valMinAbs

def outG : ∀ g : Gate ι N.A, FreeT N g × (∀ q : {q // q ∈ paG N g}, MsgT N q.1) → MsgT N g
  | .fa _ s => fun z => fun k => N.faMsgS (z.1 : Fin N.h → Fin (2 ^ N.b)) s k
  | .mid k => fun z => fun j₁ => N.midMsg F k
      (fun i => NPar.exA (fun s : Fin N.A =>
        (z.2 ⟨Gate.fa i s, by simp [paG]⟩ : Fin N.A → N.Rg) k)) j₁
  | .ib j₁ => fun z => fun j₂ => ibOut N.A N.ωi N.tInv
      (NPar.exA (fun k : Fin N.A => (z.2 ⟨Gate.mid k, by simp [paG]⟩ : Fin N.A → N.Rg) j₁)) j₂
  | .car j => fun z => encC N ((cinOf N j z.2 + cfOf N j z.2) / 2 ^ N.b)

open Classical in
def WG : ∀ g : Gate ι N.A, FreeT N g × (∀ q : {q // q ∈ paG N g}, MsgT N q.1) → ℤ
  | .car j => fun z => if ((2 ^ N.b : ℤ) ∣ cinOf N j z.2 + cfOf N j z.2) ∧
        (j.val + 1 = N.A * N.A → (cinOf N j z.2 + cfOf N j z.2) / 2 ^ N.b = 0) then 1 else 0
  | .fa i s => fun z => if ok i s (z.1 : Fin N.h → Fin (2 ^ N.b)) then 1 else 0
  | .mid _ => fun _ => 1
  | .ib _ => fun _ => 1

def gadgetNet : TForced ℤ (Gate ι N.A) where
  Free := FreeT N
  fFree := instFreeF N
  dFree := instFreeD N
  Msg := MsgT N
  fMsg := instMsgF N
  iMsg := instMsgI N
  pa := paG N
  rk := rkG N
  hrk := hrkG N
  W := WG N ok
  out := outG N F

theorem WG_01 : ∀ (g : Gate ι N.A) (z), WG N ok g z = 0 ∨ WG N ok g z = 1 := by
  intro g z
  cases g with
  | car j => simp only [WG]; split_ifs <;> simp
  | fa _ _ => simp only [WG]; split_ifs <;> simp
  | mid _ => simp [WG]
  | ib _ => simp [WG]

end
end ECDLP.L38
end
