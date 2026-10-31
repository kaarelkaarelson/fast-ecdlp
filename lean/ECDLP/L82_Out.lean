import ECDLP.L82_Disp
import ECDLP.L73_Asm

/-!
# L82 / Out: the rewritten message-code expression `outEx2` of L73, equal to `outEx` in every state

`outEx2 I X Em Kd` = `decodeE I (u+5) (lett (u+20) dqE (disp2 ..))` where the mid expression `Em` appears raw (unguarded) under the single
combined test.  If `Kd.mid.outE = guardE u Em` (the form produced by L79's `midKindG`), then `outEx2` and L73's `outEx` evaluate
equally in every state and with every array (`eval_outEx2`), so every semantic fact about `outEx` (hout, bounds of values, ...) transfers
verbatim.  `dp_outEx2_le`: exact depth bound.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L82
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L79

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- the rewritten dispatch body -/
def outBody2 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) : Ex :=
  .lett (u + 20) (dqE (u := u)) (disp2 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutX I X))

def outEx2 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) : Ex := decodeE I (u + 5) (outBody2 I X Em Kd)

theorem eval_decodeE_congr (A : ℕ → ℕ → ℕ) (xs : ℕ) (b1 b2 : Ex) (h : ∀ σ, Ex.eval σ A b1 = Ex.eval σ A b2)
    (σ : ℕ → ℕ) : Ex.eval σ A (decodeE I xs b1) = Ex.eval σ A (decodeE I xs b2) := by
  simp only [decodeE, Ex.eval]
  exact h _

/-- **`outEx2` and `outEx` agree in every state** (for every array), when the mid kind is `guardE u Em` -/
theorem eval_outEx2 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) (hmid : Kd.mid.outE = guardE u Em)
    (σ : ℕ → ℕ) : Ex.eval σ A (outEx2 I X Em Kd) = Ex.eval σ A (outEx I X Kd) := by
  unfold outEx2 outEx
  refine eval_decodeE_congr I A _ _ _ (fun σ' => ?_) σ
  simp only [outBody2, outBody, Ex.eval]
  have : outChain I X Kd = chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutX I X) := by
    simp only [outChain, chain0, hmid]
  rw [this, eval_disp2]

/-- depth of the rewritten body -/
theorem dp_outBody2 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) :
    Ex.dp (outBody2 I X Em Kd) =
      max (Ex.dp (dqE (u := u))) (max (max 4 (Ex.dp Em)) (max (max 1 (Ex.dp Kd.fa.outE) + 2)
        (max (Ex.dp Kd.ib.outE) (Ex.dp (carOutX I X)) + 3)) + 1) + 1 := by
  simp only [outBody2, dp_disp2, Ex.dp]

/-- **depth of `outEx2`** when the closed instance expressions have depth `<= dI` -/
theorem dp_outEx2_le (Em : Ex) (Kd : Kinds (w := w) (m := m) X) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (outEx2 I X Em Kd) ≤ max (max (dI + 16) 21) (Ex.dp (outBody2 I X Em Kd) + 15) :=
  dp_decodeE_le I (u + 5) (outBody2 I X Em Kd) h1 h2 h3 h4 h5 h6 h7 h8

theorem dp_dqE : Ex.dp (dqE (u := u)) = 9 := by
  simp [dqE, Ex.dp]

end

section msg
set_option maxHeartbeats 1600000 in
open ECDLP.L64 in
/-- the message-test factor expression `E.l / E.r`: exact depth in terms of the parts -/
theorem dp_msgTest_eq {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {P : ECDLP.L56.PForced (ZMod m) ι'} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
    {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e' : ι' ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u' : ℕ}
    (Xp : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e' u') (cE : Ex) (fr tt : ℕ) (vq x : ℕ) :
    Ex.dp (msgTest (ECDLP.L64.mMsg Xp fr tt) cE vq x) =
      max (max (Ex.dp Xp.parE + 6) (Ex.dp (ECDLP.L64.digE Xp fr tt) + 4)) (max (Ex.dp Xp.outE + 8) (Ex.dp cE + 4)) := by
  have := dpT_pos cE
  have := dpT_pos Xp.parE
  have := dpT_pos Xp.outE
  have := dpT_pos (ECDLP.L64.digE Xp fr tt)
  simp only [msgTest, ifEq, ECDLP.L64.mMsg, ECDLP.L64.par2, pow2, Ex.dp]
  omega
end msg

end ECDLP.L82
end
