import ECDLP.L89_Bw
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# L89 / Clamp: the source message must be clamped, and the generic repair

L69's `PExB.bout` asks `Bdd V σ A X.outE ∧ eval σ A X.outE + 1 ≤ V` whenever the setting code in slot `u+7` is `≤ V`
(this is what `NBdd.l`/`NBdd.r` give, with `σ v.z ≤ V`).  For a source node L73's `outEx` returns the slot `u+7` itself, so for
`σ (u+7) = V` it returns `V` and `eval + 1 = V + 1 > V`: `bout` (and in fact `NBdd.l`, through `mMsg`) is false for that expression.
Repair: `clampPEx`, which replaces `outE` by `outE % (number of messages of the node in slot u+5)`; semantically
the identity (a message code is `< card Msg`), and `eval + 1 ≤ nm ≤ V`.
-/
noncomputable section
namespace ECDLP.L89
open Factoring.Aux Finset Ex SB ECDLP.L56 ECDLP.L64 UCost ECDLP.L69

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
  {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- the clamped message-code expression -/
def clampE : Ex := .mod X.outE (un1 X (u + 5) X.nmE)

/-- `PEx` with the message code taken modulo the number of messages of the sender -/
def clampPEx (hu : B ≤ u) : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u where
  gE := X.gE
  nfE := X.nfE
  nmE := X.nmE
  wE := X.wE
  parE := X.parE
  outE := clampE X
  wtE := X.wtE
  hg := X.hg
  hnf := X.hnf
  hnm := X.hnm
  hw := X.hw
  hpar := X.hpar
  hout := fun σ₀ hC σ hσ a b z hab ha hb hz => by
    have h1 := X.hout σ₀ hC σ hσ a b z hab ha hb hz
    have h2 : Ex.eval σ A (un1 X (u + 5) X.nmE) = Fintype.card (P.Msg (e.symm a)) := eval_nm X hu hC hσ ha
    simp only [clampE, Ex.eval]
    rw [h1, h2]
    exact Nat.mod_eq_of_lt (E (e.symm a) _).2
  hwt := X.hwt

/-- **NEGATIVE (LEAN).**  If the expression `outE` returns the setting code (as L73's `outEx` does on a source node)
on a state with `σ (u+7) = V`, then `bout`'s conclusion `eval + 1 ≤ V` fails. -/
theorem not_bout_of_src {V : ℕ} {σ : ℕ → ℕ} (h7 : σ (u + 7) = V) (hev : Ex.eval σ A X.outE = σ (u + 7)) :
    ¬ (Ex.eval σ A X.outE + 1 ≤ V) := by
  rw [hev, h7]; omega

variable {V : ℕ}

/-- `PExBw` without `bout` (the data that does not involve the message code) -/
structure PExBw0 (V : ℕ) : Prop where
  hV : 8 ≤ V
  hgV : g ≤ V
  hsN : ∀ a : ℕ, sN P e a ≤ V
  hcV : ∀ a b : Fin g, 2 ^ (toGNetE P E).c (e.symm a) (e.symm b) ≤ V
  hwV : ∀ i, P.w i + 1 ≤ V
  bg : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A X.gE
  bnf : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nfE
  bnm : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nmE
  bw : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.wE
  bpar : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ p c : Fin g, σ (u + 5) = p → σ (u + 6) = c → Bdd V σ A X.parE
  bwt : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ a : Fin g, σ (u + 4) = a → σ (u + 7) ≤ V → Bdd V σ A X.wtE

/-- from `PExBw0` data and the plain bound `Bdd V σ A outE` (edges only) to `PExBw` of the clamped `PEx`. -/
theorem pExBw_clamp (hu : B ≤ u) (H : PExBw0 X V)
    (hout : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, e.symm a ∈ P.pa (e.symm b) → σ (u + 5) = a → σ (u + 6) = b →
      σ (u + 7) ≤ V → Bdd V σ A X.outE) :
    PExBw (clampPEx X hu) V where
  hV := H.hV
  hgV := H.hgV
  hsN := H.hsN
  hcV := H.hcV
  hwV := H.hwV
  bg := H.bg
  bnf := H.bnf
  bnm := H.bnm
  bw := H.bw
  bpar := H.bpar
  bout := fun σ₀ hC σ hσ a b hab ha hb hz => by
    have hnm : Bdd V σ A (un1 X (u + 5) X.nmE) := by
      have g1 : Ag B σ₀ (Function.update σ (u + 4) (σ (u + 5))) := hσ.upd (by omega) _
      refine ⟨show σ (u + 5) ≤ V by rw [ha]; exact le_trans a.2.le H.hgV, ?_⟩
      exact H.bnm σ₀ hC (Function.update σ (u + 4) (Ex.eval σ A (.var (u + 5)))) (by simpa [Ex.eval] using g1) a (by simp [Ex.eval, ha])
    have hev : Ex.eval σ A (un1 X (u + 5) X.nmE) = Fintype.card (P.Msg (e.symm a)) := eval_nm X hu hC hσ ha
    have hle := eval_le_of_Bdd A _ σ hnm
    have hpos : 0 < Fintype.card (P.Msg (e.symm a)) := by
      have := nmN_pos P e a.1
      simpa [nmN, a.2] using this
    show Bdd V σ A (clampE X) ∧ Ex.eval σ A (clampE X) + 1 ≤ V
    refine ⟨⟨hout σ₀ hC σ hσ a b hab ha hb hz, hnm⟩, ?_⟩
    simp only [clampE, Ex.eval]
    have := Nat.mod_lt (Ex.eval σ A X.outE) (show 0 < Ex.eval σ A (un1 X (u + 5) X.nmE) by rw [hev]; exact hpos)
    omega
  bwt := H.bwt

end
end ECDLP.L89
end
