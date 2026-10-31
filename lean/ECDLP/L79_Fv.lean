import ECDLP.L79_Depth

/-!
# L79 / Fv: free variables of the structural expressions of the dispatch (`nfEx`, `nmEx`, `parEx`)

L74's `midKind` asks `Ex.FV (· < u + 10)` of `X.nfE`, `X.nmE`, `X.parE` (they are evaluated inside the kind expression after the node
slots have been rebound, so they must not read any scratch slot `>= u + 10`).  For `pex0` these are `decodeE`-expressions; their
free variables are those of the instance expressions (`InstEx`) and of `phiE`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)

/-- the instance expressions read nothing of the scratch region `>= u + 10` (the two per-identity ones may read `u + 22 = c`) -/
structure InstFV : Prop where
  hA : Ex.FV (· < u + 10) I.AE
  hh : Ex.FV (· < u + 10) I.hE
  hpb : Ex.FV (· < u + 10) I.pbE
  hnI : Ex.FV (· < u + 10) I.nIE
  hK : Ex.FV (· < u + 10) I.KE
  hb : Ex.FV (· < u + 10) I.bE
  hnc : Ex.FV (fun y => y < u + 10 ∨ y = u + 22) I.ncE
  hMe : Ex.FV (fun y => y < u + 10 ∨ y = u + 22) I.MeE

/-- the slots a body of the decode may read: below `u+10` or one of the 15 slots written by the decode -/
def decSet (u : ℕ) (y : ℕ) : Prop :=
  ((((((((((((((y < u + 10 ∨ y = u + 12) ∨ y = u + 13) ∨ y = u + 10) ∨ y = u + 24) ∨ y = u + 15) ∨ y = u + 22) ∨ y = u + 19) ∨
    y = u + 27) ∨ y = u + 11) ∨ y = u + 18) ∨ y = u + 25) ∨ y = u + 21) ∨ y = u + 16) ∨ y = u + 17) ∨ y = u + 14

theorem fv_decodeE (hF : InstFV I) {xs : ℕ} (hxs : xs < u + 10) {body : Ex}
    (hbody : Ex.FV (decSet u) body) : Ex.FV (· < u + 10) (decodeE I xs body) := by
  obtain ⟨hA, hh, hpb, hnI, hK, hb, hnc, hMe⟩ := hF
  simp only [decodeE, kcodeE, djE, dsE, offE, blkLoop, nsum, nprod, Ex.FV]
  repeat' first
    | exact Ex.FV_mono (fun y hy => by omega) _ hA
    | exact Ex.FV_mono (fun y hy => by omega) _ hh
    | exact Ex.FV_mono (fun y hy => by omega) _ hpb
    | exact Ex.FV_mono (fun y hy => by omega) _ hnI
    | exact Ex.FV_mono (fun y hy => by omega) _ hK
    | exact Ex.FV_mono (fun y hy => by omega) _ hb
    | exact Ex.FV_mono (fun y hy => by omega) _ hnc
    | exact Ex.FV_mono (fun y hy => by omega) _ hMe
    | exact hbody
    | trivial
    | omega
    | (simp; done)
    | apply And.intro
  done

theorem fv_nfEx (hF : InstFV I) : Ex.FV (· < u + 10) (nfEx I) := by
  unfold nfEx
  refine fv_decodeE I hF (by omega) ?_
  simp only [nprod, Ex.FV, decSet]
  repeat' first
    | trivial
    | omega
    | (simp; done)
    | apply And.intro

theorem fv_nmEx (hF : InstFV I) : Ex.FV (· < u + 10) (nmEx I) := by
  unfold nmEx
  refine fv_decodeE I hF (by omega) ?_
  simp only [nprod, Ex.FV, decSet]
  repeat' first
    | trivial
    | omega
    | (simp; done)
    | apply And.intro

variable {φ : ∀ c, ιc c → ι} (Ph : PhiEx L φ B Ctx A u)

theorem fv_parEx (hF : InstFV I) (hphi : Ex.FV (fun y => y < u + 10 ∨ y = u + 22 ∨ y = u + 23) Ph.phiE) :
    Ex.FV (· < u + 10) (parEx I φ Ph) := by
  rw [parEx_eq]
  refine fv_decodeE I hF (by omega) ?_
  simp only [parBody, ECDLP.L73.eqE, Ex.FV, decSet]
  repeat' first
    | exact Ex.FV_mono (fun y hy => by omega) _ hphi
    | trivial
    | omega
    | (simp; done)
    | apply And.intro


/-- the three FV facts that `midKind` asks of `X`, for the real structural expressions -/
theorem pex0_fv {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ} (hF : InstFV I) (hu : B ≤ u)
    (hphi : Ex.FV (fun y => y < u + 10 ∨ y = u + 22 ∨ y = u + 23) Ph.phiE) :
    Ex.FV (· < u + 10) (pex0 (F := F) (ok := ok) (m := m) I Ph hu).nfE ∧
    Ex.FV (· < u + 10) (pex0 (F := F) (ok := ok) (m := m) I Ph hu).nmE ∧
    Ex.FV (· < u + 10) (pex0 (F := F) (ok := ok) (m := m) I Ph hu).parE :=
  ⟨fv_nfEx I hF, fv_nmEx I hF, fv_parEx I Ph hF hphi⟩

end
end ECDLP.L79
end
