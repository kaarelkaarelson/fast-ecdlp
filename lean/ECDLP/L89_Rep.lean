import ECDLP.L89_Asm

/-!
# L89 / Rep: `NRep` of the CLAMPED edge network (`edge_nrep` with `clampPEx`)

`edge_nrepC`: the conclusion of L73's `edge_nrep`, for the expressions of `clampPEx (pexEdge ..)` (message code taken modulo the message
count; needed because the unclamped network has no `NBdd`, see L89_Clamp / REPORT).  Same hypotheses as `edge_nrep`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L89
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L84

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- the `PEx` of the clamped edge network -/
def pexEdgeC (hm1 : 1 < m) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    PEx (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)
      (edgeEFM φ F ok m) (L.enum N0.A) u :=
  haveI := edge_free_nonempty (w := w) φ F ok m
  clampPEx (pexEdge I Ph hu hm1 Kd Sw) hu

theorem edge_nrepC {σ₀ : ℕ → ℕ} {vm : ℕ} (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (hC : Ctx σ₀) (hm : σ₀ vm = m)
    (hm1 : 1 < m) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    NRep m vm B σ₀ A (NVars.std u)
      ⟨szEx (pexEdgeC I Ph hu hm1 Kd Sw), WEx (pexEdgeC I Ph hu hm1 Kd Sw), cEx (pexEdgeC I Ph hu hm1 Kd Sw),
        msgTest (mMsg (pexEdgeC I Ph hu hm1 Kd Sw) u (u + 1)) (cEx (pexEdgeC I Ph hu hm1 Kd Sw)) (u + 3) (u + 9),
        msgTest (mMsg (pexEdgeC I Ph hu hm1 Kd Sw) (u + 1) u) (cEx (pexEdgeC I Ph hu hm1 Kd Sw)) (u + 3) (u + 9)⟩
      ((toGNetE (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)).toNet (L.enum N0.A))
      (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)) :=
  haveI := edge_free_nonempty (w := w) φ F ok m
  nrep_pforced (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A) u vm
    (pexEdgeC I Ph hu hm1 Kd Sw) hu hC hm hm1 (edge_P01 (w := w) φ F ok m)

/-- `nbdd_edge` stated for `pexEdgeC` -/
theorem nbdd_edgeC {V : ℕ} (hm1 : 1 < m) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (D : EdgeBdd (F := F) (ok := ok) (m := m) I Ph hu IB DN NN Kd Sw) {σ₀ : ℕ → ℕ} (hC : Ctx σ₀) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    NBdd V B σ₀ A (NVars.std u) (netEx (pexEdgeC I Ph hu hm1 Kd Sw)) (L.gTot N0.A) :=
  nbdd_edge I Ph hu hm1 IB DN NN Kd Sw D hC

end
end ECDLP.L89
end
