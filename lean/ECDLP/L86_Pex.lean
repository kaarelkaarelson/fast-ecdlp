import ECDLP.L86_Disp

/-!
# L86 / Pex: `PEx` and `NRep` of the edge network with the repaired dispatch

`pexEdge3` is L73's `pexEdge` with `outE := outEx3`, `wtE := wtEx3` (car gate without `digE`, balanced dispatch).  The kinds are L73's `Kinds`
(e.g. L79's `kindsC`), the mid kind must be of the form `guardE u Em`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- **`PEx` of the edge network with the repaired dispatch** -/
def pexEdge3 (hm1 : 1 < m) (Em : Ex) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (hmid : Kd.mid.outE = guardE u Em)
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    PEx (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)
      (edgeEFM φ F ok m) (L.enum N0.A) u :=
  haveI := edge_free_nonempty (w := w) φ F ok m
  { gE := gEx I
    nfE := nfEx I
    nmE := nmEx I
    wE := wEx I
    parE := parEx I φ Ph
    outE := outEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Em Kd
    wtE := wtEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw
    hg := fun σ₀ hC σ hσ => eval_gEx I hu hC hσ
    hnf := fun σ₀ hC σ hσ k hk => eval_nfEx I φ F ok m hu hC hσ hk
    hnm := fun σ₀ hC σ hσ k hk => eval_nmEx I φ F ok m hu hC hσ hk
    hw := fun σ₀ hC σ hσ k hk => eval_wEx I φ F ok m hu hC hσ hk
    hpar := fun σ₀ hC σ hσ p c hp hc => eval_parEx I φ F ok m Ph hu hC hσ hp hc
    hout := fun σ₀ hC σ hσ a b z hab ha hb hz => hout_ex3 I _ hu hC hσ Kd Em hmid a b z hab ha hb hz
    hwt := fun σ₀ hC σ hσ a z ha hz => hwt_ex3 I _ hu hC hσ Sw hm1 a z ha hz }

/-- **`NRep` of the edge network** with the repaired dispatch (the `rep` field of `EdgeCore`; same statement as L73's `edge_nrep`) -/
theorem edge_nrep3 {σ₀ : ℕ → ℕ} {vm : ℕ} (Em : Ex) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (hmid : Kd.mid.outE = guardE u Em)
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (hC : Ctx σ₀) (hm : σ₀ vm = m)
    (hm1 : 1 < m) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    NRep m vm B σ₀ A (NVars.std u)
      ⟨szEx (pexEdge3 I Ph hu hm1 Em Kd hmid Sw), WEx (pexEdge3 I Ph hu hm1 Em Kd hmid Sw), cEx (pexEdge3 I Ph hu hm1 Em Kd hmid Sw),
        msgTest (mMsg (pexEdge3 I Ph hu hm1 Em Kd hmid Sw) u (u + 1)) (cEx (pexEdge3 I Ph hu hm1 Em Kd hmid Sw)) (u + 3) (u + 9),
        msgTest (mMsg (pexEdge3 I Ph hu hm1 Em Kd hmid Sw) (u + 1) u) (cEx (pexEdge3 I Ph hu hm1 Em Kd hmid Sw)) (u + 3) (u + 9)⟩
      ((toGNetE (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)).toNet (L.enum N0.A))
      (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)) :=
  haveI := edge_free_nonempty (w := w) φ F ok m
  nrep_pforced (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A) u vm
    (pexEdge3 I Ph hu hm1 Em Kd hmid Sw) hu hC hm hm1 (edge_P01 (w := w) φ F ok m)

end
end ECDLP.L86
end
