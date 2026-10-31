import ECDLP.L73_Disp2

/-!
# L73 / Asm: the gate-level obligations `PEx` of `edgeNetM`, assembled
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- **the five structural expressions** (node count, free count, message count, width, parent test) of `edgeNetM` -/
def pex0 : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u where
  gE := gEx I
  nfE := nfEx I
  nmE := nmEx I
  wE := wEx I
  parE := parEx I φ Ph
  hg := fun σ₀ hC σ hσ => eval_gEx I hu hC hσ
  hnf := fun σ₀ hC σ hσ k hk => eval_nfEx I φ F ok m hu hC hσ hk
  hnm := fun σ₀ hC σ hσ k hk => eval_nmEx I φ F ok m hu hC hσ hk
  hw := fun σ₀ hC σ hσ k hk => eval_wEx I φ F ok m hu hC hσ hk
  hpar := fun σ₀ hC σ hσ p c hp hc => eval_parEx I φ F ok m Ph hu hC hσ hp hc

variable (hm1 : 1 < m)

/-- **`PEx` of the edge network**, from the gate kinds fa, mid, ib (L74, L75) and the source weight. -/
def pexEdge (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
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
    outE := outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd
    wtE := wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw
    hg := fun σ₀ hC σ hσ => eval_gEx I hu hC hσ
    hnf := fun σ₀ hC σ hσ k hk => eval_nfEx I φ F ok m hu hC hσ hk
    hnm := fun σ₀ hC σ hσ k hk => eval_nmEx I φ F ok m hu hC hσ hk
    hw := fun σ₀ hC σ hσ k hk => eval_wEx I φ F ok m hu hC hσ hk
    hpar := fun σ₀ hC σ hσ p c hp hc => eval_parEx I φ F ok m Ph hu hC hσ hp hc
    hout := fun σ₀ hC σ hσ a b z hab ha hb hz => hout_ex I _ hu hC hσ Kd a b z hab ha hb hz
    hwt := fun σ₀ hC σ hσ a z ha hz => hwt_ex I _ hu hC hσ Sw hm1 a z ha hz }


/-- **`NRep` of the edge network** (the `rep` field of `EdgeCore`, in the generic form of `nrep_pforced`) from the
assembled gate-level expressions. -/
theorem edge_nrep {σ₀ : ℕ → ℕ} {vm : ℕ} (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (hC : Ctx σ₀) (hm : σ₀ vm = m)
    (hm1 : 1 < m) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    NRep m vm B σ₀ A (NVars.std u)
      ⟨szEx (pexEdge I Ph hu hm1 Kd Sw), WEx (pexEdge I Ph hu hm1 Kd Sw), cEx (pexEdge I Ph hu hm1 Kd Sw),
        msgTest (mMsg (pexEdge I Ph hu hm1 Kd Sw) u (u + 1)) (cEx (pexEdge I Ph hu hm1 Kd Sw)) (u + 3) (u + 9),
        msgTest (mMsg (pexEdge I Ph hu hm1 Kd Sw) (u + 1) u) (cEx (pexEdge I Ph hu hm1 Kd Sw)) (u + 3) (u + 9)⟩
      ((toGNetE (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)).toNet (L.enum N0.A))
      (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)) :=
  haveI := edge_free_nonempty (w := w) φ F ok m
  nrep_pforced (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A) u vm
    (pexEdge I Ph hu hm1 Kd Sw) hu hC hm hm1 (edge_P01 (w := w) φ F ok m)

end
end ECDLP.L73
end
