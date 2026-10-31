import ECDLP.L89_Wt

/-!
# L89 / Asm: `PExBw` of the (clamped) edge network `PEx`, and the NBdd of its expressions

`pexBw_edge`: the value bounds `PExBw` for `clampPEx (pexEdge ..)`: structural fields from L84 (`bdd_gEx`, `bdd_nfEx`, `bdd_nmEx`, `bdd_wEx`,
`bdd_parEx`), `bwt` from `bdd_wtEx`, `bout` from `bdd_outEx` + the clamp.  Remaining hypotheses are exactly: the numeric facts on `V`
(`hsN`, `hcV`, `hwV`, `hAA`, `InstBdd`, `DecNum`, `NodeNum`, bound of `phiE`) and the per-kind bounds (fa, mid, ib in the `KSt` form, car, source weight, car weight).
`nbdd_edge`: `NBdd V B sigma0 A (NVars.std u) E g` for the expressions of the clamped network (the `NBdd` part of `EdgeCore.bnd`).
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
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) {V : ℕ}

/-- **the per-kind and numeric data** from which `PExBw` of the edge network follows -/
structure EdgeBdd (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) : Prop where
  h8 : 8 ≤ V
  hAA : N0.A * N0.A ≤ V
  hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE
  hsN : ∀ a : ℕ, sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V
  hcV : ∀ a b : Fin (L.gTot N0.A), 2 ^ (toGNetE (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)).c
    ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) ≤ V
  hwV : ∀ i, (edgeNetM (w := w) φ F ok m).w i + 1 ≤ V
  hfa : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.fa →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.fa.outE
  hmid : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.mid →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.mid.outE
  hib : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.ib →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.ib.outE
  hcarO : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 5) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 7) ≤ V → Bdd V σ A (carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
  hsrc : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (i : ι) (s : Fin N0.A),
      (L.enum N0.A).symm a = CG.src i s → σ (u + 4) = a → σ (u + 7) ≤ V →
      σ (u + 10) = 2 ^ N0.b → σ (u + 12) = N0.A → σ (u + 13) = N0.h → σ (u + 14) = N0.b →
      σ (u + 16) = L.eι i → σ (u + 17) = s → Bdd V σ A Sw.srcE
  hcarW : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 4) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 28) = N0.A * N0.A → σ (u + 7) ≤ V →
      Bdd V σ A (carWX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu))

/-- **`PExBw` of the clamped edge network.** -/
theorem pexBw_edge (hm1 : 1 < m) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (D : EdgeBdd (F := F) (ok := ok) (m := m) I Ph hu IB DN NN Kd Sw) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    PExBw (clampPEx (pexEdge I Ph hu hm1 Kd Sw) hu) V := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  refine pExBw_clamp (pexEdge I Ph hu hm1 Kd Sw) hu
    { hV := D.h8
      hgV := DN.hG
      hsN := D.hsN
      hcV := D.hcV
      hwV := D.hwV
      bg := fun σ₀ hC σ hσ => bdd_gEx I IB DN hu hC hσ
      bnf := fun σ₀ hC σ hσ k hk => bdd_nfEx I IB DN NN D.h8 hu hC hσ k hk
      bnm := fun σ₀ hC σ hσ k hk => bdd_nmEx I IB DN NN D.h8 hu hC hσ k hk
      bw := fun σ₀ hC σ hσ k hk => bdd_wEx I IB DN NN D.h8 hu hC hσ k hk
      bpar := fun σ₀ hC σ hσ p c hp hc => bdd_parEx I IB DN Ph D.h8 D.hphiB hu hC hσ p c hp hc
      bwt := fun σ₀ hC σ hσ a ha hz =>
        bdd_wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) hu IB DN D.h8 D.hAA Sw D.hsrc D.hcarW σ₀ hC σ hσ a ha hz }
    (fun σ₀ hC σ hσ a b hab ha hb hz =>
      bdd_outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd hu IB DN D.h8 D.hfa D.hmid D.hib D.hcarO σ₀ hC σ hσ a b hab ha hb hz)


/-- **`NBdd` of the expressions of the clamped edge network** (the `NBdd` conjunct of `EdgeCore.bnd`, with `g = gTot`). -/
theorem nbdd_edge (hm1 : 1 < m) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (D : EdgeBdd (F := F) (ok := ok) (m := m) I Ph hu IB DN NN Kd Sw) {σ₀ : ℕ → ℕ} (hC : Ctx σ₀) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    NBdd V B σ₀ A (NVars.std u) (netEx (clampPEx (pexEdge I Ph hu hm1 Kd Sw) hu)) (L.gTot N0.A) := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  exact nbdd_netExW _ (pexBw_edge I Ph hu hm1 IB DN NN Kd Sw D) hu hC (σ := σ₀) (fun y hy => rfl)

end
end ECDLP.L89
end
