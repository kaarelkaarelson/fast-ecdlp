import ECDLP.L84_BddNode
import ECDLP.L79_IbKindCB
import ECDLP.L79_FaCKB
import ECDLP.L79_MidCKB

/-!
# L84 / PExB0: the structural value bounds of the real network, packaged as `PExB0` (both L74's and L75's structure)

`pexB0_L75`, `pexB0_L74`: `PExB0 (pex0 I Ph hu) V` from the bounds of the instance expressions (`InstBdd`), the decode numerics (`DecNum`),
the node-size numerics (`NodeNum`), the bound of `phiE`, and `sN a <= V` (the setting counts: `sN_le_wtH` of L75 gives `sN <= 2^wtH`,
so `V >= 2^(O(m) X^3)`, a hypothesis here).
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L84
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}

theorem pexB0_L75 {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) (h8 : 8 ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE)
    (hsN : ∀ a : ℕ, sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V) :
    ECDLP.L75.PExB0 (pex0 (F := F) (ok := ok) (m := m) I Ph hu) V where
  hV := h8
  hgV := DN.hG
  hsN := hsN
  bg := fun σ₀ hC σ hσ => bdd_gEx I IB DN hu hC hσ
  bnf := fun σ₀ hC σ hσ k hk => bdd_nfEx I IB DN NN h8 hu hC hσ k hk
  bnm := fun σ₀ hC σ hσ k hk => bdd_nmEx I IB DN NN h8 hu hC hσ k hk
  bpar := fun σ₀ hC σ hσ p c hp hc => bdd_parEx I IB DN Ph h8 hphiB hu hC hσ p c hp hc

theorem pexB0_L74 {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) (h8 : 8 ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE)
    (hsN : ∀ a : ℕ, sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V) :
    ECDLP.L74.PExB0 (pex0 (F := F) (ok := ok) (m := m) I Ph hu) V where
  hV := h8
  hgV := DN.hG
  hsN := hsN
  bnf := fun σ₀ hC σ hσ k hk => bdd_nfEx I IB DN NN h8 hu hC hσ k hk
  bnm := fun σ₀ hC σ hσ k hk => bdd_nmEx I IB DN NN h8 hu hC hσ k hk
  bpar := fun σ₀ hC σ hσ p c hp hc => bdd_parEx I IB DN Ph h8 hphiB hu hC hσ p c hp hc

end
end ECDLP.L84
end
