import ECDLP.L79_Asm
import ECDLP.L79_IbKindC
import ECDLP.L79_DepthC

/-!
# L79 / AsmC: L73's `Kinds` for `pex0` from the REPAIRED (shallow-digit) fa, mid, ib kinds
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- **L73's `Kinds` with the shallow digit**: guarded fa and mid, and ib.  No free-variable hypotheses on `nfE, nmE, parE` are needed
(the kinds do not call `digE`).  `h27` of the ib kind is discharged by `KSt.hM`. -/
def kindsC (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c) (hw1 : ∀ c, 1 ≤ w c)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ)) :
    Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu) where
  fa := guardKind (φ := φ) (F := F) (ok := ok) L _ (Or.inl rfl)
    (faKindC (φ := φ) (F := F) (ok := ok) L _ hu hM1 (phiWrap u Ph.phiE) (hphi_of_PhiEx L Ph hu))
  mid := guardKind (φ := φ) (F := F) (ok := ok) L _ (Or.inr rfl)
    (midKindC (φ := φ) (F := F) (ok := ok) L _ hu hM1 hne nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr)
  ib := ibKindC (φ := φ) (F := F) (ok := ok) L _ hu hw1 (fun σ₀ hC σ hσ a b hks c hid => hks.hM c hid)

end
end ECDLP.L79
end
