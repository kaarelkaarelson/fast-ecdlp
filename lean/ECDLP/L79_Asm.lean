import ECDLP.L79_Kind
import ECDLP.L79_Fv

/-!
# L79 / Asm: L73's `Kinds` for `pex0` from the guarded fa / mid kinds
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

/-- **L73's `Kinds`** for the real structural expressions `pex0`: fa and mid from this module (guarded), ib supplied (L75).
Extra hypotheses (all explicit): `M >= 1`, `nc >= 1`, the free variables of the instance expressions and of `phiE`,
and the `Ag`-form semantic hypotheses of the four form oracles. -/
def kindsG (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c) (hF : InstFV I)
    (hphiFV : Ex.FV (fun y => y < u + 10 ∨ y = u + 22 ∨ y = u + 23) Ph.phiE)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ))
    (ibK : GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L .ib (L.enum N0.A) u
      (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) :
    Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu) where
  fa := faKindG (φ := φ) (F := F) (ok := ok) L _ hu hM1 (phiWrap u Ph.phiE) (hphi_of_PhiEx L Ph hu)
  mid := by
    obtain ⟨h1, h2, h3⟩ := pex0_fv (F := F) (ok := ok) (m := m) I Ph hF hu hphiFV
    exact midKindG (φ := φ) (F := F) (ok := ok) L _ hu hM1 hne h1 h2 h3 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr
  ib := ibK

end
end ECDLP.L79
end
