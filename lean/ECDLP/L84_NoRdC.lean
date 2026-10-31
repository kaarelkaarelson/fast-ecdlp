import ECDLP.L84_NoRd
import ECDLP.L79_AsmC

/-!
# L84 / NoRdC: read-set of the repaired (shallow-digit) kinds of L79 (`kindsC`) and of the whole dispatch built from them
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L84
open Finset Factoring.Aux Ex ECDLP.L73 ECDLP.L68 ECDLP.L64 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ} {a : ℕ → Prop}

theorem NoRd_phiWrap {phiE : Ex} (hphi : NoRd a phiE) : NoRd a (ECDLP.L79.phiWrap u phiE) := by
  simp [ECDLP.L79.phiWrap, NoRd, hphi]

theorem NoRd_digCfa : NoRd a (ECDLP.L79.digCfa u) := by simp [ECDLP.L79.digCfa, nprod, NoRd]
theorem NoRd_digCmid : NoRd a (ECDLP.L79.digCmid u) := by simp [ECDLP.L79.digCmid, nprod, NoRd]
theorem NoRd_digCib : NoRd a (ECDLP.L79.digCib u) := by simp [ECDLP.L79.digCib, nprod, NoRd]

theorem NoRd_faKindEC {phiE : Ex} (hphi : NoRd a phiE) :
    NoRd a (ECDLP.L79.faKindEC (u := u) phiE) := by
  simp [ECDLP.L79.faKindEC, ECDLP.L74.kParams, ECDLP.L79.faOutLD, ECDLP.L79.faInD, ECDLP.L68.faE, ECDLP.L74.faUE,
    mulE, pwE, sumE, natE, nprod, NoRd, hphi, NoRd_digCfa]

theorem NoRd_midKindEC {nE epsE lE rE : Ex} (hn : NoRd a nE) (he : NoRd a epsE) (hl : NoRd a lE) (hr : NoRd a rE) :
    NoRd a (ECDLP.L79.midKindEC (u := u) nE epsE lE rE) := by
  simp [ECDLP.L79.midKindEC, ECDLP.L74.kParams2, ECDLP.L74.kParams, ECDLP.L79.midOutLD, ECDLP.L74.midIn,
    ECDLP.L79.midYD, ECDLP.L68.midE, ECDLP.L68.faE, ECDLP.L68.hatYE, ECDLP.L68.hatE, ECDLP.L74.pfaKE,
    mulE, pwE, sumE, natE, nprod, NoRd, hn, he, hl, hr, NoRd_digCmid]

theorem NoRd_ibOutIC : NoRd a (ECDLP.L79.ibOutIC (u := u)) := by
  simp [ECDLP.L79.ibOutIC, ECDLP.L79.ibOutL2D, ECDLP.L75.ibE2, ECDLP.L79.ibBodyD, ECDLP.L75.e0I, ECDLP.L75.tEI,
    ECDLP.L75.kEI, ECDLP.L75.pmidEI, ECDLP.L68.hatE, mulE, pwE, sumE, natE, nprod, NoRd, NoRd_digCib]


variable {L : Lay ι ιc} {I : InstEx L N0 w B Ctx A u} {Ph : PhiEx L φ B Ctx A u} {hu : B ≤ u}
  (hI : InstNoRd a I) (hP : NoRd a Ph.phiE)

include hI hP in
/-- **`hcong` for the whole dispatch** (outE, wtE) built from `kindsC`: neither reads an array `b` with `a b`, provided the
instance expressions, `phiE`, the form oracles `nE epsE lE rE` and the source weight do not. -/
theorem NoRd_dispatchC (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c) (hw1 : ∀ c, 1 ≤ w c)
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
    (hnN : NoRd a nE) (heN : NoRd a epsE) (hlN : NoRd a lE) (hrN : NoRd a rE)
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (hs : NoRd a Sw.srcE) :
    NoRd a (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
        (ECDLP.L79.kindsC (F := F) (ok := ok) (m := m) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr)) ∧
      NoRd a (wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw) := by
  have hX := XNoRd_pex0 (F := F) (ok := ok) (m := m) (hu := hu) hI hP
  refine ⟨NoRd_outEx hI hX _ ?_ ?_ ?_, NoRd_wtEx hI hX Sw hs⟩
  · exact NoRd_guardE (NoRd_faKindEC (NoRd_phiWrap hP))
  · exact NoRd_guardE (NoRd_midKindEC hnN heN hlN hrN)
  · exact NoRd_ibOutIC

end
end ECDLP.L84
end
