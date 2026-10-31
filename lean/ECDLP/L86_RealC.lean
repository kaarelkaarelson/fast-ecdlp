import ECDLP.L86_RealTot
import ECDLP.L79_AsmC

/-!
# L86 / RealC: the real dispatch WITH L79's repaired kinds (`kindsC`) meets the depth side of `ExSyn 200`

`kindsC_outE`: the three kind expressions of `kindsC` are `guardE u (faKindEC (phiWrap u phiE))`, `guardE u (midKindEC ..)`, `ibOutIC`.
`edge_real_kindsC_dp_le_160`: oracle depths `<= 75`, `dp phiE <= 40`, instance expressions `<= 40`, `dp srcE <= 60` give all five `E` fields `<= 160`
(L73's `outEx`/`wtEx`/`carOutX`/`carWX` unchanged).
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)
  (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c) (hw1 : ∀ c, 1 ≤ w c)
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

theorem kindsC_outE :
    (kindsC (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).fa.outE =
        guardE u (faKindEC (u := u) (phiWrap u Ph.phiE)) ∧
    (kindsC (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).mid.outE =
        guardE u (midKindEC (u := u) nE epsE lE rE) ∧
    (kindsC (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).ib.outE =
        ibOutIC (u := u) := ⟨rfl, rfl, rfl⟩

theorem edge_real_kindsC_dp_le_160 (hm1 : 1 < m)
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    {dI dphi : ℕ} (hdI : dI ≤ 40) (hdphi : dphi ≤ 40)
    (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI) (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI)
    (h6 : Ex.dp I.ncE ≤ dI) (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI)
    (hphi : Ex.dp Ph.phiE ≤ dphi) (hS : Ex.dp Sw.srcE ≤ 60)
    (dn : Ex.dp nE ≤ 75) (de : Ex.dp epsE ≤ 75) (dl : Ex.dp lE ≤ 75) (dr : Ex.dp rE ≤ 75) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := pexEdge I Ph hu hm1
      (kindsC (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr) Sw
    Ex.dp (szEx P) ≤ 160 ∧ Ex.dp (WEx P) ≤ 160 ∧ Ex.dp (cEx P) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P u (u + 1)) (cEx P) (u + 3) (u + 9)) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P (u + 1) u) (cEx P) (u + 3) (u + 9)) ≤ 160 := by
  obtain ⟨ef, em, ei⟩ := kindsC_outE (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr
  have dfa : Ex.dp (guardE u (faKindEC (u := u) (phiWrap u Ph.phiE))) = max 20 (Ex.dp (phiWrap u Ph.phiE) + 10) :=
    dp_faKindEC _
  have dmid := dp_midKindEC_le (u := u) (d := 75) (by omega) nE epsE lE rE dn de dl dr
  have dib := dp_ibOutIC (u := u)
  have dpw : Ex.dp (phiWrap u Ph.phiE) = Ex.dp Ph.phiE + 2 := by
    have := dpT_pos Ph.phiE
    simp only [phiWrap, Ex.dp]; omega
  refine edge_real_dp_le_160 I Ph hu hm1 _ Sw hdI hdphi h1 h2 h3 h4 h5 h6 h7 h8 hphi hS ?_ ?_ ?_
  · rw [ef, dfa, dpw]; omega
  · rw [em]; omega
  · rw [ei, dib]; omega

end
end ECDLP.L86
end
