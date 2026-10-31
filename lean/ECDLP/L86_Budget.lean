import ECDLP.L86_Pex

/-!
# L86 / Budget: the five `NEx` fields of the edge network have depth `<= 60` with the repaired dispatch

Exact depths of the new pieces (`carOutXD` 13, `carWXD` 15, `outBody3`, `outEx3`, `wtEx3`) and the conditional budget theorem
`edge3_dp_le_60`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

theorem dp_carOutXD (u : ℕ) : Ex.dp (carOutXD u) = 13 := by
  simp [carOutXD, carInD, carOutE, tE, digCarC, digCarR, Ex.dp]

theorem dp_carWXD (u : ℕ) : Ex.dp (carWXD u) = 15 := by
  simp [carWXD, carInD, carWE, tE, digCarC, digCarR, Ex.dp]

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- exact depth of the repaired message-code body -/
theorem dp_outBody3 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) :
    Ex.dp (outBody3 X Em Kd) =
      max 9 (max (max 4 (Ex.dp Em)) (max (max 3 (Ex.dp Kd.fa.outE + 2)) (max (Ex.dp Kd.ib.outE) 13 + 3)) + 1) + 1 := by
  have := dpT_pos Kd.fa.outE
  have := dpT_pos Kd.ib.outE
  have := dpT_pos Em
  simp only [outBody3, dp_disp2, dp_dqE, Ex.dp, dp_carOutXD]
  omega

theorem dp_outEx3_le (Em : Ex) (Kd : Kinds (w := w) (m := m) X) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (outEx3 I X Em Kd) ≤ max (max (dI + 16) 21) (Ex.dp (outBody3 X Em Kd) + 15) :=
  dp_decodeE_le I (u + 5) (outBody3 X Em Kd) h1 h2 h3 h4 h5 h6 h7 h8

theorem dp_wtChain3 (Sw : SrcWt (w := w) X) :
    Ex.dp (wtChain3 X Sw) = max (Ex.dp Sw.srcE) 17 + 1 := by
  have := dpT_pos Sw.srcE
  simp only [wtChain3, dp_carWXD, Ex.dp]
  omega

theorem dp_wtEx3_le (Sw : SrcWt (w := w) X) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (wtEx3 I X Sw) ≤ max (max (dI + 16) 21) (max (Ex.dp Sw.srcE) 17 + 1 + 15) := by
  have := dp_decodeE_le I (u + 4) (wtChain3 X Sw) h1 h2 h3 h4 h5 h6 h7 h8
  rw [dp_wtChain3] at this
  exact this

end

section genPEx
variable {m' B' g : ℕ} {Ctx' : (ℕ → ℕ) → Prop} {A' : ℕ → ℕ → ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
  {P' : ECDLP.L56.PForced (ZMod m') ι'} {E' : ∀ i, P'.Msg i ≃ Fin (Fintype.card (P'.Msg i))}
  {EF' : ∀ i, P'.Free i ≃ Fin (Fintype.card (P'.Free i))} {e' : ι' ≃ Fin g} [hF' : ∀ i, Nonempty (P'.Free i)] {u' : ℕ}
  (Xp : PEx (B := B') (Ctx := Ctx') (A := A') P' E' EF' e' u')

theorem dp_par2' (p c : ℕ) : Ex.dp (ECDLP.L64.par2 Xp p c) = Ex.dp Xp.parE + 2 := by
  have := dpT_pos Xp.parE
  simp only [ECDLP.L64.par2, Ex.dp]; omega

theorem dp_un1' (t : ℕ) (b : Ex) : Ex.dp (ECDLP.L64.un1 Xp t b) = Ex.dp b + 1 := by
  have := dpT_pos b
  simp only [ECDLP.L64.un1, Ex.dp]; omega

theorem dp_digE' (fr tt : ℕ) :
    Ex.dp (ECDLP.L64.digE Xp fr tt) = max (max (Ex.dp Xp.nfE + 4) (Ex.dp Xp.parE + 6)) (Ex.dp Xp.nmE + 5) := by
  have h1 := dpT_pos Xp.parE
  have h2 := dpT_pos Xp.nmE
  have h3 := dpT_pos Xp.nfE
  simp only [ECDLP.L64.digE, ECDLP.L64.ppE, ECDLP.L64.nAE, nprod, dp_par2', dp_un1', Ex.dp]
  omega

theorem dp_szEx' : Ex.dp (ECDLP.L64.szEx Xp) =
    max (max (max (Ex.dp Xp.gE) (max (Ex.dp Xp.parE + 2) (Ex.dp Xp.nmE + 1) + 1)) 1 + 1) (Ex.dp Xp.nfE + 1) + 1 := by
  have h1 := dpT_pos Xp.parE
  have h2 := dpT_pos Xp.nmE
  have h3 := dpT_pos Xp.nfE
  have h4 := dpT_pos Xp.gE
  simp only [ECDLP.L64.szEx, ECDLP.L64.nAE, nprod, dp_par2', dp_un1', Ex.dp]
  omega

theorem dp_WEx' : Ex.dp (ECDLP.L64.WEx Xp) = Ex.dp Xp.wtE + 2 := by
  have := dpT_pos Xp.wtE
  simp only [ECDLP.L64.WEx, Ex.dp]; omega

theorem dp_cEx' : Ex.dp (ECDLP.L64.cEx Xp) =
    max (max 1 (Ex.dp Xp.parE + 2)) (max (max (Ex.dp Xp.wE + 1) 1 + 1) (max (max 1 (Ex.dp Xp.parE + 2)) (max (max (Ex.dp Xp.wE + 1) 1 + 1) 1) + 1)) + 1 := by
  have h1 := dpT_pos Xp.parE
  have h2 := dpT_pos Xp.wE
  simp only [ECDLP.L64.cEx, dp_par2', dp_un1', Ex.dp]
  try omega
end genPEx

section total
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

theorem dp_gEx_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI) :
    Ex.dp (gEx I) ≤ dI + 8 := by
  have := dpT_pos I.AE
  simp only [gEx, offE, blkLoop, nsum, Ex.dp]
  omega

theorem dp_wEx_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (wEx I) ≤ max (dI + 16) 21 := by
  have h := dp_decodeE_le I (u + 4) (.ifLt (.var (u + 21)) (.lit 1) (.mul (.var (u + 14)) (.var (u + 13)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 27)) (.lit 1)) (.add (.var (u + 27)) (.lit 3)))) h1 h2 h3 h4 h5 h6 h7 h8
  unfold wEx
  simp only [Ex.dp] at h ⊢
  omega

/-- **Budget theorem.**  With the instance expressions of depth `<= dI <= 20`, the fa-index oracle of depth `<= dφ <= 21`, the source weight of depth `<= 30`,
`dp fa <= 33`, `dp ib <= 32`, `dp Em <= 35` (raw mid), all five fields of the `NEx` of `edge_nrep3` have depth `<= 60`. -/
theorem edge3_dp_le_60 (hm1 : 1 < m) (Em : Ex) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (hmid : Kd.mid.outE = guardE u Em) (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    {dI dphi : ℕ} (hdI : dI ≤ 20) (hdphi : dphi ≤ 21)
    (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI) (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI)
    (h6 : Ex.dp I.ncE ≤ dI) (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI)
    (hphi : Ex.dp Ph.phiE ≤ dphi) (hS : Ex.dp Sw.srcE ≤ 30)
    (hfa : Ex.dp Kd.fa.outE ≤ 33) (hib : Ex.dp Kd.ib.outE ≤ 32) (hEm : Ex.dp Em ≤ 35) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := pexEdge3 I Ph hu hm1 Em Kd hmid Sw
    Ex.dp (szEx P) ≤ 60 ∧ Ex.dp (WEx P) ≤ 60 ∧ Ex.dp (cEx P) ≤ 60 ∧
      Ex.dp (msgTest (mMsg P u (u + 1)) (cEx P) (u + 3) (u + 9)) ≤ 60 ∧
      Ex.dp (msgTest (mMsg P (u + 1) u) (cEx P) (u + 3) (u + 9)) ≤ 60 := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  have eg : P.gE = gEx I := rfl
  have enf : P.nfE = nfEx I := rfl
  have enm : P.nmE = nmEx I := rfl
  have ew : P.wE = wEx I := rfl
  have epar : P.parE = parEx I φ Ph := rfl
  have eout : P.outE = outEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Em Kd := rfl
  have ewt : P.wtE = wtEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw := rfl
  have dg := dp_gEx_le I h1 h4 h5 h6
  have dnf := dp_nfEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dnm := dp_nmEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dw := dp_wEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dpar := dp_parEx_le I Ph h1 h2 h3 h4 h5 h6 h7 h8
  have dout := dp_outEx3_le I _ Em Kd h1 h2 h3 h4 h5 h6 h7 h8
  have dbody := dp_outBody3 (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Em Kd
  have dwt := dp_wtEx3_le I _ Sw h1 h2 h3 h4 h5 h6 h7 h8
  have := dpT_pos Kd.fa.outE
  have := dpT_pos Kd.ib.outE
  have := dpT_pos Em
  have := dpT_pos Sw.srcE
  have hpar_pos := dpT_pos (parEx I φ Ph)
  have hcE := dp_cEx' P
  have hsz := dp_szEx' P
  have hW := dp_WEx' P
  have hdg := dp_digE' P
  simp only [eg, enf, enm, ew, epar, eout, ewt] at hcE
  simp only [eg, enf, enm, ew, epar, eout, ewt] at hsz
  simp only [eg, enf, enm, ew, epar, eout, ewt] at hW
  simp only [eg, enf, enm, ew, epar, eout, ewt] at hdg
  have hm1' := fun fr tt => dp_msgTest_eq P (ECDLP.L64.cEx P) fr tt (u + 3) (u + 9)
  have hl := hm1' u (u + 1)
  have hr := hm1' (u + 1) u
  simp only [hdg, epar, eout, hcE] at hl
  simp only [hdg, epar, eout, hcE] at hr
  have := dpT_pos (wtEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw)
  clear_value P
  have hfa' := hfa
  generalize Ex.dp (parEx I φ Ph) = dparE at *
  generalize Ex.dp (nfEx I) = dnfE at *
  generalize Ex.dp (nmEx I) = dnmE at *
  generalize Ex.dp (wEx I) = dwE at *
  generalize Ex.dp (gEx I) = dgE at *
  generalize Ex.dp (outEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Em Kd) = doutE at *
  generalize Ex.dp (wtEx3 I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw) = dwtE at *
  generalize Ex.dp (outBody3 (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Em Kd) = dbodyE at *
  generalize Ex.dp Kd.fa.outE = dfaE at *
  generalize Ex.dp Kd.ib.outE = dibE at *
  generalize Ex.dp Em = dEm at *
  generalize Ex.dp Sw.srcE = dsrcE at *
  generalize Ex.dp Ph.phiE = dphiE at *
  have b_par : dparE ≤ 44 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_nf : dnfE ≤ 36 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_nm : dnmE ≤ 36 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_w : dwE ≤ 36 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_g : dgE ≤ 28 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_body : dbodyE ≤ 37 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_out : doutE ≤ 52 := by clear hl hr hsz hcE hW hm1' hdg; omega
  have b_wt : dwtE ≤ 46 := by clear hl hr hsz hcE hW hm1' hdg; omega
  clear hm1' hdg dout dbody dwt dw dnf dnm dg dpar hfa' hfa hib hEm hS hphi h1 h2 h3 h4 h5 h6 h7 h8 hdI hdphi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsz]; omega
  · rw [hW]; omega
  · rw [hcE]; omega
  · rw [hl]; omega
  · rw [hr]; omega

end total
end ECDLP.L86
end
