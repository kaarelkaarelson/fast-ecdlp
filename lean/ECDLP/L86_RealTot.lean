import ECDLP.L86_Real

/-!
# L86 / RealTot: **the real dispatch meets the depth side of L85's `ExSyn 200`**

`edge_real_dp_le_160`: for L73's `pexEdge` (unchanged `outEx`, `wtEx`, `carOutX`/`carWX` with `digE`, linear dispatch), with arbitrary `Kinds` and `SrcWt`,
the five `NEx` fields of `edge_nrep` (`szEx, WEx, cEx, msgTest .. l, msgTest .. r`) have depth `<= 160`, which is `Ex.dp E.f + 40 <= 200`.
Hypotheses are depth bounds only: the 8 InstEx expressions `<= dI <= 40`, `phiE <= 40`, `srcE <= 60`, the three kind expressions `<= 100`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

theorem ar_par {dI dphi dp ph : ℕ} (hdI : dI ≤ 40) (hdphi : dphi ≤ 40) (hph : ph ≤ dphi) (h : dp ≤ max (max (dI + 16) (ph + 23)) 29) :
    dp ≤ 63 := by omega
theorem ar_dec {dI dp : ℕ} (hdI : dI ≤ 40) (h : dp ≤ max (dI + 16) 21) : dp ≤ 56 := by omega
theorem ar_g {dI dp : ℕ} (hdI : dI ≤ 40) (h : dp ≤ dI + 8) : dp ≤ 48 := by omega
theorem ar_dig {nf par nm dg : ℕ} (h1 : nf ≤ 56) (h2 : par ≤ 63) (h3 : nm ≤ 56) (h : dg = max (max (nf + 4) (par + 6)) (nm + 5)) :
    dg ≤ 69 := by omega
theorem ar_car {dI dg dc k : ℕ} (hdI : dI ≤ 40) (hdg : dg ≤ 69) (h : dc ≤ max (max (dI + 16) 21) (dg + 1) + k) (hk : k ≤ 6) :
    dc ≤ 82 := by omega
theorem ar_out {dI fa mid ib car dout : ℕ} (hdI : dI ≤ 40) (h1 : fa ≤ 100) (h2 : mid ≤ 100) (h3 : ib ≤ 100) (h4 : car ≤ 82)
    (h : dout ≤ max (max (dI + 16) 25) (max (max (fa + 3) (mid + 4)) (max (ib + 5) (car + 5)) + 15 + 1)) : dout ≤ 121 := by omega
theorem ar_wt {dI src cw dwt : ℕ} (hdI : dI ≤ 40) (h1 : src ≤ 60) (h2 : cw ≤ 82)
    (h : dwt ≤ max (max (dI + 16) 25) (max (src + 1) (cw + 3) + 15)) : dwt ≤ 100 := by omega

section total
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

theorem edge_real_dp_le_160 (hm1 : 1 < m) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    {dI dphi : ℕ} (hdI : dI ≤ 40) (hdphi : dphi ≤ 40)
    (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI) (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI)
    (h6 : Ex.dp I.ncE ≤ dI) (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI)
    (hphi : Ex.dp Ph.phiE ≤ dphi) (hS : Ex.dp Sw.srcE ≤ 60)
    (hfa : Ex.dp Kd.fa.outE ≤ 100) (hmid : Ex.dp Kd.mid.outE ≤ 100) (hib : Ex.dp Kd.ib.outE ≤ 100) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := pexEdge I Ph hu hm1 Kd Sw
    Ex.dp (szEx P) ≤ 160 ∧ Ex.dp (WEx P) ≤ 160 ∧ Ex.dp (cEx P) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P u (u + 1)) (cEx P) (u + 3) (u + 9)) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P (u + 1) u) (cEx P) (u + 3) (u + 9)) ≤ 160 := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  have eg : P.gE = gEx I := rfl
  have enf : P.nfE = nfEx I := rfl
  have enm : P.nmE = nmEx I := rfl
  have ew : P.wE = wEx I := rfl
  have epar : P.parE = parEx I φ Ph := rfl
  have eout : P.outE = outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd := rfl
  have ewt : P.wtE = wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw := rfl
  have dg := dp_gEx_le I h1 h4 h5 h6
  have dnf := dp_nfEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dnm := dp_nmEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dw := dp_wEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dpar := dp_parEx_le I Ph h1 h2 h3 h4 h5 h6 h7 h8
  have dout := dp_outEx_real I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd h1 h2 h3 h4 h5 h6 h7 h8
  have dwt := dp_wtEx_real I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw h1 h2 h3 h4 h5 h6 h7 h8
  have dcar := dp_carOutX_le I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) h1 h2 h3 h4 h5 h6 h7 h8
  have dcarw := dp_carWX_le I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) h1 h2 h3 h4 h5 h6 h7 h8
  have ddig : Ex.dp (ECDLP.L68.digE (pex0 (F := F) (ok := ok) (m := m) I Ph hu) u (u + 1)) =
      max (max (Ex.dp (nfEx I) + 4) (Ex.dp (parEx I φ Ph) + 6)) (Ex.dp (nmEx I) + 5) :=
    dp_digE L (pex0 (F := F) (ok := ok) (m := m) I Ph hu) u (u + 1)
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
  have hpos1 := dpT_pos (parEx I φ Ph)
  have hpos2 := dpT_pos (wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw)
  clear_value P
  generalize Ex.dp (parEx I φ Ph) = dparE at *
  generalize Ex.dp (nfEx I) = dnfE at *
  generalize Ex.dp (nmEx I) = dnmE at *
  generalize Ex.dp (wEx I) = dwE at *
  generalize Ex.dp (gEx I) = dgE at *
  generalize Ex.dp (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) = doutE at *
  generalize Ex.dp (wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw) = dwtE at *
  generalize Ex.dp (carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) = dcarE at *
  generalize Ex.dp (carWX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) = dcarwE at *
  generalize Ex.dp (ECDLP.L68.digE (pex0 (F := F) (ok := ok) (m := m) I Ph hu) u (u + 1)) = ddigE at *
  generalize Ex.dp Kd.fa.outE = dfaE at *
  generalize Ex.dp Kd.mid.outE = dmidE at *
  generalize Ex.dp Kd.ib.outE = dibE at *
  generalize Ex.dp Sw.srcE = dsrcE at *
  generalize Ex.dp Ph.phiE = dphiE at *
  have b_par : dparE ≤ 63 := ar_par hdI hdphi hphi dpar
  have b_nf : dnfE ≤ 56 := ar_dec hdI dnf
  have b_nm : dnmE ≤ 56 := ar_dec hdI dnm
  have b_w : dwE ≤ 56 := ar_dec hdI dw
  have b_g : dgE ≤ 48 := ar_g hdI dg
  have b_dig : ddigE ≤ 69 := ar_dig b_nf b_par b_nm ddig
  have b_car : dcarE ≤ 82 := ar_car hdI b_dig dcar (by omega)
  have b_carw : dcarwE ≤ 82 := ar_car hdI b_dig dcarw (by omega)
  have b_out : doutE ≤ 121 := ar_out hdI hfa hmid hib b_car dout
  have b_wt : dwtE ≤ 100 := ar_wt hdI hS b_carw dwt
  clear hm1' hdg dout dwt dcar dcarw ddig dw dnf dnm dg dpar hfa hmid hib hS hphi h1 h2 h3 h4 h5 h6 h7 h8 hdI hdphi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsz]; omega
  · rw [hW]; omega
  · rw [hcE]; omega
  · rw [hl]; omega
  · rw [hr]; omega

end total
end ECDLP.L86
end
