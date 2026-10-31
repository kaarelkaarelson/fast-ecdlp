import ECDLP.L91_Top

/-!
# L91 / Final: `ExSyn 200` for the edge network `edge_nrep` (L73's `pexEdge`), generic and for the REAL instance
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
  ECDLP.L79 ECDLP.L82 ECDLP.L86

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A 16)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A 16) (hu : B ≤ 16)

/-- **`Sy` side of `ExSyn` for `edge_nrep`** (generic in the instance data): binders `>= 10`, variables `< 990`, array reads only as `0 < rd`,
for the five network expressions and `gEx I`. -/
theorem edge_sy (hI : InstSy I) (hP : Sy Ph.phiE) (hm1 : 1 < m)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (h1 : Sy Kd.fa.outE) (h2 : Sy Kd.mid.outE) (h3 : Sy Kd.ib.outE) (hS : Sy Sw.srcE) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := pexEdge I Ph hu hm1 Kd Sw
    Sy (szEx P) ∧ Sy (WEx P) ∧ Sy (cEx P) ∧ Sy (msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9)) ∧
      Sy (msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)) ∧ Sy P.gE := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  have hX : XSy (pex0 (F := F) (ok := ok) (m := m) I Ph hu) := ⟨Sy_nfEx hI, Sy_nmEx hI, Sy_parEx hI hP⟩
  have hPS : PSy P := ⟨Sy_gEx hI, Sy_nfEx hI, Sy_nmEx hI, Sy_wEx hI, Sy_parEx hI hP,
    Sy_outEx hI hX Kd h1 h2 h3, Sy_wtEx hI hX Sw hS⟩
  have hc := Sy_cEx hPS
  refine ⟨Sy_szEx hPS, Sy_WEx hPS, hc, ?_, ?_, hPS.g⟩
  · exact Sy_msgTest hPS (Sy_mMsg hPS (by norm_num) (by norm_num)) hc (by norm_num) (by norm_num) (by norm_num)
  · exact Sy_msgTest hPS (Sy_mMsg hPS (by norm_num) (by norm_num)) hc (by norm_num) (by norm_num) (by norm_num)


/-- **`ExSyn 200` for `edge_nrep`, generic in the instance data** (`u = 16`).  Depth hypotheses as in L86's `edge_real_dp_le_160`
(with `dI <= 32` so that `gE <= dI + 8 <= 40`); `btE` is a hypothesis. -/
theorem exSyn200_edge (hI : InstSy I) (hP : Sy Ph.phiE) (hm1 : 1 < m)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (h1 : Sy Kd.fa.outE) (h2 : Sy Kd.mid.outE) (h3 : Sy Kd.ib.outE) (hS : Sy Sw.srcE)
    {dI dphi : ℕ} (hdI : dI ≤ 32) (hdphi : dphi ≤ 40)
    (d1 : Ex.dp I.AE ≤ dI) (d2 : Ex.dp I.hE ≤ dI) (d3 : Ex.dp I.pbE ≤ dI) (d4 : Ex.dp I.nIE ≤ dI) (d5 : Ex.dp I.KE ≤ dI)
    (d6 : Ex.dp I.ncE ≤ dI) (d7 : Ex.dp I.MeE ≤ dI) (d8 : Ex.dp I.bE ≤ dI)
    (hphi : Ex.dp Ph.phiE ≤ dphi) (hdS : Ex.dp Sw.srcE ≤ 60)
    (dfa : Ex.dp Kd.fa.outE ≤ 100) (dmid : Ex.dp Kd.mid.outE ≤ 100) (dib : Ex.dp Kd.ib.outE ≤ 100)
    (btE : Ex) (hb : Sy btE) (hdb : Ex.dp btE ≤ 40) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := pexEdge I Ph hu hm1 Kd Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE btE := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := edge_sy I Ph hu hI hP hm1 Kd Sw h1 h2 h3 hS
  obtain ⟨e1, e2, e3, e4, e5⟩ := edge_real_dp_le_160 I Ph hu hm1 Kd Sw (by omega) hdphi d1 d2 d3 d4 d5 d6 d7 d8 hphi hdS dfa dmid dib
  have dg : Ex.dp P.gE ≤ 40 := by
    have := dp_gEx_le I d1 d4 d5 d6
    show Ex.dp (gEx I) ≤ 40
    omega
  exact
    { bsz := s1.1, bW := s2.1, bc := s3.1, bl := s4.1, br := s5.1, bg := s6.1, bb := hb.1
      vE := ⟨s1.2.1, s2.2.1, s3.2.1, s4.2.1, s5.2.1⟩, vg := s6.2.1, vb := hb.2.1
      dsz := le_trans (Nat.add_le_add_right e1 40) (by norm_num), dW := le_trans (Nat.add_le_add_right e2 40) (by norm_num),
      dc := le_trans (Nat.add_le_add_right e3 40) (by norm_num), dl := le_trans (Nat.add_le_add_right e4 40) (by norm_num),
      dr := le_trans (Nat.add_le_add_right e5 40) (by norm_num), dg := dg, db := hdb
      rdE := ⟨s1.2.2, s2.2.2, s3.2.2, s4.2.2, s5.2.2⟩, rdg := s6.2.2, rdb := hb.2.2 }

end
end ECDLP.L91
end
