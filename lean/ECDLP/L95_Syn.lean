import ECDLP.L95_Real
import ECDLP.L91_Real
import ECDLP.L89_Rep

/-!
# L95 / Syn: `Sy`, depth and `ExSyn 200` for the REPAIRED real instance, with the CLAMPED dispatch (`clampPEx`)

* `Sy_*2`: syntactic side (binders >= 10, variables < 990, reads only as `0 < rd`) of `szE2 .. epsEx2` at `u = 16`.
* `edgeC_sy`, `edgeC_dp`: generic (any `InstEx` at `u = 16` with the L91/L86 hypotheses) for `pexEdgeC = clampPEx (pexEdge ..)`.
* `exSyn200_real2C`: **`ExSyn 200` for the clamped network built from `instEx2`**; only `btE` is a hypothesis.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L83 ECDLP.L76 ECDLP.L73 ECDLP.L91

section sy
theorem Sy_szE2 : Sy (szE2 16) := by
  simp only [szE2, nsum, nbitW, bitRd]; sy

theorem Sy_log2E2 : Sy (log2E2 16 (.var 79)) := by
  simp only [log2E2, nsum]; sy

theorem Sy_prel2 {u : ℕ} (hu : u = 16) {b : Ex} (hb : Sy b) : Sy (prel2 u b) := by
  subst hu; simp only [prel2, szE2, jm1E2, log2E2, nsum, nbitW, bitRd]; sy

theorem Sy_AEx2 : Sy (AEx2 16) := Sy_prel2 rfl (by sy)
theorem Sy_hEx2 : Sy (hEx2 16) := Sy_prel2 rfl (by sy)
theorem Sy_pbEx2 : Sy (pbEx2 16) := Sy_prel2 rfl (by sy)
theorem Sy_bEx2 : Sy (bEx2 16) := Sy_prel2 rfl (by sy)
theorem Sy_MEx2 : Sy (MEx2 16) := Sy_prel2 rfl (by sy)

theorem Sy_epsEx2 (n : ℕ) : Sy (epsEx2 16 n 31 59) := by
  have := Sy_MEx2
  have h2 := Sy_sgcEx n 31 (by norm_num)
  have hn : Sy (negEx n 31 59) := by
    simp only [negEx]
    refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first | exact Sy_tabX (by sy) _ _ (Sy_lits _) | exact Sy_ifLt h2 (Sy_lit _) (Sy_tabX (by sy) _ _ (Sy_lits _)) (Sy_tabX (by sy) _ _ (Sy_lits _))
  simp only [epsEx2]
  sy

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (hu : B ≤ 16)

theorem instSy_real2 : InstSy (instEx2 (n := n) 16 hB hR) :=
  ⟨Sy_lit _, Sy_lit _, Sy_AEx2, Sy_hEx2, Sy_pbEx2, Sy_bEx2, Sy_ncEx n, Sy_MEx2⟩

theorem kinds_real2_sy (n : ℕ) :
    Sy (ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39)))) ∧
    Sy (ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx2 16 n 31 59) (lEx n 31 59) (rEx n 31 59))) ∧
    Sy (ECDLP.L79.ibOutIC (u := 16)) :=
  ⟨Sy_guardE (Sy_faKindEC (Sy_phiWrap (Sy_phiEx n))),
   Sy_guardE (Sy_midKindEC (Sy_nEx n) (Sy_epsEx2 n) (Sy_lEx n) (Sy_rEx n)), Sy_ibOutIC⟩

theorem kinds_real2_dp (n : ℕ) :
    Ex.dp (ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39)))) ≤ 100 ∧
    Ex.dp (ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx2 16 n 31 59) (lEx n 31 59) (rEx n 31 59))) ≤ 100 ∧
    Ex.dp (ECDLP.L79.ibOutIC (u := 16)) ≤ 100 := by
  have h1 := ECDLP.L79.dp_faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39))
  have h2 := ECDLP.L79.dp_midKindEC_le (u := 16) (d := 75) (by norm_num) (nEx n 31) (epsEx2 16 n 31 59) (lEx n 31 59) (rEx n 31 59)
    (by rw [dp_nEx]; norm_num) (by have := dp_epsEx2 n 31 59 16; omega) (by rw [dp_lEx]; norm_num) (by rw [dp_rEx]; norm_num)
  have h3 := ECDLP.L79.dp_ibOutIC (u := 16)
  have hp : Ex.dp (ECDLP.L79.phiWrap 16 (phiEx n 38 39)) = 23 := by
    simp only [ECDLP.L79.phiWrap, Ex.dp, dp_phiEx]; norm_num
  rw [hp] at h1
  refine ⟨by omega, by omega, by omega⟩

end
end sy

/-! ### the clamped dispatch -/
section clamp
open ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L79 ECDLP.L82 ECDLP.L86

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A 16)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A 16) (hu : B ≤ 16)

/-- **`Sy` side of `ExSyn` for the CLAMPED edge network** `pexEdgeC` (generic in the instance data) -/
theorem edgeC_sy (hI : InstSy I) (hP : Sy Ph.phiE) (hm1 : 1 < m)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (h1 : Sy Kd.fa.outE) (h2 : Sy Kd.mid.outE) (h3 : Sy Kd.ib.outE) (hS : Sy Sw.srcE) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := ECDLP.L89.pexEdgeC I Ph hu hm1 Kd Sw
    Sy (szEx P) ∧ Sy (WEx P) ∧ Sy (cEx P) ∧ Sy (msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9)) ∧
      Sy (msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)) ∧ Sy P.gE := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  have hX : XSy (pex0 (F := F) (ok := ok) (m := m) I Ph hu) := ⟨Sy_nfEx hI, Sy_nmEx hI, Sy_parEx hI hP⟩
  have hPS0 : PSy (pexEdge I Ph hu hm1 Kd Sw) := ⟨Sy_gEx hI, Sy_nfEx hI, Sy_nmEx hI, Sy_wEx hI, Sy_parEx hI hP,
    Sy_outEx hI hX Kd h1 h2 h3, Sy_wtEx hI hX Sw hS⟩
  have hPS : PSy P := by
    refine ⟨hPS0.g, hPS0.nf, hPS0.nm, hPS0.w, hPS0.par, ?_, hPS0.wt⟩
    show Sy (ECDLP.L89.clampE (pexEdge I Ph hu hm1 Kd Sw))
    exact Sy_mod hPS0.out (Sy_un1 (X := pexEdge I Ph hu hm1 Kd Sw) (by norm_num) hPS0.nm)
  have hc := Sy_cEx hPS
  refine ⟨Sy_szEx hPS, Sy_WEx hPS, hc, ?_, ?_, hPS.g⟩
  · exact Sy_msgTest hPS (Sy_mMsg hPS (by norm_num) (by norm_num)) hc (by norm_num) (by norm_num) (by norm_num)
  · exact Sy_msgTest hPS (Sy_mMsg hPS (by norm_num) (by norm_num)) hc (by norm_num) (by norm_num) (by norm_num)

end
section genPEx
variable {m' B' g : ℕ} {Ctx' : (ℕ → ℕ) → Prop} {A' : ℕ → ℕ → ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
  {P' : ECDLP.L56.PForced (ZMod m') ι'} {E' : ∀ i, P'.Msg i ≃ Fin (Fintype.card (P'.Msg i))}
  {EF' : ∀ i, P'.Free i ≃ Fin (Fintype.card (P'.Free i))} {e' : ι' ≃ Fin g} [hF' : ∀ i, Nonempty (P'.Free i)] {u' : ℕ}
  (Xp : PEx (B := B') (Ctx := Ctx') (A := A') P' E' EF' e' u')

/-- the five `E` expressions of any `PEx` have depth `<= 160` once its fields are bounded -/
theorem dp5_le_160 (hpar : Ex.dp Xp.parE ≤ 63) (hnf : Ex.dp Xp.nfE ≤ 56) (hnm : Ex.dp Xp.nmE ≤ 56) (hw : Ex.dp Xp.wE ≤ 56)
    (hg : Ex.dp Xp.gE ≤ 48) (hout : Ex.dp Xp.outE ≤ 122) (hwt : Ex.dp Xp.wtE ≤ 100) (fr tt vq x : ℕ) :
    Ex.dp (ECDLP.L64.szEx Xp) ≤ 160 ∧ Ex.dp (ECDLP.L64.WEx Xp) ≤ 160 ∧ Ex.dp (ECDLP.L64.cEx Xp) ≤ 160 ∧
      Ex.dp (msgTest (ECDLP.L64.mMsg Xp fr tt) (ECDLP.L64.cEx Xp) vq x) ≤ 160 := by
  have h1 := dp_cEx' Xp
  have h2 := dp_szEx' Xp
  have h3 := dp_WEx' Xp
  have h4 := dp_digE' Xp fr tt
  have h5 := dp_msgTest_eq Xp (ECDLP.L64.cEx Xp) fr tt vq x
  rw [h4] at h5
  have := dpT_pos Xp.parE
  have := dpT_pos Xp.wE
  omega

end genPEx

variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A 16)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A 16) (hu : B ≤ 16)

/-- **depth of the CLAMPED edge network's five `E` expressions** (hypotheses as in L86's `edge_real_dp_le_160`; the clamp costs `+2` in `outE`) -/
theorem edgeC_dp (hm1 : 1 < m) (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    {dI dphi : ℕ} (hdI : dI ≤ 40) (hdphi : dphi ≤ 40)
    (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI) (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI)
    (h6 : Ex.dp I.ncE ≤ dI) (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI)
    (hphi : Ex.dp Ph.phiE ≤ dphi) (hS : Ex.dp Sw.srcE ≤ 60)
    (hfa : Ex.dp Kd.fa.outE ≤ 100) (hmid : Ex.dp Kd.mid.outE ≤ 100) (hib : Ex.dp Kd.ib.outE ≤ 100) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    let P := ECDLP.L89.pexEdgeC I Ph hu hm1 Kd Sw
    Ex.dp (szEx P) ≤ 160 ∧ Ex.dp (WEx P) ≤ 160 ∧ Ex.dp (cEx P) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9)) ≤ 160 ∧
      Ex.dp (msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)) ≤ 160 := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  have dg := dp_gEx_le I h1 h4 h5 h6
  have dnf := dp_nfEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dnm := dp_nmEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dw := dp_wEx_le I h1 h2 h3 h4 h5 h6 h7 h8
  have dpar := dp_parEx_le I Ph h1 h2 h3 h4 h5 h6 h7 h8
  have dout := dp_outEx_real I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd h1 h2 h3 h4 h5 h6 h7 h8
  have dwt := dp_wtEx_real I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw h1 h2 h3 h4 h5 h6 h7 h8
  have dcar := dp_carOutX_le I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) h1 h2 h3 h4 h5 h6 h7 h8
  have dcarw := dp_carWX_le I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) h1 h2 h3 h4 h5 h6 h7 h8
  have ddig : Ex.dp (ECDLP.L68.digE (pex0 (F := F) (ok := ok) (m := m) I Ph hu) 16 (16 + 1)) =
      max (max (Ex.dp (nfEx I) + 4) (Ex.dp (parEx I φ Ph) + 6)) (Ex.dp (nmEx I) + 5) :=
    dp_digE L (pex0 (F := F) (ok := ok) (m := m) I Ph hu) 16 (16 + 1)
  have b_par : Ex.dp (parEx I φ Ph) ≤ 63 := ar_par hdI hdphi hphi dpar
  have b_nf : Ex.dp (nfEx I) ≤ 56 := ar_dec hdI dnf
  have b_nm : Ex.dp (nmEx I) ≤ 56 := ar_dec hdI dnm
  have b_w : Ex.dp (wEx I) ≤ 56 := ar_dec hdI dw
  have b_g : Ex.dp (gEx I) ≤ 48 := ar_g hdI dg
  have b_dig : Ex.dp (ECDLP.L68.digE (pex0 (F := F) (ok := ok) (m := m) I Ph hu) 16 (16 + 1)) ≤ 69 := ar_dig b_nf b_par b_nm ddig
  have b_car := ar_car hdI b_dig dcar (by omega)
  have b_carw := ar_car hdI b_dig dcarw (by omega)
  have b_out : Ex.dp (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) ≤ 121 := ar_out hdI hfa hmid hib b_car dout
  have b_wt : Ex.dp (wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw) ≤ 100 := ar_wt hdI hS b_carw dwt
  have hun : Ex.dp (ECDLP.L64.un1 (pexEdge I Ph hu hm1 Kd Sw) (16 + 5) (pexEdge I Ph hu hm1 Kd Sw).nmE) = Ex.dp (nmEx I) + 1 :=
    dp_un1' _ _ _
  have b_outC : Ex.dp P.outE ≤ 122 := by
    show Ex.dp (Ex.mod (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd)
      (ECDLP.L64.un1 (pexEdge I Ph hu hm1 Kd Sw) (16 + 5) (pexEdge I Ph hu hm1 Kd Sw).nmE)) ≤ 122
    simp only [Ex.dp]
    have : Ex.dp (ECDLP.L64.un1 (pexEdge I Ph hu hm1 Kd Sw) (16 + 5) (pexEdge I Ph hu hm1 Kd Sw).nmE) ≤ 57 := by omega
    omega
  obtain ⟨c1, c2, c3, c4⟩ := dp5_le_160 P b_par b_nf b_nm b_w b_g b_outC b_wt 16 (16 + 1) (16 + 3) (16 + 9)
  obtain ⟨_, _, _, c5⟩ := dp5_le_160 P b_par b_nf b_nm b_w b_g b_outC b_wt (16 + 1) 16 (16 + 3) (16 + 9)
  exact ⟨c1, c2, c3, c4, c5⟩

/-- **`ExSyn 200` for the CLAMPED `edge_nrepC`, generic in the instance data** (`u = 16`; hypotheses as L91's `exSyn200_edge`). -/
theorem exSyn200_edgeC (hI : InstSy I) (hP : Sy Ph.phiE) (hm1 : 1 < m)
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
    let P := ECDLP.L89.pexEdgeC I Ph hu hm1 Kd Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE btE := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  intro P
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := edgeC_sy I Ph hu hI hP hm1 Kd Sw h1 h2 h3 hS
  obtain ⟨e1, e2, e3, e4, e5⟩ := edgeC_dp I Ph hu hm1 Kd Sw (by omega) hdphi d1 d2 d3 d4 d5 d6 d7 d8 hphi hdS dfa dmid dib
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

end clamp

section real
open ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 ECDLP.L64 Slot Cst ECDLP.L90
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (hu : B ≤ 16)
  {m : ℕ} (hm1 : 1 < m) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)

/-- **`ExSyn 200` for the CLAMPED REAL network built from the repaired instance `instEx2`** (`u = 16`).  Only `btE` is a hypothesis.
(L91's `exSyn200_real` was for the unclamped network and the old `szE`; this one is for `pexEdgeC (instEx2 ..)`.) -/
theorem exSyn200_real2C
    (Kd : Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) 16 hB hR) (phiExInst 16 hB hR) hu))
    (hfa : Kd.fa.outE = ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39))))
    (hmid : Kd.mid.outE = ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx2 16 n 31 59) (lEx n 31 59) (rEx n 31 59)))
    (hib : Kd.ib.outE = ECDLP.L79.ibOutIC (u := 16))
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) 16 hB hR) (phiExInst 16 hB hR) hu))
    (hSw : Sw.srcE = srcE 16 (badE 16 n))
    (btE : Ex) (hb : Sy btE) (hdb : Ex.dp btE ≤ 40) :
    haveI := edge_free_nonempty (w := fun _ => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m
    let P := ECDLP.L89.pexEdgeC (instEx2 (n := n) 16 hB hR) (phiExInst 16 hB hR) hu hm1 Kd Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE btE := by
  obtain ⟨k1, k2, k3⟩ := kinds_real2_sy n
  obtain ⟨q1, q2, q3⟩ := kinds_real2_dp n
  have hphi : Sy (phiExInst (n := n) (A := A) (Ctx := Ctx) (p := p) (a := a) (b := b) (X := X) (xR := xR) (yR := yR) (π := π) (ℓ := ℓ) (bW := bW) 16 hB hR).phiE := Sy_phiEx n
  refine exSyn200_edgeC (instEx2 (n := n) 16 hB hR) (phiExInst 16 hB hR) hu (instSy_real2 hB hR) hphi hm1 Kd Sw
    (hfa ▸ k1) (hmid ▸ k2) (hib ▸ k3) (hSw ▸ Sy_srcE n) (dI := 21) (dphi := 21) (by norm_num) (by norm_num)
    (by show Ex.dp (AEx2 16) ≤ 21; have := dp_AEx2 16; omega) (by show Ex.dp (hEx2 16) ≤ 21; have := dp_hEx2 16; omega)
    (by show Ex.dp (pbEx2 16) ≤ 21; have := dp_pbEx2 16; omega) (by simp [instEx2, Ex.dp])
    (by simp [instEx2, Ex.dp]) (by show Ex.dp (ncEx n 16) ≤ 21; rw [dp_ncEx]) (by show Ex.dp (MEx2 16) ≤ 21; have := dp_MEx2 16; omega)
    (by show Ex.dp (bEx2 16) ≤ 21; have := dp_bEx2 16; omega) (by show Ex.dp (phiEx n (16 + 22) (16 + 23)) ≤ 21; rw [dp_phiEx])
    (by rw [hSw]; exact dp_srcE n)
    (hfa ▸ q1) (hmid ▸ q2) (hib ▸ q3) btE hb hdb

end real

end ECDLP.L95
end
