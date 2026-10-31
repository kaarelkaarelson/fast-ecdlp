import ECDLP.L91_Inst

/-!
# L91 / Disp: `Sy` (binders >= 10, variables < 990, array reads only as `0 < rd`) for the REAL dispatch at `u = 16`
(mirrors L84's `NoRd` development: decodeE, gEx, nfEx, nmEx, wEx, parEx, digE, car gate, kinds of L79 `kindsC`, outEx, wtEx).
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex ECDLP.L73 ECDLP.L68 ECDLP.L64 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

section dispatch

variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc}

/-- the instance expressions are `Sy` -/
structure InstSy (I : InstEx L N0 w B Ctx A 16) : Prop where
  nI : Sy I.nIE
  K' : Sy I.KE
  A' : Sy I.AE
  h' : Sy I.hE
  pb : Sy I.pbE
  b' : Sy I.bE
  nc : Sy I.ncE
  Me : Sy I.MeE

variable {I : InstEx L N0 w B Ctx A 16} (hI : InstSy I)
include hI

theorem Sy_blkLoop : Sy (blkLoop I) := by
  have := hI.nc
  simp only [blkLoop]; sy

theorem Sy_offE {t : Ex} (ht : Sy t) : Sy (offE I t) := by
  have := Sy_blkLoop hI
  simp only [offE]; sy

theorem Sy_kcodeE (xs : ℕ) (hxs : xs < 990) : Sy (kcodeE I xs) := by
  have := hI.nI
  simp only [kcodeE]; sy

theorem Sy_djE (xs : ℕ) (hxs : xs < 990) : Sy (djE I xs) := by
  have := hI.nI
  simp only [djE]; sy

theorem Sy_dsE (xs : ℕ) (hxs : xs < 990) : Sy (dsE I xs) := by
  have := hI.nI
  simp only [dsE]; sy

theorem Sy_decodeE (xs : ℕ) (hxs : xs < 990) {body : Ex} (hb : Sy body) : Sy (decodeE I xs body) := by
  have h1 := hI.nI
  have h2 := hI.A'
  have h3 := hI.h'
  have h4 := hI.pb
  have h5 := hI.K'
  have h6 := hI.Me
  have h7 := hI.nc
  have h8 := hI.b'
  have h9 := Sy_kcodeE hI xs hxs
  have h10 := Sy_djE hI xs hxs
  have h11 := Sy_dsE hI xs hxs
  have h12 := fun {t : Ex} (ht : Sy t) => Sy_offE hI ht
  simp only [decodeE]; sy

theorem Sy_gEx : Sy (gEx I) := by
  have h1 := hI.nI
  have h2 := hI.A'
  have h5 := hI.K'
  have h12 := Sy_offE hI h5
  simp only [gEx]; sy

theorem Sy_nfEx : Sy (nfEx I) := Sy_decodeE hI _ (by norm_num) (by simp only [nprod]; sy)
theorem Sy_nmEx : Sy (nmEx I) := Sy_decodeE hI _ (by norm_num) (by simp only [nprod]; sy)
theorem Sy_wEx : Sy (wEx I) := Sy_decodeE hI _ (by norm_num) (by sy)


variable {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  {Ph : PhiEx L φ B Ctx A 16} (hP : Sy Ph.phiE)
include hP

theorem Sy_parEx : Sy (parEx I φ Ph) := by
  refine Sy_decodeE hI _ (by norm_num) ?_
  have := hP
  simp only [parEx, ECDLP.L73.eqE]; sy

end dispatch

section kinds
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e 16)

structure XSy : Prop where
  nf : Sy X.nfE
  nm : Sy X.nmE
  par : Sy X.parE

variable {X}

theorem Sy_digE (hX : XSy X) (fr tt : ℕ) (h1 : fr < 990) (h2 : tt < 990) : Sy (ECDLP.L68.digE X fr tt) := by
  have := hX.nf; have := hX.nm; have := hX.par
  simp only [ECDLP.L68.digE, ECDLP.L68.ppE, ECDLP.L68.nAE, ECDLP.L68.par2, ECDLP.L68.un1, nprod]; sy

theorem Sy_carIn' (hX : XSy X) {vj vc vr : ℕ} (hj : 10 ≤ vj ∧ vj < 990) (hc : 10 ≤ vc ∧ vc < 990) (hr : 10 ≤ vr ∧ vr < 990)
    {jE pcE pibE body : Ex} (h1 : Sy jE) (h2 : Sy pcE) (h3 : Sy pibE) (h4 : Sy body) :
    Sy (carIn' X vj vc vr jE pcE pibE body) := by
  have := Sy_digE hX 16 17 (by norm_num) (by norm_num)
  obtain ⟨_, _⟩ := hj
  obtain ⟨_, _⟩ := hc
  obtain ⟨_, _⟩ := hr
  simp only [carIn']; sy

theorem Sy_tE (vb vM vj vc vr : ℕ) (h : vb < 990) (h2 : vM < 990) (h3 : vj < 990) (h4 : vc < 990) (h5 : vr < 990) :
    Sy (ECDLP.L68.tE vb vM vj vc vr) := by
  simp only [ECDLP.L68.tE]; sy
theorem Sy_carOutE (vb vM vj vc vr : ℕ) (h : vb < 990) (h2 : vM < 990) (h3 : vj < 990) (h4 : vc < 990) (h5 : vr < 990) :
    Sy (ECDLP.L68.carOutE vb vM vj vc vr) := by
  have := Sy_tE vb vM vj vc vr h h2 h3 h4 h5
  simp only [ECDLP.L68.carOutE]; sy
theorem Sy_carWE (vb vM vj vA2 vc vr : ℕ) (h : vb < 990) (h2 : vM < 990) (h3 : vj < 990) (h4 : vc < 990) (h5 : vr < 990)
    (h6 : vA2 < 990) : Sy (ECDLP.L68.carWE vb vM vj vA2 vc vr) := by
  have := Sy_tE vb vM vj vc vr h h2 h3 h4 h5
  simp only [ECDLP.L68.carWE]; sy


section fam
variable {L : Lay ι ιc}

theorem Sy_guardE {E : Ex} (h : Sy E) : Sy (ECDLP.L79.guardE 16 E) := by
  simp only [ECDLP.L79.guardE]; sy

theorem Sy_phiWrap {phiE : Ex} (hphi : Sy phiE) : Sy (ECDLP.L79.phiWrap 16 phiE) := by
  simp only [ECDLP.L79.phiWrap]; sy

theorem Sy_digCfa : Sy (ECDLP.L79.digCfa 16) := by simp only [ECDLP.L79.digCfa, nprod]; sy
theorem Sy_digCmid : Sy (ECDLP.L79.digCmid 16) := by simp only [ECDLP.L79.digCmid, nprod]; sy
theorem Sy_digCib : Sy (ECDLP.L79.digCib 16) := by simp only [ECDLP.L79.digCib, nprod]; sy

theorem Sy_faKindEC {phiE : Ex} (hphi : Sy phiE) :
    Sy (ECDLP.L79.faKindEC (u := 16) phiE) := by
  have := Sy_digCfa
  simp only [ECDLP.L79.faKindEC, ECDLP.L74.kParams, ECDLP.L79.faOutLD, ECDLP.L79.faInD, ECDLP.L68.faE, ECDLP.L74.faUE,
    mulE, pwE, sumE, natE, nprod]; sy

theorem Sy_midKindEC {nE epsE lE rE : Ex} (hn : Sy nE) (he : Sy epsE) (hl : Sy lE) (hr : Sy rE) :
    Sy (ECDLP.L79.midKindEC (u := 16) nE epsE lE rE) := by
  have := Sy_digCmid
  simp only [ECDLP.L79.midKindEC, ECDLP.L74.kParams2, ECDLP.L74.kParams, ECDLP.L79.midOutLD, ECDLP.L74.midIn,
    ECDLP.L79.midYD, ECDLP.L68.midE, ECDLP.L68.faE, ECDLP.L68.hatYE, ECDLP.L68.hatE, ECDLP.L74.pfaKE,
    mulE, pwE, sumE, natE, nprod]; sy

theorem Sy_ibOutIC : Sy (ECDLP.L79.ibOutIC (u := 16)) := by
  have := Sy_digCib
  simp only [ECDLP.L79.ibOutIC, ECDLP.L79.ibOutL2D, ECDLP.L75.ibE2, ECDLP.L79.ibBodyD, ECDLP.L75.e0I, ECDLP.L75.tEI,
    ECDLP.L75.kEI, ECDLP.L75.pmidEI, ECDLP.L68.hatE, mulE, pwE, sumE, natE, nprod]; sy

end fam

section disp
variable {L : Lay ι ιc} {I : InstEx L N0 w B Ctx A 16} (hI : InstSy I)
  {X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) 16}
  (hX : XSy X)

include hI in
theorem Sy_carJ : Sy (carJ I) := Sy_decodeE hI _ (by norm_num) (by sy)
theorem Sy_carPC : Sy (carPC (u := 16)) := by simp only [carPC]; sy
include hI in
theorem Sy_carPIB : Sy (carPIB I) := Sy_decodeE hI _ (by norm_num) (by sy)
theorem Sy_dqE : Sy (dqE (u := 16)) := by simp only [dqE]; sy

include hI hX in
theorem Sy_carOutX : Sy (carOutX I X) :=
  Sy_carIn' hX (by norm_num) (by norm_num) (by norm_num) (Sy_carJ hI) Sy_carPC (Sy_carPIB hI)
    (Sy_carOutE _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

include hI hX in
theorem Sy_carWX : Sy (carWX I X) := by
  have := Sy_carIn' hX (vj := 16 + 92) (vc := 16 + 93) (vr := 16 + 94) (by norm_num) (by norm_num) (by norm_num) (Sy_carJ hI) Sy_carPC (Sy_carPIB hI)
    (Sy_carWE (16 + 10) (16 + 11) (16 + 92) (16 + 28) (16 + 93) (16 + 94) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  simp only [carWX, carWL']; sy

include hI hX in
theorem Sy_outEx (Kd : Kinds (w := w) (m := m) X) (h1 : Sy Kd.fa.outE) (h2 : Sy Kd.mid.outE) (h3 : Sy Kd.ib.outE) :
    Sy (outEx I X Kd) := by
  refine Sy_decodeE hI _ (by norm_num) ?_
  have := Sy_carOutX hI hX
  have := Sy_dqE
  simp only [outBody, outChain]; sy

include hI hX in
theorem Sy_wtEx (Sw : SrcWt (w := w) X) (hs : Sy Sw.srcE) : Sy (wtEx I X Sw) := by
  refine Sy_decodeE hI _ (by norm_num) ?_
  have := Sy_carWX hI hX
  simp only [wtChain]; sy

end disp
end kinds


end ECDLP.L91
end
