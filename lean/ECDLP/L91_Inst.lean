import ECDLP.L91_Base

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex ECDLP.L83 ECDLP.L76 ECDLP.L73

theorem Sy_pE : Sy pE := by
  simp only [pE, valE, nbitW, bitRd]; sy

theorem Sy_prel {u : ℕ} (hu : u = 16) {b : Ex} (hb : Sy b) : Sy (prel u b) := by
  subst hu; simp only [prel, szE, jm1E, log2E, pE, valE, nbitW, bitRd]; sy

theorem Sy_AEx : Sy (AEx 16) := Sy_prel rfl (by sy)
theorem Sy_hEx : Sy (hEx 16) := Sy_prel rfl (by sy)
theorem Sy_pbEx : Sy (pbEx 16) := Sy_prel rfl (by sy)
theorem Sy_bEx : Sy (bEx 16) := Sy_prel rfl (by sy)
theorem Sy_MEx : Sy (MEx 16) := Sy_prel rfl (by sy)

theorem Sy_sgE (i : Ex) (hi : Sy i) : Sy (ECDLP.L76.sgE lay72 i) := by
  simp only [ECDLP.L76.sgE, ECDLP.L76.pidx, lay72, valE, nbitW, bitRd]; sy

theorem Sy_sgcEx (n cv : ℕ) (h : cv < 990) : Sy (sgcEx n cv) :=
  Sy_sgE (.sub (.var cv) (.lit (17 * n + 11))) (by sy)

theorem Sy_famChain (n cv : ℕ) (hcv : cv < 990) {rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn : Ex}
    (h1 : Sy rg) (h2 : Sy ue) (h3 : Sy cu) (h4 : Sy s0x) (h5 : Sy s0y) (h6 : Sy srx) (h7 : Sy sry) (h8 : Sy e0)
    (h9 : Sy e1) (h10 : Sy e2) (h11 : Sy e3) (h12 : Sy sn) :
    Sy (famChain n cv rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn) := by
  simp only [famChain]; sy

theorem Sy_ncEx (n : ℕ) : Sy (ncEx n 16) := by
  have := Sy_sgcEx n (16 + 22) (by norm_num)
  simp only [ncEx]
  refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> sy

theorem Sy_phiEx (n : ℕ) : Sy (phiEx n 38 39) := by
  have := Sy_sgcEx n 38 (by norm_num)
  simp only [phiEx]
  refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> 
    simp only [tabX, aff, bndE] <;> sy

theorem Sy_nEx (n : ℕ) : Sy (nEx n 31) := by
  have := Sy_sgcEx n 31 (by norm_num)
  simp only [nEx]
  refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> sy

theorem Sy_lEx (n : ℕ) : Sy (lEx n 31 59) := by
  simp only [lEx]
  refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Sy_tabX (by sy) _ _ (Sy_lits _)

theorem Sy_rEx (n : ℕ) : Sy (rEx n 31 59) := by
  simp only [rEx]
  refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Sy_tabX (by sy) _ _ (Sy_lits _)

theorem Sy_epsEx (n : ℕ) : Sy (epsEx n 31 59 16) := by
  have := Sy_MEx
  have h2 := Sy_sgcEx n 31 (by norm_num)
  have hn : Sy (negEx n 31 59) := by
    simp only [negEx]
    refine Sy_famChain n _ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first | exact Sy_tabX (by sy) _ _ (Sy_lits _) | exact Sy_ifLt h2 (Sy_lit _) (Sy_tabX (by sy) _ _ (Sy_lits _)) (Sy_tabX (by sy) _ _ (Sy_lits _))
  simp only [epsEx]
  sy


open ECDLP.L81 ECDLP.L44 ECDLP.L51 in
theorem Sy_srcE (n : ℕ) : Sy (srcE 16 (badE 16 n)) := by
  have hb : Sy bWE := by simp only [bWE, valE, nbitW, bitRd]; sy
  have hcv : ∀ c j, Sy j → Sy (cvBitE lay72 c j) := by
    intro c j hj
    cases c <;> simp only [cvBitE, nbit, nbitW, lay72, c0B, bitRd, valE] <;> sy
  have hc : ∀ c jj nb, Sy jj → Sy nb → Sy (cstIn c jj nb) := fun c jj nb hj hn => by
    simp only [cstIn, ECDLP.L81.eqE]; sy
  have hx : ∀ i jj, Sy i → Sy jj → Sy (xcDefE lay72 i jj) ∧ Sy (xcBitE lay72 i jj) := fun i jj hi hj => by
    simp only [xcDefE, xcBitE, pfDef, pfBit, qOf, ECDLP.L76.pidx, lay72, valE, nbitW, bitRd]
    constructor <;> sy
  simp only [srcE, srcCell, pw2, badE, cstDisp, tgIn, xIn, ECDLP.L81.eqE]
  have hsg : ∀ i, Sy i → Sy (ECDLP.L76.sgE lay72 i) := Sy_sgE
  sy


open ECDLP.L81 ECDLP.L44 ECDLP.L51 in
theorem dp_srcE (n : ℕ) : Ex.dp (srcE 16 (badE 16 n)) ≤ 60 := by
  simp [srcE, srcCell, pw2, badE, cstDisp, cstIn, tgIn, xIn, ECDLP.L81.eqE, bWE, cvBitE, nbit, nbitW, c0B, bitRd, valE, lay72,
    xcDefE, xcBitE, pfDef, pfBit, qOf, ECDLP.L76.sgE, ECDLP.L76.pidx, Ex.dp]

end ECDLP.L91
end
