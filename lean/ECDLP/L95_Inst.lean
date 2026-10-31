import ECDLP.L95_Bdd

/-!
# L95 / Inst: FV, NoRd, depth of the rewritten prelude; `instEx2`, `heps_real2`, `kindsReal2'`
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83 ECDLP.L84 ECDLP.L90

section fv
theorem fv_szE2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (szE2 u) := by
  simp [szE2, nsum, nbitW, bitRd, Ex.FV, h0]

theorem fv_log2E2 (u : ℕ) (s : ℕ → Prop) (x : Ex) (hx : Ex.FV s x) : Ex.FV s (log2E2 u x) := by
  have := Ex.FV_mono (s := s) (s' := fun y => s y ∨ y = u + 60) (fun y hy => Or.inl hy) x hx
  simp [log2E2, nsum, Ex.FV, hx, this]

theorem fv_prel2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) (body : Ex)
    (hb : Ex.FV (fun y => (((((s y ∨ y = u + 63) ∨ y = u + 64) ∨ y = u + 65) ∨ y = u + 66) ∨ y = u + 67)) body) :
    Ex.FV s (prel2 u body) := by
  have h1 := fv_szE2 u s h0
  have h2 : Ex.FV (fun y => s y ∨ y = u + 63) (jm1E2 u) := by
    have := fv_log2E2 u (fun y => s y ∨ y = u + 63) (.var (u + 63)) (by simp [Ex.FV])
    simp only [jm1E2, Ex.FV]
    simp [this]
  simp only [prel2, Ex.FV]
  refine ⟨h1, h2, ?_, ?_, ?_, hb⟩
  all_goals simp [pow2, Ex.FV]

theorem fv_AEx2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (AEx2 u) :=
  fv_prel2 u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_hEx2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (hEx2 u) :=
  fv_prel2 u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_pbEx2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (pbEx2 u) :=
  fv_prel2 u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_bEx2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (bEx2 u) :=
  fv_prel2 u s h0 _ (by simp [Ex.FV])
theorem fv_MEx2 (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (MEx2 u) :=
  fv_prel2 u s h0 _ (by simp [Ex.FV])

theorem fv_epsEx2 (n cv tv u : ℕ) (s : ℕ → Prop) (h0 : s 0) (hc : s cv) (ht : s tv) : Ex.FV s (epsEx2 u n cv tv) := by
  have h1 := fv_negEx s n cv tv h0 hc ht
  have h2 := fv_MEx2 u s h0
  simp only [epsEx2, pow2, Ex.FV]
  simp [h1, h2]
end fv

section norD
variable (n u : ℕ)

theorem NoRd_szE2 : NoRd Out (szE2 u) := by
  simp [szE2, nsum, nbitW, bitRd, NoRd, Out]

theorem NoRd_log2E2 (x : Ex) (hx : NoRd Out x) : NoRd Out (log2E2 u x) := by
  simp [log2E2, nsum, NoRd, hx]

theorem NoRd_jm1E2 : NoRd Out (jm1E2 u) := by
  have := NoRd_log2E2 u (.var (u + 63)) trivial
  simp only [jm1E2, NoRd, and_true]; exact this

theorem NoRd_prel2 (body : Ex) (hb : NoRd Out body) : NoRd Out (prel2 u body) := by
  simp [prel2, NoRd, NoRd_szE2, NoRd_jm1E2, pow2, pw2, hb]

theorem NoRd_AEx2 : NoRd Out (AEx2 u) := NoRd_prel2 u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_hEx2 : NoRd Out (hEx2 u) := NoRd_prel2 u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_pbEx2 : NoRd Out (pbEx2 u) := NoRd_prel2 u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_bEx2 : NoRd Out (bEx2 u) := NoRd_prel2 u _ (by simp [NoRd])
theorem NoRd_MEx2 : NoRd Out (MEx2 u) := NoRd_prel2 u _ (by simp [NoRd])

theorem NoRd_epsEx2 (cv tv : ℕ) : NoRd Out (epsEx2 u n cv tv) := by
  simp [epsEx2, NoRd, NoRd_negEx, pow2, pw2, NoRd_MEx2]
end norD

section depth
theorem dp_epsEx2 (n cv tv u : ℕ) : Ex.dp (epsEx2 u n cv tv) ≤ 22 := by
  simp [epsEx2, negEx, MEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, famChain, tabX, lits, sgcEx, ECDLP.L76.sgE,
    ECDLP.L76.pidx, lay72, valE, nbitW, bitRd, Ex.dp]
theorem dp_AEx2 (u : ℕ) : Ex.dp (AEx2 u) ≤ 11 := by
  simp [AEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, nbitW, bitRd, Ex.dp]
theorem dp_hEx2 (u : ℕ) : Ex.dp (hEx2 u) ≤ 11 := by
  simp [hEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, nbitW, bitRd, Ex.dp]
theorem dp_pbEx2 (u : ℕ) : Ex.dp (pbEx2 u) ≤ 11 := by
  simp [pbEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, nbitW, bitRd, Ex.dp]
theorem dp_bEx2 (u : ℕ) : Ex.dp (bEx2 u) ≤ 11 := by
  simp [bEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, nbitW, bitRd, Ex.dp]
theorem dp_MEx2 (u : ℕ) : Ex.dp (MEx2 u) ≤ 12 := by
  simp [MEx2, prel2, szE2, jm1E2, log2E2, nsum, pow2, nbitW, bitRd, Ex.dp]
end depth

end ECDLP.L95
end
