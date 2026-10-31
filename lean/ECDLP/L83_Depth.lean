import ECDLP.L83_Kinds

/-!
# L83 / Depth: exact `Ex.dp` of the instance expressions and oracles (they do not depend on the numeral arguments; proved by `rfl`)

ExSyn budget (L79): fa kind `max 20 (dp phiE + 10)`, mid kind `d + 25` for oracle depth `d >= 8`, `dp_parEx_le`: `max (dI+16) (dp phiE + 23) 29`.
Here: `dp phiE = 21`, `dI = 21` (ncEx; the others `<= 12`), mid oracles `<= 22`.
-/
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
noncomputable section
namespace ECDLP.L83
open Factoring.Aux Ex ECDLP.L76

theorem dp_phiEx (n cv ev : ℕ) : Ex.dp (phiEx n cv ev) = 21 := by
  simp [phiEx, famChain, tabX, aff, bndE, sgcEx, ECDLP.L76.sgE, ECDLP.L76.pidx, lay72, valE, nbitW, bitRd, Ex.dp]
theorem dp_nEx (n cv : ℕ) : Ex.dp (nEx n cv) = 21 := by
  simp [nEx, famChain, sgcEx, ECDLP.L76.sgE, ECDLP.L76.pidx, lay72, valE, nbitW, bitRd, Ex.dp]
theorem dp_ncEx (n u : ℕ) : Ex.dp (ncEx n u) = 21 := by
  simp [ncEx, famChain, sgcEx, ECDLP.L76.sgE, ECDLP.L76.pidx, lay72, valE, nbitW, bitRd, Ex.dp]
theorem dp_lEx (n cv tv : ℕ) : Ex.dp (lEx n cv tv) = 11 := by
  simp [lEx, famChain, tabX, lits, Ex.dp]
theorem dp_rEx (n cv tv : ℕ) : Ex.dp (rEx n cv tv) = 11 := by
  simp [rEx, famChain, tabX, lits, Ex.dp]
theorem dp_epsEx (n cv tv u : ℕ) : Ex.dp (epsEx n cv tv u) = 22 := by
  simp [epsEx, negEx, MEx, prel, szE, jm1E, log2E, pE, nsum, pow2, famChain, tabX, lits, sgcEx, ECDLP.L76.sgE,
    ECDLP.L76.pidx, lay72, valE, nbitW, bitRd, Ex.dp]
theorem dp_AEx (u : ℕ) : Ex.dp (AEx u) = 11 := rfl
theorem dp_hEx (u : ℕ) : Ex.dp (hEx u) = 11 := rfl
theorem dp_pbEx (u : ℕ) : Ex.dp (pbEx u) = 11 := rfl
theorem dp_bEx (u : ℕ) : Ex.dp (bEx u) = 11 := rfl
theorem dp_MEx (u : ℕ) : Ex.dp (MEx u) = 12 := rfl

end ECDLP.L83
end
