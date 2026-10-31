import ECDLP.L94_Wt
import ECDLP.L91_Real

/-!
# L94 / Real: depth and `Sy` of `btEx` for the real instance (`u = 16`, node index in variable `20`)
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L91 ECDLP.L79

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {φ : ∀ c, ιc c → ι}

theorem dp_gateBt (u : ℕ) : Ex.dp (gateBt u) ≤ 8 := by
  simp only [gateBt, Ex.dp]; omega

theorem dp_btEx (I : InstEx L N0 w B Ctx A 16) (Ph : PhiEx L φ B Ctx A 16) (xs : ℕ)
    (h1 : Ex.dp I.AE ≤ 21) (h2 : Ex.dp I.hE ≤ 21)
    (h3 : Ex.dp I.pbE ≤ 21) (h4 : Ex.dp I.nIE ≤ 21) (h5 : Ex.dp I.KE ≤ 21) (h6 : Ex.dp I.ncE ≤ 21)
    (h7 : Ex.dp I.MeE ≤ 21) (h8 : Ex.dp I.bE ≤ 21) (hp : Ex.dp Ph.phiE ≤ 21) :
    Ex.dp (btEx I Ph xs) ≤ 40 := by
  have hd := dp_decodeE_le (dI := 21) I xs (gateBt 16) h1 h2 h3 h4 h5 h6 h7 h8
  have hg := dp_gateBt 16
  have := dpT_pos I.AE
  have := dpT_pos I.nIE
  have := dpT_pos I.bE
  have := dpT_pos I.hE
  simp only [btEx, srcBt, occE, ECDLP.L73.eqE, nsum, Ex.dp] at *
  omega

theorem Sy_gateBt : Sy (gateBt 16) := by
  simp only [gateBt]; sy

theorem Sy_btEx (I : InstEx L N0 w B Ctx A 16) (Ph : PhiEx L φ B Ctx A 16) (hI : InstSy I) (hP : Sy Ph.phiE)
    {xs : ℕ} (hxs : xs < 990) : Sy (btEx I Ph xs) := by
  have h1 := hI.nI
  have h2 := hI.A'
  have h3 := hI.h'
  have h5 := hI.K'
  have h7 := hI.nc
  have h8 := hI.b'
  have hd := Sy_decodeE hI xs hxs Sy_gateBt
  have he : ∀ {a b : Ex}, Sy a → Sy b → Sy (ECDLP.L73.eqE a b) := by
    intro a b ha hb; simp only [ECDLP.L73.eqE]; sy
  have hocc : Sy (occE I Ph) := by
    simp only [occE]
    sy
  simp only [btEx, srcBt]
  sy

end
end ECDLP.L94
end
