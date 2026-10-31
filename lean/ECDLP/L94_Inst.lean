import ECDLP.L94_Real
import ECDLP.L94_Bdd
import ECDLP.L90_NoRd

/-!
# L94 / Inst: `btReal` for the REAL network (`u = 16`, node index in variable `20`): Sy, depth, NoRd (arrays 3 and >= 12), evaluation
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 ECDLP.L64
  ECDLP.L83 ECDLP.L84 ECDLP.L91 ECDLP.L90 Slot Cst

theorem NoRd_btEx {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
    {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
    {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι} {a : ℕ → Prop} {I : InstEx L N0 w B Ctx A u} (hI : InstNoRd a I)
    {Ph : PhiEx L φ B Ctx A u} (hP : NoRd a Ph.phiE) (xs : ℕ) : NoRd a (btEx I Ph xs) := by
  have hd := NoRd_decodeE hI xs (body := gateBt u) (by simp [gateBt, NoRd])
  have hocc : NoRd a (occE I Ph) := by
    simp only [occE]
    refine NoRd_nsum hI.K' ?_
    simp only [NoRd, true_and]
    exact NoRd_nsum hI.nc (NoRd_eqE73 hP (by simp [NoRd]))
  simp only [btEx, srcBt, NoRd, hocc, hI.A', hI.nI, hI.b', hI.h', hd, true_and, and_true]

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW)

/-- **the weight expression of the real network** (`u = 16`, node in variable 20) -/
def btReal (n : ℕ) (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) : Ex :=
  btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) 20

theorem sy_btReal : Sy (btReal (A := A) (p := p) (a := a) (b := b) (X := X) (xR := xR) (yR := yR) (π := π) (ℓ := ℓ) (bW := bW) n hB hR) :=
  Sy_btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) (instSy_real hB hR) (Sy_phiEx n) (by norm_num)

theorem dp_btReal : Ex.dp (btReal (A := A) (p := p) (a := a) (b := b) (X := X) (xR := xR) (yR := yR) (π := π) (ℓ := ℓ) (bW := bW) n hB hR) ≤ 40 :=
  dp_btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) 20 (dp_AEx 16 ▸ (by norm_num)) (dp_hEx 16 ▸ (by norm_num))
    (dp_pbEx 16 ▸ (by norm_num)) (by simp [instEx, Ex.dp]) (by simp [instEx, Ex.dp])
    (by show Ex.dp (ncEx n 16) ≤ 21; rw [dp_ncEx]) (by show Ex.dp (MEx 16) ≤ 21; rw [dp_MEx]; norm_num)
    (dp_bEx 16 ▸ (by norm_num)) (by show Ex.dp (phiEx n (16 + 22) (16 + 23)) ≤ 21; rw [dp_phiEx])

theorem noRd_btReal : ECDLP.L84.NoRd ECDLP.L84.Out (btReal (A := A) (p := p) (a := a) (b := b) (X := X) (xR := xR) (yR := yR) (π := π) (ℓ := ℓ) (bW := bW) n hB hR) :=
  NoRd_btEx (instNoRd_real hB hR) (NoRd_phiExInst hB hR) 20

end
end ECDLP.L94
end
