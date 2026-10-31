import ECDLP.L79_Depth

/-!
# L82 / Floor: the depth floor of the real mid output expression and the dispatch
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L82
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (midKindE)
open ECDLP.L79

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- **Exact depth of the guarded mid expression as a function of the digit depth `δ`** (`δ >= 6`, shallow oracles). -/
theorem dp_mid_delta (nE epsE lE rE : Ex) {δ : ℕ} (hδ : Ex.dp (digE X u (u + 1)) = δ) (h6 : 6 ≤ δ)
    (hl : Ex.dp lE ≤ δ + 2) (hr : Ex.dp rE ≤ δ + 2) (he : Ex.dp epsE ≤ δ + 8) (hn : Ex.dp nE ≤ δ + 10) :
    Ex.dp (guardE u (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE)) = δ + 24 := by
  have := dp_midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE
  have h1 := dpT_pos nE
  rw [dp_midKindE]
  rw [hδ]
  omega

/-- **Floor**: whatever the digit expression and the four oracles are, the guarded mid expression has depth `>= 30`. -/
theorem dp_mid_floor (nE epsE lE rE : Ex) :
    30 ≤ Ex.dp (guardE u (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE)) := by
  have h1 := dpT_pos nE
  have h2 := dpT_pos epsE
  have h3 := dpT_pos lE
  have h4 := dpT_pos rE
  have h5 := dpT_pos (digE X u (u + 1))
  rw [dp_midKindE]
  omega

end
end ECDLP.L82
end
