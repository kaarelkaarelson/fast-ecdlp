import ECDLP.L95_Real
import ECDLP.L90_NoRd

/-!
# L95 / NoRd: array-3 / array->=12 independence of the dispatch of the REPAIRED real instance (`instEx2`, `epsEx2`, `kindsReal2'`)
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L84 ECDLP.L83 ECDLP.L90

section real
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

theorem instNoRd_real2 : InstNoRd Out (instEx2 (n := n) (ℓ := ℓ) (π := π) u hB hR) :=
  ⟨trivial, trivial, NoRd_AEx2 u, NoRd_hEx2 u, NoRd_pbEx2 u, NoRd_bEx2 u, NoRd_ncEx n u, NoRd_MEx2 u⟩

/-- **the repaired real dispatch reads neither array 3 nor an array >= 12** (`Sw.srcE` being the only hypothesis) -/
theorem NoRd_dispatchReal2 (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu))
    (hs : NoRd Out Sw.srcE) :
    NoRd Out (outEx (instEx2 (n := n) (ℓ := ℓ) (π := π) u hB hR)
        (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu)
        (kindsReal2' (ℓ := ℓ) (π := π) hB hR hu m ok)) ∧
      NoRd Out (wtEx (instEx2 (n := n) (ℓ := ℓ) (π := π) u hB hR)
        (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu) Sw) :=
  NoRd_dispatchC' hu (instNoRd_real2 hB hR) (NoRd_phiExInst hB hR) (fun c => M_pos c) (hne_real (sgR n ℓ π))
    (fun c => wP_pos _) (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43)) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx2 n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real2 hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)
    (NoRd_nEx n _) (NoRd_epsEx2 n u _ _) (NoRd_lEx n _ _) (NoRd_rEx n _ _) Sw hs

end real
end ECDLP.L95
end
