import ECDLP.L83_Fv
import ECDLP.L79_AsmC

/-!
# L83 / Kinds: L79's `kindsC` instantiated for the real network (with the ONE remaining hypothesis `hne`)
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

theorem instFV_real : ECDLP.L79.InstFV (instEx (n := n) u hB hR) :=
  ⟨fv_AEx u _ (by omega), fv_hEx u _ (by omega), fv_pbEx u _ (by omega), trivial, trivial, fv_bEx u _ (by omega),
    fv_ncEx n u _ (by omega) (Or.inr rfl), fv_MEx u _ (by omega)⟩

theorem M_pos (c : Fin (18 * n + 12)) : 1 ≤ (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M := by
  show 1 ≤ 2 ^ (kP (Nat.size p)) * wP (Nat.size p)
  exact Nat.mul_pos (Nat.two_pow_pos _) (wP_pos _)

/-- **`Kinds` of the real network** (fa, mid, ib guarded/closed-form kinds of L79), under the single hypothesis `hne` -/
def kindsReal (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)
    (hne : ∀ c : Fin (18 * n + 12), 0 < (layOf (sgR n ℓ π)).nc c) :
    Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu) :=
  ECDLP.L79.kindsC (instEx (n := n) u hB hR) (phiExInst u hB hR) hu (fun c => M_pos c) hne (fun c => wP_pos _)
    (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega)) (hn_real hB hR hu) (heps_real hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)

end
end ECDLP.L83
end
