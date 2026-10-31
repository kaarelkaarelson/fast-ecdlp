import ECDLP.L90_Kind
import ECDLP.L83_Kinds

/-!
# L90 / Real: `kindsReal'` -- L79's repaired kinds for the REAL network with NO `hne` hypothesis

`hne_real`: for every identity, either the slot list is nonempty or the form has no term (a sign identity without a sign requirement has both empty).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

/-- **the weakened `hne` holds for every prefix**: nonempty slot list, or no term -/
theorem hne_real (sg : Fin (n + 1) → Sg) (c : Fin (18 * n + 12)) :
    0 < (layOf sg).nc c ∨ (frF sg (cnEquiv n) c).n = 0 := by
  show 0 < (slotList sg ((cnEquiv n).symm c)).length ∨ (formL sg ((cnEquiv n).symm c)).length = 0
  cases (cnEquiv n).symm c with
  | sign i =>
    cases hs : sg i
    · right; simp [formL, hs]
    · left; simp [slotList, hs]
    · left; simp [slotList, hs]
  | _ => left; simp [slotList]

/-- **`Kinds` of the real network, for every prefix** (no `hne`). Label: LEAN. -/
def kindsReal' (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop) :
    Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu) :=
  kindsC' (instEx (n := n) u hB hR) (phiExInst u hB hR) hu (fun c => M_pos c) (hne_real (sgR n ℓ π)) (fun c => wP_pos _)
    (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)

/-- the kind expressions of `kindsReal'` -/
theorem kindsReal'_outE (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop) :
    (kindsReal' (ℓ := ℓ) (π := π) hB hR hu m ok).fa.outE =
        ECDLP.L79.guardE u (ECDLP.L79.faKindEC (u := u) (ECDLP.L79.phiWrap u (phiExInst (n := n) u hB hR).phiE)) ∧
    (kindsReal' (ℓ := ℓ) (π := π) hB hR hu m ok).mid.outE =
        ECDLP.L79.guardE u (ECDLP.L79.midKindEC (u := u) (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u)
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))) ∧
    (kindsReal' (ℓ := ℓ) (π := π) hB hR hu m ok).ib.outE = ECDLP.L79.ibOutIC (u := u) := ⟨rfl, rfl, rfl⟩

end
end ECDLP.L90
end
