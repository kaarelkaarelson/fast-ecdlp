import ECDLP.L83_Enum

/-!
# L83 / Used: the used-slot lists are exact (`usedS (formF sg c) = (slotList sg c).toFinset`), duplicate-free, and give the `ecc` ranks
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L83
open Finset ECDLP.L44 ECDLP.L54 ECDLP.L63 Slot Cst

variable {n : ℕ}

theorem usedS_eq (sg : Fin (n + 1) → Sg) (c : Cn n) : usedS (formF sg c) = (slotList sg c).toFinset := by
  ext s
  rw [List.mem_toFinset]
  refine ⟨usedS_sub sg c s, fun h => ?_⟩
  unfold formF
  rw [mem_usedS_mkF]
  cases c <;> simp only [formL, tailT, slotList] at h ⊢ <;> (try split at h) <;> (try split) <;>
    simp_all <;> aesop

theorem slotList_nodup (sg : Fin (n + 1) → Sg) (c : Cn n) : (slotList sg c).Nodup := by
  cases c <;> simp [slotList] <;> (try split) <;> (try simp) <;> (try omega)
  all_goals first
    | (rename_i a; cases a <;> simp [bnd])
    | (simp [Fin.ext_iff])

/-- the number of slots of identity `c` -/
def ncOf (sg : Fin (n + 1) → Sg) (c : Cn n) : ℕ := (slotList sg c).length

theorem card_usedS (sg : Fin (n + 1) → Sg) (c : Cn n) : (usedS (formF sg c)).card = ncOf sg c := by
  rw [usedS_eq, List.toFinset_card_of_nodup (slotList_nodup sg c)]; rfl

end ECDLP.L83
end
