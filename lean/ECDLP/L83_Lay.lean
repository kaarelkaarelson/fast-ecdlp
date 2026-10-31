import ECDLP.L83_Used
import ECDLP.L73_Lay

/-!
# L83 / Lay: L73's `Lay` for the real slots `Slot n` and the real identities `UC sg (cnEquiv n)`

`nι = 24n+23`, `eι = slotEquiv n`, `nc c = (slotList sg (e.symm c)).length`, `ecc c j` = the position of `j` in the (duplicate-free) used-slot list.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L83
open Finset ECDLP.L44 ECDLP.L54 ECDLP.L63 Slot Cst

variable {n : ℕ}

/-- the used-slot list of identity `c` of the enumeration `cnEquiv n` -/
def lst (sg : Fin (n + 1) → Sg) (c : Fin (18 * n + 12)) : List (Slot n) := slotList sg ((cnEquiv n).symm c)

theorem mem_UC_iff (sg : Fin (n + 1) → Sg) (c : Fin (18 * n + 12)) (s : Slot n) :
    s ∈ usedS (famF sg (cnEquiv n) c) ↔ s ∈ lst sg c := by
  show s ∈ usedS (formF sg ((cnEquiv n).symm c)) ↔ _
  rw [usedS_eq, List.mem_toFinset]; rfl

/-- rank of a used slot in the list -/
def eccOf (sg : Fin (n + 1) → Sg) (c : Fin (18 * n + 12)) :
    UC sg (cnEquiv n) c ≃ Fin (lst sg c).length where
  toFun j := ⟨(lst sg c).idxOf j.1, List.idxOf_lt_length_of_mem ((mem_UC_iff sg c j.1).1 j.2)⟩
  invFun k := ⟨(lst sg c)[k], (mem_UC_iff sg c _).2 (List.getElem_mem _)⟩
  left_inv j := by
    apply Subtype.ext
    exact List.getElem_idxOf _
  right_inv k := by
    apply Fin.ext
    exact List.Nodup.idxOf_getElem (slotList_nodup sg _) k.1 k.2

/-- **L73's `Lay` for the real network** -/
def layOf (sg : Fin (n + 1) → Sg) : ECDLP.L73.Lay (Slot n) (UC sg (cnEquiv n)) where
  nι := 24 * n + 23
  eι := slotEquiv n
  nc c := (lst sg c).length
  ecc c := eccOf sg c

theorem layOf_eι (sg : Fin (n + 1) → Sg) (s : Slot n) : ((layOf sg).eι s : ℕ) = slotNum s := rfl

/-- `ecc` ranks are positions in the list: `(lst c)[ecc j] = j` -/
theorem lst_ecc (sg : Fin (n + 1) → Sg) (c : Fin (18 * n + 12)) (j : UC sg (cnEquiv n) c) :
    (lst sg c)[(eccOf sg c j : ℕ)]'(eccOf sg c j).2 = j.1 := List.getElem_idxOf _

end ECDLP.L83
end
