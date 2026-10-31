import ECDLP.L65_Bridge
import ECDLP.L63_Count

/-!
# L94 / Sum: exact-ish count `T = sum_c |slots of c| <= 107 n + 83` (the 11n+5 range identities read only 4 slots)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L94
open Finset ECDLP.L44 ECDLP.L54 ECDLP.L63 Slot Cst

variable {n K : ℕ}

/-- slots read by an identity: 4 for range identities, at most 9 otherwise -/
def gBnd : Cn n → ℕ
  | .rng _ => 4
  | _ => 9

theorem len_le_gBnd (sg : Fin (n + 1) → Sg) (x : Cn n) : (slotList sg x).length ≤ gBnd x := by
  cases x <;> simp [slotList, gBnd] <;> (try split) <;> simp

theorem card_UC_le_len (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) :
    Fintype.card (UC sg e c) ≤ (slotList sg (e.symm c)).length := by
  unfold UC
  rw [Fintype.card_coe]
  exact (card_le_card (t := (slotList sg (e.symm c)).toFinset) fun s hs =>
    List.mem_toFinset.2 (usedS_sub sg _ s hs)).trans (List.toFinset_card_le _)

theorem card_rng_ge : 11 * n + 5 ≤ (univ.filter (fun x : Cn n => ∃ a, x = Cn.rng a)).card := by
  have h := card_Var (n := n)
  rw [← h]
  refine card_le_card_of_injOn (fun a => Cn.rng a) (fun a _ => ?_) (fun a _ b _ hab => by simpa using hab)
  simp

theorem sum_gBnd : ∑ x : Cn n, gBnd x + 5 * (univ.filter (fun x : Cn n => ∃ a, x = Cn.rng a)).card = 9 * (18 * n + 12) := by
  classical
  have : ∀ x : Cn n, gBnd x + 5 * (if ∃ a, x = Cn.rng a then 1 else 0) = 9 := by
    intro x
    cases x <;> simp [gBnd]
  have h2 : ∑ x : Cn n, (gBnd x + 5 * (if ∃ a, x = Cn.rng a then 1 else 0)) = ∑ x : Cn n, 9 := sum_congr rfl fun x _ => this x
  rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, card_Cn, smul_eq_mul] at h2
  rw [Finset.card_filter]
  simpa [mul_comm] using h2

theorem sumNc_le (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) :
    ∑ c : Fin K, Fintype.card (UC sg e c) ≤ 107 * n + 83 := by
  classical
  have h1 : ∑ c : Fin K, Fintype.card (UC sg e c) ≤ ∑ c : Fin K, gBnd (e.symm c) :=
    sum_le_sum fun c _ => (card_UC_le_len sg e c).trans (len_le_gBnd sg _)
  have h2 : ∑ c : Fin K, gBnd (e.symm c) = ∑ x : Cn n, gBnd x := Equiv.sum_comp e.symm gBnd
  have h3 := sum_gBnd (n := n)
  have h4 := card_rng_ge (n := n)
  omega

end ECDLP.L94
end
