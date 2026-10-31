import ECDLP.L81_SrcSlot
import ECDLP.L63_Count

/-!
# L81 / Idx: an explicit slot numbering `Slot n ~ Fin (24 n + 23)` with `SlotIdx`
(constants first, then the sign slacks, then the `x` variables; every other slot after them).
-/
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L81
open Finset ECDLP.L44 Slot Cst

variable (n : ℕ)

/-- the slots that carry bit constraints -/
def Special : Slot n → Prop
  | .cst _ => True
  | .tg _ => True
  | .v (.x _) => True
  | _ => False

/-- the numbering on the special slots (arbitrary elsewhere) -/
def sNum : Slot n → ℕ
  | .cst c => cIdx c
  | .tg i => 11 + i
  | .v (.x i) => 12 + n + i
  | _ => 0

theorem cIdx_lt (c : Cst) : cIdx c < 11 := by cases c <;> decide

theorem cIdx_inj {c d : Cst} (h : cIdx c = cIdx d) : c = d := by
  have := congrArg cstOf h
  rwa [cstOf_cIdx, cstOf_cIdx] at this

theorem special_cases {s : Slot n} (h : Special n s) :
    (∃ c, s = .cst c) ∨ (∃ i, s = .tg i) ∨ (∃ i, s = .v (.x i)) := by
  cases s with
  | cst c => exact Or.inl ⟨c, rfl⟩
  | tg i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | v a => cases a with
    | x i => exact Or.inr (Or.inr ⟨i, rfl⟩)
    | _ => exact absurd h (by simp [Special])
  | sl a => exact absurd h (by simp [Special])
  | u i => exact absurd h (by simp [Special])

theorem sNum_inj : Set.InjOn (sNum n) {s | Special n s} := by
  intro s hs t ht h
  rcases special_cases n hs with ⟨c, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
  rcases special_cases n ht with ⟨d, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> simp only [sNum] at h
  · rw [cIdx_inj h]
  · have := cIdx_lt c; have := j.2; omega
  · have := cIdx_lt c; have := j.2; omega
  · have := cIdx_lt d; have := i.2; omega
  · congr 1; exact Fin.ext (by omega)
  · have := j.2; have := i.2; omega
  · have := cIdx_lt d; have := i.2; omega
  · have := j.2; have := i.2; omega
  · congr 2; exact Fin.ext (by omega)

theorem sNum_lt {s : Slot n} (h : Special n s) : sNum n s < 13 + 2 * n := by
  rcases special_cases n h with ⟨c, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp only [sNum]
  · have := cIdx_lt c; omega
  · have := i.2; omega
  · have := i.2; omega

theorem sNum_surj {k : ℕ} (hk : k < 13 + 2 * n) : ∃ s, Special n s ∧ sNum n s = k := by
  by_cases h1 : k < 11
  · exact ⟨.cst (cstOf k), trivial, by
      have : cIdx (cstOf k) = k := by
        interval_cases k <;> rfl
      simpa [sNum] using this⟩
  · by_cases h2 : k < 12 + n
    · exact ⟨.tg ⟨k - 11, by omega⟩, trivial, by simp [sNum]; omega⟩
    · exact ⟨.v (.x ⟨k - 12 - n, by omega⟩), trivial, by simp [sNum]; omega⟩

/-- **an explicit slot numbering** -/
theorem exists_slotIdx : ∃ e : Slot n ≃ Fin (24 * n + 23), SlotIdx n (fun i => (e i : ℕ)) := by
  classical
  have hcard : Fintype.card (Slot n) = (Finset.range (24 * n + 23)).card := by
    rw [ECDLP.L63.card_Slot, Finset.card_range]
  have hfst : Finset.image (sNum n) (Finset.univ.filter (Special n)) ⊆ Finset.range (24 * n + 23) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have := sNum_lt n hs
    simp only [Finset.mem_range]; omega
  have hinj : Set.InjOn (sNum n) ↑(Finset.univ.filter (Special n)) := by
    intro a ha b hb h
    exact sNum_inj n (by simpa using ha) (by simpa using hb) h
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard hfst hinj
  let q : (Finset.range (24 * n + 23) : Finset ℕ) ≃ Fin (24 * n + 23) :=
    { toFun := fun x => ⟨x.1, Finset.mem_range.1 x.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_range.2 i.2⟩
      left_inv := fun x => rfl
      right_inv := fun i => rfl }
  refine ⟨g.trans q, ?_, ?_, ?_, ?_⟩
  · intro c; exact hg _ (by simp [Special])
  · intro i; exact hg (.tg i) (by simp [Special])
  · intro i; exact hg (.v (.x i)) (by simp [Special])
  · intro s h1 h2 h3
    by_contra hlt
    push_neg at hlt
    have hsp : ¬ Special n s := by
      intro hs
      rcases special_cases n hs with ⟨c, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      exacts [h1 c rfl, h2 i rfl, h3 i rfl]
    obtain ⟨s', hs', hv⟩ := sNum_surj n hlt
    have : (g s : ℕ) = g s' := by
      rw [hg s' (by simpa using hs'), hv]
      simp [Equiv.trans_apply, q] at hlt
      exact_mod_cast (by simpa [q] using hlt)
    exact hsp (by rw [g.injective (Subtype.ext this)]; exact hs')

end ECDLP.L81
