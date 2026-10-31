import ECDLP.L59_Explicit
import ECDLP.L57_Inst

/-!
# L63 / Slots: at most 9 slots per identity of L44's system

`slotList sg c` lists the slots read by identity `c`; `usedS_sub`: every used slot is in it;
`card_usedS_le : (usedS (formF sg c)).card ≤ 9`; hence `card (UC sg e c) ≤ 9` (L57 had 12).
-/
noncomputable section
namespace ECDLP.L63
open Finset ECDLP.L44 ECDLP.L54 Slot Cst

variable {n K : ℕ}

theorem mem_usedS_mkF {ι : Type} [DecidableEq ι] (L : List (ℤ × ι × ι)) (s : ι) :
    s ∈ usedS (mkF L) ↔ ∃ e ∈ L, e.2.1 = s ∨ e.2.2 = s := by
  unfold usedS
  simp only [mem_union, mem_image, mem_univ, true_and, mkF]
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact ⟨_, List.get_mem _ _, Or.inl ht.2⟩
    · exact ⟨_, List.get_mem _ _, Or.inr ht.2⟩
  · rintro ⟨e, he, h⟩
    obtain ⟨t, rfl⟩ := List.mem_iff_get.1 he
    rcases h with h | h
    · exact Or.inl ⟨t, mem_univ _, h⟩
    · exact Or.inr ⟨t, mem_univ _, h⟩

/-- the slots read by identity `c` (with repetitions) -/
def slotList (sg : Fin (n + 1) → Sg) : Cn n → List (Slot n)
  | .rng a => [v a, sl a, cst one, cst (bnd a)]
  | .uEq i => [u i, cst one, v (.x i)]
  | .curve i => [v (.y i), u i, v (.x i), cst ca, cst cb, cst one, cst cOp, v (.qc i), cst cp]
  | .s0x => [v (.sx 0), cst one, v (.x 0)]
  | .s0y => [v (.sy 0), cst one, v (.y 0)]
  | .sRx => [v (.sx (Fin.last n)), cst one, cst cRx]
  | .sRy => [v (.sy (Fin.last n)), cst one, cst cRy]
  | .e0 j => [v (.w j), v (.x j.succ), v (.sx j.castSucc), cst one, cst cOp, v (.q0 j), cst cp]
  | .e1 j => [v (.l j), v (.x j.succ), v (.sx j.castSucc), v (.y j.succ), cst one, v (.sy j.castSucc),
      cst cOp, v (.q1 j), cst cp]
  | .e2 j => [v (.l j), cst one, v (.sx j.castSucc), v (.x j.succ), v (.sx j.succ), cst cOp, v (.q2 j), cst cp]
  | .e3 j => [v (.l j), v (.sx j.castSucc), v (.sx j.succ), v (.sy j.succ), cst one, v (.sy j.castSucc),
      cst cOp, v (.q3 j), cst cp]
  | .sign i => match sg i with
      | .none => []
      | .pos => [v (.y i), cst one, cst cc1, tg i]
      | .neg => [v (.y i), cst one, tg i, cst cc0]

theorem slotList_len (sg : Fin (n + 1) → Sg) (c : Cn n) : (slotList sg c).length ≤ 9 := by
  cases c <;> simp [slotList] <;> (try split) <;> simp

theorem usedS_sub (sg : Fin (n + 1) → Sg) (c : Cn n) (s : Slot n) (h : s ∈ usedS (formF sg c)) :
    s ∈ slotList sg c := by
  unfold formF at h
  rw [mem_usedS_mkF] at h
  obtain ⟨e, he, hs⟩ := h
  cases c <;> simp only [formL, tailT, slotList] at he ⊢ <;> (try split at he) <;> (try split) <;>
    aesop
