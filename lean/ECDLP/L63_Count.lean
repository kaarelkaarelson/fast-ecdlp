import ECDLP.L63_Slots

/-!
# L63 / Count: exact `|Var n|`, `|Slot n|`, `K = |Cn n|` as functions of `m = n + 1`, and `nmax = 9`
-/
noncomputable section
namespace ECDLP.L63
open Finset ECDLP.L44 ECDLP.L54 Slot Cst

variable {n K : ℕ}

theorem card_UC_le9 (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) :
    Fintype.card (UC sg e c) ≤ 9 := by
  unfold UC
  rw [Fintype.card_coe]
  refine (card_le_card (t := (slotList sg (e.symm c)).toFinset) fun s hs =>
    List.mem_toFinset.2 (usedS_sub sg _ s hs)).trans ((List.toFinset_card_le _).trans (slotList_len sg _))

theorem card_Var : Fintype.card (Var n) = 11 * n + 5 := by
  let f : Var n → (Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin n ⊕ Fin n ⊕ Fin (n + 1) ⊕
      Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin n)
    | .x i => .inl i
    | .y i => .inr (.inl i)
    | .sx i => .inr (.inr (.inl i))
    | .sy i => .inr (.inr (.inr (.inl i)))
    | .w i => .inr (.inr (.inr (.inr (.inl i))))
    | .l i => .inr (.inr (.inr (.inr (.inr (.inl i)))))
    | .qc i => .inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))
    | .q0 i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))
    | .q1 i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))
    | .q2 i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))
    | .q3 i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))))
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      cases a <;> cases b <;> simp_all [f]
    · intro v
      rcases v with i | i | i | i | i | i | i | i | i | i | i
      exacts [⟨.x i, rfl⟩, ⟨.y i, rfl⟩, ⟨.sx i, rfl⟩, ⟨.sy i, rfl⟩, ⟨.w i, rfl⟩, ⟨.l i, rfl⟩, ⟨.qc i, rfl⟩,
        ⟨.q0 i, rfl⟩, ⟨.q1 i, rfl⟩, ⟨.q2 i, rfl⟩, ⟨.q3 i, rfl⟩]
  rw [Fintype.card_of_bijective hf]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem card_Slot : Fintype.card (Slot n) = 24 * n + 23 := by
  let f : Slot n → (Var n ⊕ Var n ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Cst)
    | .v a => .inl a
    | .sl a => .inr (.inl a)
    | .u i => .inr (.inr (.inl i))
    | .tg i => .inr (.inr (.inr (.inl i)))
    | .cst c => .inr (.inr (.inr (.inr c)))
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      cases a <;> cases b <;> simp_all [f]
    · intro v
      rcases v with i | i | i | i | i
      exacts [⟨.v i, rfl⟩, ⟨.sl i, rfl⟩, ⟨.u i, rfl⟩, ⟨.tg i, rfl⟩, ⟨.cst i, rfl⟩]
  rw [Fintype.card_of_bijective hf]
  have hC : Fintype.card Cst = 11 := rfl
  simp only [Fintype.card_sum, Fintype.card_fin, hC, card_Var]
  omega

theorem card_Cn : Fintype.card (Cn n) = 18 * n + 12 := by
  let f : Cn n → (Var n ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin 4 ⊕ Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin (n + 1))
    | .rng a => .inl a
    | .uEq i => .inr (.inl i)
    | .curve i => .inr (.inr (.inl i))
    | .s0x => .inr (.inr (.inr (.inl 0)))
    | .s0y => .inr (.inr (.inr (.inl 1)))
    | .sRx => .inr (.inr (.inr (.inl 2)))
    | .sRy => .inr (.inr (.inr (.inl 3)))
    | .e0 k => .inr (.inr (.inr (.inr (.inl k))))
    | .e1 k => .inr (.inr (.inr (.inr (.inr (.inl k)))))
    | .e2 k => .inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))
    | .e3 k => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))))
    | .sign i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      cases a <;> cases b <;> simp_all [f]
    · intro v
      rcases v with a | i | i | i | k | k | k | k | i
      · exact ⟨.rng a, rfl⟩
      · exact ⟨.uEq i, rfl⟩
      · exact ⟨.curve i, rfl⟩
      · fin_cases i
        exacts [⟨.s0x, rfl⟩, ⟨.s0y, rfl⟩, ⟨.sRx, rfl⟩, ⟨.sRy, rfl⟩]
      · exact ⟨.e0 k, rfl⟩
      · exact ⟨.e1 k, rfl⟩
      · exact ⟨.e2 k, rfl⟩
      · exact ⟨.e3 k, rfl⟩
      · exact ⟨.sign i, rfl⟩
  rw [Fintype.card_of_bijective hf]
  simp only [Fintype.card_sum, Fintype.card_fin, card_Var]
  omega

/-- number of identities in terms of `m = n + 1` points -/
theorem card_K (e : Cn n ≃ Fin K) : K = 18 * n + 12 := by
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, card_Cn] at this
  omega

end ECDLP.L63
end
