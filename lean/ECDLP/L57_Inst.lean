import ECDLP.L57_Par
import ECDLP.L56_EFinal

/-!
# L57 / Inst: the combinatorial constants of the concrete ECDLP network
-/
noncomputable section
namespace ECDLP.L57
open Finset ECDLP.L30 ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

section
variable {n : ℕ}

theorem formL_len (sg : Fin (n + 1) → Sg) (c : Cn n) : (formL sg c).length ≤ 6 := by
  cases c <;> simp [formL, tailT] <;> (try split) <;> simp

theorem usedS_card {ι : Type} [DecidableEq ι] (F : Form ι) : (usedS F).card ≤ 2 * F.n := by
  unfold usedS
  refine (card_union_le _ _).trans ?_
  have h1 : (univ.image F.l).card ≤ F.n := card_image_le.trans (by simp)
  have h2 : (univ.image F.r).card ≤ F.n := card_image_le.trans (by simp)
  omega

theorem card_UC_le {K : ℕ} (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) :
    Fintype.card (UC sg e c) ≤ 12 := by
  unfold UC
  rw [Fintype.card_coe]
  refine (usedS_card _).trans ?_
  have : (famF sg e c).n ≤ 6 := by
    show (formL sg (e.symm c)).length ≤ 6
    exact formL_len sg _
  omega

open ECDLP.L44 in
theorem card_Var_le : Fintype.card (Var n) ≤ 11 * n + 5 := by
  let f : (Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin n ⊕ Fin n ⊕ Fin (n + 1) ⊕
      Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin n) → Var n
    | .inl i => .x i
    | .inr (.inl i) => .y i
    | .inr (.inr (.inl i)) => .sx i
    | .inr (.inr (.inr (.inl i))) => .sy i
    | .inr (.inr (.inr (.inr (.inl i)))) => .w i
    | .inr (.inr (.inr (.inr (.inr (.inl i))))) => .l i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => .qc i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => .q0 i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => .q1 i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))) => .q2 i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))) => .q3 i
  have hf : Function.Surjective f := by
    intro v
    cases v
    · exact ⟨.inl _, rfl⟩
    · exact ⟨.inr (.inl _), rfl⟩
    · exact ⟨.inr (.inr (.inl _)), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inl _))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inl _)))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inl _))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (_)))))))))), rfl⟩
  refine (Fintype.card_le_of_surjective f hf).trans ?_
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem card_Cn_le : Fintype.card (Cn n) ≤ 18 * (n + 1) := by
  let f : (Var n ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin 4 ⊕ Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin (n + 1)) → Cn n
    | .inl a => .rng a
    | .inr (.inl i) => .uEq i
    | .inr (.inr (.inl i)) => .curve i
    | .inr (.inr (.inr (.inl i))) =>
        if i.val = 0 then .s0x else if i.val = 1 then .s0y else if i.val = 2 then .sRx else .sRy
    | .inr (.inr (.inr (.inr (.inl k)))) => .e0 k
    | .inr (.inr (.inr (.inr (.inr (.inl k))))) => .e1 k
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))) => .e2 k
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))) => .e3 k
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))) => .sign i
  have hf : Function.Surjective f := by
    intro v
    cases v
    · exact ⟨.inl _, rfl⟩
    · exact ⟨.inr (.inl _), rfl⟩
    · exact ⟨.inr (.inr (.inl _)), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inl ⟨0, by omega⟩))), by simp [f]⟩
    · exact ⟨.inr (.inr (.inr (.inl ⟨1, by omega⟩))), by simp [f]⟩
    · exact ⟨.inr (.inr (.inr (.inl ⟨2, by omega⟩))), by simp [f]⟩
    · exact ⟨.inr (.inr (.inr (.inl ⟨3, by omega⟩))), by simp [f]⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inl _)))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inl _))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (_)))))))), rfl⟩
  refine (Fintype.card_le_of_surjective f hf).trans ?_
  have := card_Var_le (n := n)
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- number of (identity, slot) incidences of a shared slot is at most the number of identities, when each
identity reads each slot once -/
theorem occ_le_K {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ} {ιc : Fin K → Type} [∀ c, Fintype (ιc c)]
    (φ : ∀ c, ιc c → ι) (hinj : ∀ c, Function.Injective (φ c)) (i : ι) : occ (ιc := ιc) φ i ≤ K := by
  unfold occ
  calc _ ≤ (univ : Finset (Fin K)).card := by
        refine card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
        intro p hp q hq hpq
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
        obtain ⟨c, x⟩ := p
        obtain ⟨c', x'⟩ := q
        simp only at hpq
        subst hpq
        have : x = x' := hinj _ (hp.trans hq.symm)
        subst this; rfl
    _ = K := by simp

end
end ECDLP.L57
end
