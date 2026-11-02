import Mathlib
import ECDLPv2.L116_Union

/-!
# L116 / Prod: the number of generating `s`-tuples is multiplicative over a coprime product
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L116

open Finset

section prod
variable {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Fintype B] [Fintype C]

theorem closure_prod_iff (hcop : Nat.Coprime (Fintype.card B) (Fintype.card C)) {s : ℕ}
    (m : Fin s → B × C) :
    AddSubgroup.closure (Set.range m) = ⊤ ↔
      AddSubgroup.closure (Set.range (fun i => (m i).1)) = ⊤ ∧
      AddSubgroup.closure (Set.range (fun i => (m i).2)) = ⊤ := by
  set H := AddSubgroup.closure (Set.range m) with hH
  have hmapB : AddSubgroup.map (AddMonoidHom.fst B C) H =
      AddSubgroup.closure (Set.range (fun i => (m i).1)) := by
    rw [hH, AddMonoidHom.map_closure, ← Set.range_comp]; rfl
  have hmapC : AddSubgroup.map (AddMonoidHom.snd B C) H =
      AddSubgroup.closure (Set.range (fun i => (m i).2)) := by
    rw [hH, AddMonoidHom.map_closure, ← Set.range_comp]; rfl
  constructor
  · intro h
    rw [h] at hmapB hmapC
    exact ⟨by rw [← hmapB]; exact AddSubgroup.map_top_of_surjective _ Prod.fst_surjective,
      by rw [← hmapC]; exact AddSubgroup.map_top_of_surjective _ Prod.snd_surjective⟩
  · rintro ⟨hB, hC⟩
    rw [hB] at hmapB; rw [hC] at hmapC
    have hBC : IsCoprime (Fintype.card B : ℤ) (Fintype.card C : ℤ) :=
      Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨u, v, huv⟩ := hBC
    have key : ∀ (b : B), ((b, 0) : B × C) ∈ H := by
      intro b
      obtain ⟨h, hhH, hh1⟩ : ∃ h ∈ H, h.1 = b := by
        have : b ∈ AddSubgroup.map (AddMonoidHom.fst B C) H := by rw [hmapB]; trivial
        obtain ⟨h, hh, rfl⟩ := this
        exact ⟨h, hh, rfl⟩
      have h1 : (v : ℤ) • ((Fintype.card C : ℤ) • h) ∈ H := H.zsmul_mem (H.zsmul_mem hhH _) _
      have h2 : (v : ℤ) • ((Fintype.card C : ℤ) • h) = (b, 0) := by
        ext
        · simp only [Prod.smul_fst, hh1]
          have hB0 : ((Fintype.card B : ℤ) * u) • b = 0 := by
            rw [mul_comm, mul_smul]; simp
          calc (v : ℤ) • (Fintype.card C : ℤ) • b = (v * Fintype.card C : ℤ) • b := by rw [mul_smul]
            _ = (u * Fintype.card B + v * Fintype.card C : ℤ) • b := by
                rw [add_smul, mul_comm u, hB0, zero_add]
            _ = b := by rw [huv]; simp
        · simp only [Prod.smul_snd]
          have : (Fintype.card C : ℤ) • h.2 = 0 := by simp
          rw [this]; simp
      rwa [h2] at h1
    have key2 : ∀ (c : C), ((0, c) : B × C) ∈ H := by
      intro c
      obtain ⟨h, hhH, hh1⟩ : ∃ h ∈ H, h.2 = c := by
        have : c ∈ AddSubgroup.map (AddMonoidHom.snd B C) H := by rw [hmapC]; trivial
        obtain ⟨h, hh, rfl⟩ := this
        exact ⟨h, hh, rfl⟩
      have h1 : (u : ℤ) • ((Fintype.card B : ℤ) • h) ∈ H := H.zsmul_mem (H.zsmul_mem hhH _) _
      have h2 : (u : ℤ) • ((Fintype.card B : ℤ) • h) = (0, c) := by
        ext
        · simp only [Prod.smul_fst]
          have : (Fintype.card B : ℤ) • h.1 = 0 := by simp
          rw [this]; simp
        · simp only [Prod.smul_snd, hh1]
          have hC0 : ((Fintype.card C : ℤ) * v) • c = 0 := by
            rw [mul_comm, mul_smul]; simp
          calc (u : ℤ) • (Fintype.card B : ℤ) • c = (u * Fintype.card B : ℤ) • c := by rw [mul_smul]
            _ = (u * Fintype.card B + v * Fintype.card C : ℤ) • c := by
                rw [add_smul, mul_comm v, hC0, add_zero]
            _ = c := by rw [huv]; simp
      rwa [h2] at h1
    rw [eq_top_iff]
    rintro ⟨b, c⟩ -
    have := H.add_mem (key b) (key2 c)
    simpa using this

open Classical in
theorem genCount_prod (hcop : Nat.Coprime (Fintype.card B) (Fintype.card C)) (s : ℕ) :
    genCount (B × C) s = genCount B s * genCount C s := by
  unfold genCount
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun m => ((fun i => (m i).1), (fun i => (m i).2)))
    (fun x => fun i => (x.1 i, x.2 i)) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hm
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_setOf_eq]
    exact (closure_prod_iff hcop m).1 hm
  · intro x hx
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_setOf_eq] at hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact (closure_prod_iff hcop _).2 hx
  · intro m _; rfl
  · intro x _; rfl

end prod
end ECDLP.L116
