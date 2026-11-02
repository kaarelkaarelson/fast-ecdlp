import Mathlib

/-!
# L114 / Comb: conditional-to-unconditional counting for the round

`lf_bound` : if, on every fibre `{a | Tmap a = y}` of the conditioning variable where the (fibre-constant)
event `cond` holds, the property `Good i` fails for at most a `1/D i` fraction, then
`#{cond ∧ ∃ i ∈ I, ¬Good i} ≤ (∑_{i ∈ I} 1/D i) * #{cond}`.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

section comb
variable {Ω Y ι : Type*} [Fintype Ω] [DecidableEq Y]

theorem single_prime_bound (Tmap : Ω → Y) (cond : Ω → Prop) [DecidablePred cond]
    (Good : Ω → Prop) [DecidablePred Good] (D : ℕ)
    (hcond : ∀ a a', Tmap a = Tmap a' → (cond a ↔ cond a'))
    (hgood : ∀ y, (∃ a, Tmap a = y ∧ cond a) →
      (univ.filter fun a => Tmap a = y ∧ ¬ Good a).card * D ≤ (univ.filter fun a => Tmap a = y).card) :
    (univ.filter fun a => cond a ∧ ¬ Good a).card * D ≤ (univ.filter cond).card := by
  classical
  set Yset : Finset Y := univ.image Tmap with hY
  have hm : ∀ a, Tmap a ∈ Yset := fun a => mem_image.2 ⟨a, mem_univ _, rfl⟩
  have e1 : (univ.filter fun a => cond a ∧ ¬ Good a).card =
      ∑ y ∈ Yset, (univ.filter fun a => Tmap a = y ∧ cond a ∧ ¬ Good a).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Tmap) (t := Yset) (fun a _ => hm a)]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1; ext a; simp only [mem_filter, mem_univ, true_and]; tauto
  have e2 : (univ.filter cond).card = ∑ y ∈ Yset, (univ.filter fun a => Tmap a = y ∧ cond a).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Tmap) (t := Yset) (fun a _ => hm a)]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1; ext a; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [e1, e2, Finset.sum_mul]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hy : ∃ a, Tmap a = y ∧ cond a
  · obtain ⟨a0, ha0, hc0⟩ := hy
    have h1 : (univ.filter fun a => Tmap a = y ∧ cond a ∧ ¬ Good a) =
        (univ.filter fun a => Tmap a = y ∧ ¬ Good a) := by
      ext a; simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, (hcond a a0 (h1.trans ha0.symm)).2 hc0, h3⟩
    have h2 : (univ.filter fun a => Tmap a = y ∧ cond a) = (univ.filter fun a => Tmap a = y) := by
      ext a; simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, _⟩; exact h1
      · intro h1; exact ⟨h1, (hcond a a0 (h1.trans ha0.symm)).2 hc0⟩
    rw [h1, h2]; exact hgood y ⟨a0, ha0, hc0⟩
  · have : (univ.filter fun a => Tmap a = y ∧ cond a ∧ ¬ Good a) = ∅ := by
      ext a; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨h1, h2, _⟩; exact hy ⟨a, h1, h2⟩
    rw [this]; simp

theorem lf_bound [DecidableEq ι] (Tmap : Ω → Y) (cond : Ω → Prop) [DecidablePred cond] (I : Finset ι)
    (Good : ι → Ω → Prop) [∀ i, DecidablePred (Good i)] (D : ι → ℕ) (hD : ∀ i ∈ I, 0 < D i)
    (hcond : ∀ a a', Tmap a = Tmap a' → (cond a ↔ cond a'))
    (hgood : ∀ i ∈ I, ∀ y, (∃ a, Tmap a = y ∧ cond a) →
      (univ.filter fun a => Tmap a = y ∧ ¬ Good i a).card * D i ≤ (univ.filter fun a => Tmap a = y).card) :
    ((univ.filter fun a => cond a ∧ ∃ i ∈ I, ¬ Good i a).card : ℚ) ≤
      (∑ i ∈ I, (1 : ℚ) / D i) * (univ.filter cond).card := by
  classical
  have hsub : (univ.filter fun a => cond a ∧ ∃ i ∈ I, ¬ Good i a) ⊆
      I.biUnion (fun i => univ.filter fun a => cond a ∧ ¬ Good i a) := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and, mem_biUnion] at ha ⊢
    obtain ⟨hc, i, hi, hg⟩ := ha
    exact ⟨i, hi, hc, hg⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ i ∈ I, ((univ.filter fun a => cond a ∧ ¬ Good i a).card : ℚ) ≤
      (1 : ℚ) / D i * (univ.filter cond).card := by
    intro i hi
    have := single_prime_bound Tmap cond (Good i) (D i) hcond (hgood i hi)
    have hDi : (0 : ℚ) < D i := by exact_mod_cast hD i hi
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hDi]
    exact_mod_cast this
  calc ((univ.filter fun a => cond a ∧ ∃ i ∈ I, ¬ Good i a).card : ℚ)
      ≤ ∑ i ∈ I, ((univ.filter fun a => cond a ∧ ¬ Good i a).card : ℚ) := by exact_mod_cast h1
    _ ≤ ∑ i ∈ I, (1 : ℚ) / D i * (univ.filter cond).card := Finset.sum_le_sum h2
    _ = _ := by rw [Finset.sum_mul]

end comb
end ECDLP.L114
