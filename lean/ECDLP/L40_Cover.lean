import Mathlib

/-!
# L40 (1): coverage from additive energy (Cauchy-Schwarz)

For a finite additive group `G`, finite `F ⊆ G`, `S ⊆ F^m`, the number of distinct sums
`{∑ t | t ∈ S}` is at least `|S|^2 / E_m(F)`, where
`E_m(F) = #{(t,u) ∈ F^m × F^m | ∑ t = ∑ u}`.
-/
namespace ECDLP.L40

open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `m`-fold additive energy of `F`. -/
def energy (m : ℕ) (F : Finset G) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin m => F) ×ˢ Fintype.piFinset (fun _ : Fin m => F)).filter
    (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card

/-- representation function of `S` -/
def rep {m : ℕ} (S : Finset (Fin m → G)) (R : G) : ℕ := (S.filter (fun t => ∑ i, t i = R)).card

/-- the set of sums attained by `S` -/
def sums {m : ℕ} (S : Finset (Fin m → G)) : Finset G := S.image (fun t => ∑ i, t i)

theorem sum_rep {m : ℕ} (S : Finset (Fin m → G)) : ∑ R ∈ sums S, rep S R = S.card := by
  unfold sums rep
  exact (card_eq_sum_card_image (fun t : Fin m → G => ∑ i, t i) S).symm

theorem sum_rep_sq {m : ℕ} (S : Finset (Fin m → G)) :
    ∑ R ∈ sums S, rep S R ^ 2 = ((S ×ˢ S).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
  have h := card_eq_sum_card_fiberwise (f := fun p : (Fin m → G) × (Fin m → G) => ∑ i, p.1 i)
    (s := (S ×ˢ S).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)) (t := sums S) (by
      intro p hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
      simp only [sums, coe_image, Set.mem_image, mem_coe]
      exact ⟨p.1, hp.1.1, rfl⟩)
  rw [h]
  refine sum_congr rfl (fun R _ => ?_)
  have : ((S ×ˢ S).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).filter
      (fun p => ∑ i, p.1 i = R) = (S.filter (fun t => ∑ i, t i = R)) ×ˢ
        (S.filter (fun t => ∑ i, t i = R)) := by
    ext ⟨t, u⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h2, by rw [← h3, h4]⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨⟨h1, h3⟩, by rw [h2, h4]⟩, h2⟩
  rw [this, card_product, sq]; rfl

theorem sq_card_le_sums_mul_energy {m : ℕ} (F : Finset G) (S : Finset (Fin m → G))
    (hS : S ⊆ Fintype.piFinset (fun _ : Fin m => F)) :
    S.card ^ 2 ≤ (sums S).card * energy m F := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := sums S) (f := rep S)
  rw [sum_rep, sum_rep_sq] at h1
  refine h1.trans (Nat.mul_le_mul_left _ (card_le_card ?_))
  intro p hp
  simp only [mem_filter, mem_product] at hp ⊢
  exact ⟨⟨hS hp.1.1, hS hp.1.2⟩, hp.2⟩

/-- Real-number form: `#sums ≥ |S|^2 / E_m(F)` when the energy is positive. -/
theorem coverage_real {m : ℕ} (F : Finset G) (S : Finset (Fin m → G))
    (hS : S ⊆ Fintype.piFinset (fun _ : Fin m => F)) (hE : 0 < energy m F) :
    (S.card : ℝ) ^ 2 / energy m F ≤ (sums S).card := by
  rw [div_le_iff₀ (by exact_mod_cast hE)]
  exact_mod_cast (sq_card_le_sums_mul_energy F S hS).trans (le_of_eq (by ring))

end ECDLP.L40
