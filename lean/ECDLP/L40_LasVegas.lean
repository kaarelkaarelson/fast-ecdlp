import Mathlib

/-!
# L40 (4): Las Vegas lemma
Over a finite field `K` (e.g. `ZMod n`, n prime) with `q` elements, for fixed `λ ≠ 0` in `K^N`,
`#{b ∈ K^N | ∑ λ_i b_i = c} = q^(N-1)` for every `c`; and the version with `λ` depending on
independent data `ω`.
-/
namespace ECDLP.L40

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

theorem fiber_card_indep (l : Fin N → K) (i0 : Fin N) (h : l i0 ≠ 0) (c c' : K) :
    (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c)).card =
    (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c')).card := by
  -- translation by b0 with ∑ l_i b0_i = c' - c
  set b0 : Fin N → K := Pi.single i0 ((c' - c) / l i0) with hb0
  have hs : ∑ i, l i * b0 i = c' - c := by
    rw [hb0, Finset.sum_eq_single i0]
    · simp; field_simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  refine card_bij (fun b _ => b + b0) ?_ ?_ ?_
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    simp only [Pi.add_apply, mul_add, sum_add_distrib, hb, hs]; ring
  · intro a _ b _ hab; simpa using hab
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    refine ⟨b - b0, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Pi.sub_apply, mul_sub, sum_sub_distrib, hb, hs]; ring

theorem las_vegas_count (l : Fin N → K) (i0 : Fin N) (h : l i0 ≠ 0) (c : K) :
    (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c)).card = Fintype.card K ^ (N - 1) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i0.elim0)
  have htot : ∑ c' : K, (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c')).card
      = Fintype.card K ^ N := by
    rw [← card_eq_sum_card_fiberwise (f := fun b : Fin N → K => ∑ i, l i * b i)
      (s := (univ : Finset (Fin N → K))) (t := univ) (by intro _ _; simp)]
    simp
  have hconst : ∑ c' : K, (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c')).card
      = Fintype.card K * (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c)).card := by
    rw [sum_congr rfl (fun c' _ => fiber_card_indep l i0 h c' c)]
    simp
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have : Fintype.card K * (univ.filter (fun b : Fin N → K => ∑ i, l i * b i = c)).card
      = Fintype.card K * Fintype.card K ^ (N - 1) := by
    rw [← hconst, htot, ← pow_succ']; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_left hq this

/-- Probability form for `λ` fixed. -/
theorem las_vegas_prob (l : Fin N → K) (i0 : Fin N) (h : l i0 ≠ 0) :
    ((univ.filter (fun b : Fin N → K => ∑ i, l i * b i = 0)).card : ℚ)
      / (Fintype.card K : ℚ) ^ N = 1 / Fintype.card K := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i0.elim0)
  have hq : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [las_vegas_count l i0 h]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_pow, pow_succ]
  field_simp

/-- Independence form (§7(i)): the nonzero vector `Λ ω` depends on data `ω` independent of the
uniform `b`; the number of pairs `(ω, b)` with `∑ Λ(ω)_i b_i = 0` is `|Ω| q^(N-1)`. -/
theorem las_vegas_indep {Ω : Type*} [Fintype Ω] (Λ : Ω → Fin N → K) (hΛ : ∀ ω, Λ ω ≠ 0) :
    (univ.filter (fun x : Ω × (Fin N → K) => ∑ i, Λ x.1 i * x.2 i = 0)).card
      = Fintype.card Ω * Fintype.card K ^ (N - 1) := by
  classical
  have hfib : ∀ ω : Ω, ((univ.filter (fun x : Ω × (Fin N → K) => ∑ i, Λ x.1 i * x.2 i = 0)).filter
      (fun x => x.1 = ω)).card = Fintype.card K ^ (N - 1) := by
    intro ω
    obtain ⟨i0, hi0⟩ : ∃ i0, Λ ω i0 ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hΛ ω (funext hcon)
    rw [← las_vegas_count (Λ ω) i0 hi0 0]
    refine card_bij (fun x _ => x.2) ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [← hx.2]; exact hx.1
    · intro a ha b hb hab
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Prod.ext (ha.2.trans hb.2.symm) hab
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact ⟨(ω, b), by simp [hb], rfl⟩
  rw [card_eq_sum_card_fiberwise (f := fun x : Ω × (Fin N → K) => x.1) (t := univ)
    (by intro _ _; simp)]
  simp [hfib]

end ECDLP.L40
