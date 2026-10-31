import Mathlib
import ECDLP.L49_Iso
import ECDLP.L46_Avg

/-!
# L49 (2): the dilation-nondegeneracy hypothesis and the average energy over `u ∈ Kˣ`

Fixed curve `E : y² = x³ + A x + B`; `E_u : y² = x³ + u⁴A x + u⁶B` (`Eu A B u`, an abbreviation of
`shortW (u⁴A) (u⁶B)`), `u ∈ Kˣ`.

`DilationNondeg A B m T D'` is the single mathematical input for the average energy bound over dilations
(Lemma N' with Lemma W): for every non-trivial `2m`-tuple `t ∈ T^{2m}` of x-values the number of
`u ∈ Kˣ` for which some `2m` nonzero points of `E_u` with x-coordinates `t` sum to `O` is `≤ 2D'`
(the polynomial `g_t(s) = f_{2m}(s t; A, B)` has degree `≤ D'` in `s = u⁻²`; `u ↦ u⁻²` is 2-to-1).

`avg_energy_dil` : `∑_u Eng(E_u) ≤ M·|Kˣ|` with `M = dfac·4^m X^m + 4^m·2D'·X^{2m}/|Kˣ|`.
-/
namespace ECDLP.L49

open Finset ECDLP.L40 ECDLP.L43 ECDLP.L46

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- the parameter vector of `E_u` -/
def θu (A B : K) (u : Kˣ) : Fin 2 → K := ![(u : K) ^ 4 * A, (u : K) ^ 6 * B]

/-- **Hypothesis (Lemma N′ + degree bound for dilations).** -/
def DilationNondeg (A B : K) (m : ℕ) (T : Finset K) (D' : ℕ) : Prop :=
  ∀ t : Fin (2 * m) → K, (∀ i, t i ∈ T) → ¬ TrivL (List.ofFn t) →
    (univ.filter (fun u : Kˣ => ∃ P : Fin (2 * m) → (Eu A B u).Point,
      (∀ i, P i ≠ 0 ∧ xco _ (P i) = t i) ∧ ∑ i, P i = 0)).card ≤ 2 * D'

/-- a `Rel`-tuple gives `2m` nonzero points with the given x-coordinates summing to `O` -/
theorem rel_to_pts {m : ℕ} (θ : Fin 2 → K) (u : Fin (2 * m) → K × K) (hR : Rel m θ u) :
    ∃ P : Fin (2 * m) → (shortW (θ 0) (θ 1)).Point,
      (∀ i, P i ≠ 0 ∧ xco _ (P i) = (u i).1) ∧ ∑ i, P i = 0 := by
  obtain ⟨hd, hns, hsum⟩ := hR
  set W := shortW (θ 0) (θ 1) with hW
  let P' : Fin (2 * m) → W.Point := fun i =>
    if (i : ℕ) < m then ECDLP.L30.ptOf W (u i) else -ECDLP.L30.ptOf W (u i)
  have hne : ∀ i, P' i ≠ 0 := by
    intro i
    have := ECDLP.L30.ptOf_ne_zero (hns i)
    simp only [P']; split_ifs
    · exact this
    · exact neg_ne_zero.2 this
  have hx : ∀ i, xco _ (P' i) = (u i).1 := by
    intro i
    simp only [P']; split_ifs
    · exact xco_ptOf (hns i)
    · rw [xco_neg]; exact xco_ptOf (hns i)
  refine ⟨P', fun i => ⟨hne i, hx i⟩, ?_⟩
  rw [sum_split]
  have h1 : ∀ j : Fin m, P' (lo m j) = ECDLP.L30.ptOf W (u (lo m j)) := by
    intro j; simp only [P', lo]; rw [if_pos j.isLt]
  have h2 : ∀ j : Fin m, P' (hi m j) = -ECDLP.L30.ptOf W (u (hi m j)) := by
    intro j; simp only [P', hi]; rw [if_neg (by omega)]
  simp only [h1, h2, sum_neg_distrib]
  rw [hsum]; exact add_neg_cancel _

open Classical in
/-- bad set over dilations: pairs `(u, v)` with `v` a `2m`-tuple of factor-base points of `E_u`
satisfying `Rel` -/
noncomputable def badU (A B : K) (m : ℕ) (T : Finset K) : Finset (Kˣ × (Fin (2 * m) → K × K)) :=
  (univ : Finset (Kˣ × (Fin (2 * m) → K × K))).filter
    (fun x => (∀ i, x.2 i ∈ curvePts (θu A B x.1) T) ∧ Rel m (θu A B x.1) x.2)

/-- skeleton of the average energy bound over dilations -/
theorem badU_card (A B : K) (m D' : ℕ) (T : Finset K) (hN : DilationNondeg A B m T D') :
    (badU A B m T).card ≤
      dfac m * 4 ^ m * T.card ^ m * Fintype.card Kˣ
        + 4 ^ m * (2 * D') * T.card ^ (2 * m) := by
  classical
  set Tt : Finset (Fin (2 * m) → K) := Fintype.piFinset (fun _ => T) with hTt
  set xs : Kˣ × (Fin (2 * m) → K × K) → (Fin (2 * m) → K) := fun x i => (x.2 i).1
  have hmaps : (↑(badU A B m T) : Set _).MapsTo xs ↑Tt := by
    intro x hx
    simp only [badU, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
    simp only [hTt, mem_coe, Fintype.mem_piFinset]
    intro i
    have := hx.1 i
    simp only [curvePts, mem_filter, mem_product] at this
    exact this.1.1
  rw [card_eq_sum_card_fiberwise hmaps]
  have key : ∀ t ∈ Tt, ∀ Us : Finset Kˣ,
      (∀ x ∈ (badU A B m T).filter (fun x => xs x = t), x.1 ∈ Us) →
      ((badU A B m T).filter (fun x => xs x = t)).card ≤ Us.card * 4 ^ m := by
    intro t _ Us hUs
    rw [card_eq_sum_card_fiberwise (f := fun x => x.1) (t := Us) (fun x hx => hUs x hx)]
    calc _ ≤ ∑ _u ∈ Us, 4 ^ m := by
          refine sum_le_sum (fun u _ => ?_)
          refine le_trans (card_le_card_of_injOn (fun x => x.2)
            (t := (Fintype.piFinset (fun _ : Fin (2 * m) => curvePts (θu A B u) T)).filter
              (fun v => ∀ i, (v i).1 = t i)) ?_ ?_) (card_lifts m T (θu A B u) t)
          · intro x hx
            simp only [coe_filter, badU, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
            obtain ⟨⟨⟨h1, _⟩, hxt⟩, rfl⟩ := hx
            simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq]
            exact ⟨h1, fun i => congrFun hxt i⟩
          · intro x hx y hy hxy
            simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
            exact Prod.ext (hx.2.trans hy.2.symm) hxy
      _ = Us.card * 4 ^ m := by simp
  have hbound : ∀ t ∈ Tt, ((badU A B m T).filter (fun x => xs x = t)).card ≤
      if TrivL (List.ofFn t) then Fintype.card Kˣ * 4 ^ m else (2 * D') * 4 ^ m := by
    intro t ht
    split_ifs with htr
    · exact key t ht univ (fun _ _ => mem_univ _)
    · have htT : ∀ i, t i ∈ T := by simpa [hTt, Fintype.mem_piFinset] using ht
      refine (key t ht _ ?_).trans (Nat.mul_le_mul_right _ (hN t htT htr))
      intro x hx
      simp only [mem_filter, badU, mem_univ, true_and] at hx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      have h3' : (fun i => (x.2 i).1) = t := h3
      simp only [mem_filter, mem_univ, true_and]
      obtain ⟨P, hP, hs⟩ := rel_to_pts _ _ h2
      refine ⟨P, fun i => ⟨(hP i).1, ?_⟩, hs⟩
      exact ((hP i).2).trans (congrFun h3' i)
  calc ∑ t ∈ Tt, ((badU A B m T).filter (fun x => xs x = t)).card
      ≤ ∑ t ∈ Tt, (if TrivL (List.ofFn t) then Fintype.card Kˣ * 4 ^ m
          else (2 * D') * 4 ^ m) := sum_le_sum hbound
    _ = (Tt.filter (fun t => TrivL (List.ofFn t))).card * (Fintype.card Kˣ * 4 ^ m)
        + (Tt.filter (fun t => ¬ TrivL (List.ofFn t))).card * ((2 * D') * 4 ^ m) := by
      rw [← sum_filter_add_sum_filter_not Tt (fun t => TrivL (List.ofFn t))]
      congr 1
      · rw [sum_congr rfl (fun t ht => if_pos (mem_filter.1 ht).2)]; simp
      · rw [sum_congr rfl (fun t ht => if_neg (mem_filter.1 ht).2)]; simp
    _ ≤ (dfac m * T.card ^ m) * (Fintype.card Kˣ * 4 ^ m)
        + (T.card ^ (2 * m)) * ((2 * D') * 4 ^ m) := by
      gcongr
      · exact card_trivial_tuples T m
      · calc _ ≤ Tt.card := card_filter_le _ _
          _ = T.card ^ (2 * m) := by simp [hTt, Fintype.card_piFinset]
    _ = _ := by ring

/-- `Eng(E_u)` is at most the fibre of `badU` over `u` -/
theorem eng_le_badU (hK : ringChar K ≠ 2) (T : Finset K) (n : ℕ) (A B : K) (u : Kˣ)
    (hd : disc ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ≠ 0) :
    Eng T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ≤
      ((badU A B (n + 1) T).filter (fun x => x.1 = u)).card := by
  classical
  refine (eng_le_fiber hK T n _ _ hd).trans ?_
  refine card_le_card_of_injOn (fun x => (u, x.2)) ?_ ?_
  · intro x hx
    simp only [coe_filter, badSet, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have e : x.1 = θu A B u := by rw [h3]; rfl
    simp only [coe_filter, badU, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← e]
    exact ⟨⟨h1, h2⟩, trivial⟩
  · intro x hx y hy h
    simp only [coe_filter, Set.mem_ofPred_eq, badSet, mem_filter, mem_univ, true_and] at hx hy
    have e : x.2 = y.2 := (Prod.mk.inj h).2
    exact Prod.ext (hx.2.trans hy.2.symm) e

end ECDLP.L49

namespace ECDLP.L49
open Finset
theorem fiber_univ' {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (B : Finset (Kˣ × (Fin (2 * m) → K × K))) :
    B.card = ∑ u : Kˣ, (B.filter (fun x => x.1 = u)).card :=
  card_eq_sum_card_fiberwise (fun x _ => by simp)
end ECDLP.L49
