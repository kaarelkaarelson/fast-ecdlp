import Mathlib
import ECDLP.L40_Trivial

/-!
# L40 (3): counting skeleton of the average-energy bound

Parameters `θ = (A,B) : Fin 2 → K` (`K` a finite field); the factor-base points over `θ` are
`curvePts θ T = {(x,y) | x ∈ T, y² = x³ + A x + B}`.  `Rel θ u` is an *abstract* relation on a
`2m`-tuple of points (in the application: `P₁+…+P_m = Q₁+…+Q_m`, `u = (P,Q)`).  The two inputs
from the Semaev/valuation theory are *hypotheses* (not proved here):

* `hsem` : if the relation holds then a fixed polynomial `f t ∈ K[A,B]` (`t` = tuple of
  x-coordinates) vanishes at `θ` (Semaev's theorem);
* `hN` : for non-trivial `t` (some x-value of odd multiplicity) `f t ≠ 0` (Lemma N);
* `hdeg` : `totalDegree (f t) ≤ D` (Lemma W).

Conclusion: the total number of `(θ,u)` with `u` a relation-tuple over `θ` is at most
`(2m-1)!! 4^m |T|^m q² + 4^m D |T|^{2m} q`  (`q = |K|`).

Note the constant `4^m` (= `2^{2m}`, two y-choices per point) in the trivial part.
-/
namespace ECDLP.L40

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- factor-base points over parameter `θ = (A,B)` -/
def curvePts (θ : Fin 2 → K) (T : Finset K) : Finset (K × K) :=
  (T ×ˢ (univ : Finset K)).filter (fun P => P.2 ^ 2 = P.1 ^ 3 + θ 0 * P.1 + θ 1)

/-- the y-values over x -/
def fib (θ : Fin 2 → K) (x : K) : Finset K :=
  (univ : Finset K).filter (fun y => y ^ 2 = x ^ 3 + θ 0 * x + θ 1)

theorem card_fib_le (θ : Fin 2 → K) (x : K) : (fib θ x).card ≤ 2 := by
  by_cases h : (fib θ x).Nonempty
  · obtain ⟨y0, hy0⟩ := h
    simp only [fib, mem_filter, mem_univ, true_and] at hy0
    have : fib θ x ⊆ {y0, -y0} := by
      intro y hy
      simp only [fib, mem_filter, mem_univ, true_and] at hy
      have : y ^ 2 = y0 ^ 2 := by rw [hy, hy0]
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h <;> simp [h]
    exact (card_le_card this).trans (card_le_two)
  · rw [not_nonempty_iff_eq_empty.1 h]; simp

/-- fibre bound: tuples over `θ` with prescribed x-coordinates `t` number at most `2^{2m}`. -/
theorem card_lifts (m : ℕ) (T : Finset K) (θ : Fin 2 → K) (t : Fin (2 * m) → K) :
    ((Fintype.piFinset (fun _ : Fin (2 * m) => curvePts θ T)).filter
      (fun u => ∀ i, (u i).1 = t i)).card ≤ 4 ^ m := by
  have hinj : Set.InjOn (fun u : Fin (2 * m) → K × K => fun i => (u i).2)
      ↑((Fintype.piFinset (fun _ : Fin (2 * m) => curvePts θ T)).filter
        (fun u => ∀ i, (u i).1 = t i)) := by
    intro u hu v hv huv
    simp only [coe_filter, Set.mem_ofPred_eq] at hu hv
    funext i
    exact Prod.ext ((hu.2 i).trans (hv.2 i).symm) (congrFun huv i)
  refine (card_le_card_of_injOn _ (t := Fintype.piFinset (fun i => fib θ (t i))) ?_ hinj).trans ?_
  · intro u hu
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq] at hu
    simp only [mem_coe, Fintype.mem_piFinset]
    intro i
    have h1 := hu.1 i
    simp only [curvePts, mem_filter, mem_product, mem_univ, and_true] at h1
    simp only [fib, mem_filter, mem_univ, true_and]
    rw [← hu.2 i]; exact h1.2
  · rw [Fintype.card_piFinset]
    calc ∏ i, (fib θ (t i)).card ≤ ∏ _i : Fin (2 * m), 2 :=
          prod_le_prod (fun i _ => card_fib_le θ (t i))
      _ = 4 ^ m := by simp [pow_mul]

/-- number of zeros of a nonzero polynomial of total degree ≤ D in `K²`: at most `D q`. -/
theorem card_zeros_le (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0) (D : ℕ) (hD : p.totalDegree ≤ D) :
    ((univ : Finset (Fin 2 → K)).filter (fun θ => MvPolynomial.eval θ p = 0)).card
      ≤ D * Fintype.card K := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset K)
  have hq : (0 : NNRat) < (Fintype.card K : NNRat) := by exact_mod_cast Fintype.card_pos
  have e : (Fintype.piFinset fun _ : Fin 2 => (univ : Finset K)) = univ := by ext; simp
  rw [e] at h
  simp only [card_univ] at h
  rw [div_le_div_iff₀ (by positivity) hq] at h
  have h2 : (((univ : Finset (Fin 2 → K)).filter (fun θ => MvPolynomial.eval θ p = 0)).card : NNRat)
      * Fintype.card K ≤ p.totalDegree * (Fintype.card K : NNRat) ^ 2 := h
  have h3 : ((univ : Finset (Fin 2 → K)).filter (fun θ => MvPolynomial.eval θ p = 0)).card
      * Fintype.card K ≤ p.totalDegree * Fintype.card K ^ 2 := by exact_mod_cast h2
  have h4 : ((univ : Finset (Fin 2 → K)).filter (fun θ => MvPolynomial.eval θ p = 0)).card
      * Fintype.card K ≤ (D * Fintype.card K) * Fintype.card K := by
    calc _ ≤ p.totalDegree * Fintype.card K ^ 2 := h3
      _ ≤ D * Fintype.card K ^ 2 := Nat.mul_le_mul_right _ hD
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h4 Fintype.card_pos

/-- The bad set: pairs `(θ,u)` with `u` a `2m`-tuple of factor-base points over `θ` satisfying `Rel`. -/
def badSet (m : ℕ) (T : Finset K) (Rel : (Fin 2 → K) → (Fin (2 * m) → K × K) → Prop)
    [DecidablePred (fun x : (Fin 2 → K) × (Fin (2 * m) → K × K) => Rel x.1 x.2)] :
    Finset ((Fin 2 → K) × (Fin (2 * m) → K × K)) :=
  (univ : Finset ((Fin 2 → K) × (Fin (2 * m) → K × K))).filter
    (fun x => (∀ i, x.2 i ∈ curvePts x.1 T) ∧ Rel x.1 x.2)

/-- **Skeleton.**  -/
theorem avg_energy_skeleton (m : ℕ) (T : Finset K) (D : ℕ)
    (Rel : (Fin 2 → K) → (Fin (2 * m) → K × K) → Prop)
    [DecidablePred (fun x : (Fin 2 → K) × (Fin (2 * m) → K × K) => Rel x.1 x.2)]
    (f : (Fin (2 * m) → K) → MvPolynomial (Fin 2) K)
    (hsem : ∀ θ u, (∀ i, u i ∈ curvePts θ T) → Rel θ u →
      MvPolynomial.eval θ (f (fun i => (u i).1)) = 0)
    (hdeg : ∀ t, (f t).totalDegree ≤ D)
    (hN : ∀ t, (∀ i, t i ∈ T) → ¬ TrivL (List.ofFn t) → f t ≠ 0) :
    (badSet m T Rel).card ≤
      dfac m * 4 ^ m * T.card ^ m * Fintype.card K ^ 2
        + 4 ^ m * D * T.card ^ (2 * m) * Fintype.card K := by
  classical
  set Tt : Finset (Fin (2 * m) → K) := Fintype.piFinset (fun _ => T) with hTt
  set xs : (Fin 2 → K) × (Fin (2 * m) → K × K) → (Fin (2 * m) → K) := fun x i => (x.2 i).1
  have hmaps : (↑(badSet m T Rel) : Set _).MapsTo xs ↑Tt := by
    intro x hx
    simp only [badSet, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
    simp only [hTt, mem_coe, Fintype.mem_piFinset]
    intro i
    have := hx.1 i
    simp only [curvePts, mem_filter, mem_product] at this
    exact this.1.1
  rw [card_eq_sum_card_fiberwise hmaps]
  -- per-fibre bound
  have key : ∀ t ∈ Tt, ∀ Θ : Finset (Fin 2 → K),
      (∀ x ∈ (badSet m T Rel).filter (fun x => xs x = t), x.1 ∈ Θ) →
      ((badSet m T Rel).filter (fun x => xs x = t)).card ≤ Θ.card * 4 ^ m := by
    intro t _ Θ hΘ
    rw [card_eq_sum_card_fiberwise (f := fun x => x.1) (t := Θ) (fun x hx => hΘ x hx)]
    calc _ ≤ ∑ _θ ∈ Θ, 4 ^ m := by
          refine sum_le_sum (fun θ _ => ?_)
          refine le_trans (card_le_card_of_injOn (fun x => x.2)
            (t := (Fintype.piFinset (fun _ : Fin (2 * m) => curvePts θ T)).filter
              (fun u => ∀ i, (u i).1 = t i)) ?_ ?_) (card_lifts m T θ t)
          · intro x hx
            simp only [coe_filter, badSet, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
            obtain ⟨⟨⟨h1, _⟩, hxt⟩, rfl⟩ := hx
            simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq]
            exact ⟨h1, fun i => congrFun hxt i⟩
          · intro x hx y hy hxy
            simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
            exact Prod.ext (hx.2.trans hy.2.symm) hxy
      _ = Θ.card * 4 ^ m := by simp
  have hbound : ∀ t ∈ Tt, ((badSet m T Rel).filter (fun x => xs x = t)).card ≤
      if TrivL (List.ofFn t) then Fintype.card K ^ 2 * 4 ^ m else D * Fintype.card K * 4 ^ m := by
    intro t ht
    split_ifs with htr
    · refine (key t ht univ (fun _ _ => mem_univ _)).trans ?_
      simp [Fintype.card_fun, Fintype.card_fin]
    · have htT : ∀ i, t i ∈ T := by simpa [hTt, Fintype.mem_piFinset] using ht
      have hf := hN t htT htr
      refine (key t ht ((univ : Finset (Fin 2 → K)).filter
        (fun θ => MvPolynomial.eval θ (f t) = 0)) ?_).trans ?_
      · intro x hx
        simp only [mem_filter, badSet, mem_univ, true_and] at hx
        obtain ⟨⟨h1, h2⟩, h3⟩ := hx
        have := hsem x.1 x.2 h1 h2
        have h3' : (fun i => (x.2 i).1) = t := h3
        rw [h3'] at this
        simpa using this
      · exact Nat.mul_le_mul_right _ (card_zeros_le (f t) hf D (hdeg t))
  calc ∑ t ∈ Tt, ((badSet m T Rel).filter (fun x => xs x = t)).card
      ≤ ∑ t ∈ Tt, (if TrivL (List.ofFn t) then Fintype.card K ^ 2 * 4 ^ m
          else D * Fintype.card K * 4 ^ m) := sum_le_sum hbound
    _ = (Tt.filter (fun t => TrivL (List.ofFn t))).card * (Fintype.card K ^ 2 * 4 ^ m)
        + (Tt.filter (fun t => ¬ TrivL (List.ofFn t))).card * (D * Fintype.card K * 4 ^ m) := by
      rw [← sum_filter_add_sum_filter_not Tt (fun t => TrivL (List.ofFn t))]
      congr 1
      · rw [sum_congr rfl (fun t ht => if_pos (mem_filter.1 ht).2)]; simp
      · rw [sum_congr rfl (fun t ht => if_neg (mem_filter.1 ht).2)]; simp
    _ ≤ (dfac m * T.card ^ m) * (Fintype.card K ^ 2 * 4 ^ m)
        + (T.card ^ (2 * m)) * (D * Fintype.card K * 4 ^ m) := by
      gcongr
      · exact card_trivial_tuples T m
      · calc _ ≤ Tt.card := card_filter_le _ _
          _ = T.card ^ (2 * m) := by simp [hTt, Fintype.card_piFinset]
    _ = _ := by ring

end ECDLP.L40
