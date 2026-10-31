import Mathlib
import ECDLP.L43_Cheb

/-!
# L43 (1): Mathlib Weierstrass points over a finite field as the abstract setting of L40

* `xc : W.Point → Option K` (`zero ↦ none`, `some x y _ ↦ some x`).
* `Fintype W.Point` (injection into `Option (K × K)`).
* x-fibres of any subset have at most 2 elements (`card_fibre_le_two`).
* for the short curve `y² = x³ + A x + B` with `Δ ≠ 0`, the factor base
  `fb T = {P ≠ 0 : x(P) ∈ T}` has `|fb T| = fsize T A B`.
-/
namespace ECDLP.L43

open Finset WeierstrassCurve WeierstrassCurve.Affine

section general

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- x-coordinate with `none` at infinity -/
def xc : W.Point → Option K
  | .zero => none
  | .some x _ _ => some x

/-- y-coordinate (junk at infinity) -/
def yco : W.Point → K
  | .zero => 0
  | .some _ y _ => y

/-- x-coordinate (junk at infinity) -/
def xco : W.Point → K
  | .zero => 0
  | .some x _ _ => x

theorem pt_ext {P Q : W.Point} (h : xc W P = xc W Q) (hy : yco W P = yco W Q) : P = Q := by
  cases P <;> cases Q <;> simp_all [xc, yco]

noncomputable instance instFintypePoint : Fintype W.Point :=
  haveI : Finite W.Point := Finite.of_injective
    (fun P : W.Point => (match P with | .zero => (none : Option (K × K)) | .some x y _ => some (x, y)))
    (by intro P Q h; cases P <;> cases Q <;> simp_all)
  Fintype.ofFinite _

/-- **x-fibres have at most two elements** in any subset of the points. -/
theorem card_fibre_le_two (F : Finset W.Point) (a : Option K) :
    (F.filter (fun P => xc W P = a)).card ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty (F.filter (fun P => xc W P = a)) with h | ⟨P0, hP0⟩
  · simp [h]
  rcases a with _ | x
  · -- only the point at infinity
    have : (F.filter (fun P => xc W P = none)).card ≤ 1 := by
      rw [card_le_one]
      intro P hP Q hQ
      simp only [mem_filter] at hP hQ
      cases P <;> cases Q <;> simp_all [xc]
    omega
  · simp only [mem_filter] at hP0
    cases hP : P0 with
    | zero => rw [hP] at hP0; simp [xc] at hP0
    | some x0 y0 h0 =>
      rw [hP] at hP0
      have hx0 : x0 = x := by simpa [xc] using hP0.2
      subst hx0
      have : (F.filter (fun P => xc W P = some x0)).card ≤ ({y0, W.negY x0 y0} : Finset K).card := by
        refine card_le_card_of_injOn (yco W) ?_ ?_
        · intro P hP
          simp only [coe_filter, Set.mem_ofPred_eq] at hP
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
          cases P with
          | zero => simp [xc] at hP
          | some x1 y1 h1 =>
            have hx1 : x1 = x0 := by simpa [xc] using hP.2
            subst hx1
            exact Y_eq_of_X_eq h1.1 h0.1 rfl
        · intro P hP Q hQ hy
          simp only [coe_filter, Set.mem_ofPred_eq] at hP hQ
          exact pt_ext W (hP.2.trans hQ.2.symm) hy
      exact this.trans (card_le_two)
  
end general

section short

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- the short Weierstrass curve `y² = x³ + A x + B` -/
def shortW (A B : K) : WeierstrassCurve.Affine K := ⟨0, 0, 0, A, B⟩

/-- discriminant polynomial -/
def disc (A B : K) : K := 4 * A ^ 3 + 27 * B ^ 2

theorem shortW_equation (A B x y : K) :
    (shortW A B).Equation x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  rw [equation_iff]; simp [shortW]

theorem shortW_Δ (A B : K) : (shortW A B).Δ = -16 * disc A B := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, shortW, disc]; ring

theorem shortW_nonsing (hK : ringChar K ≠ 2) (A B : K) (h : disc A B ≠ 0) (x y : K) :
    (shortW A B).Nonsingular x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  have h16 : (-16 : K) ≠ 0 := by
    have : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have h' : (-16 : K) = -(2 ^ 4) := by norm_num
    rw [h']; exact neg_ne_zero.2 (pow_ne_zero _ this)
  rw [← shortW_equation, ← equation_iff_nonsingular_of_Δ_ne_zero]
  rw [shortW_Δ]; exact mul_ne_zero h16 h

/-- the factor base: finite points with x-coordinate in `T` -/
noncomputable def fb (A B : K) (T : Finset K) : Finset (shortW A B).Point :=
  univ.filter (fun P => xc _ P ≠ none ∧ xco _ P ∈ T)

theorem card_fb (hK : ringChar K ≠ 2) (A B : K) (h : disc A B ≠ 0) (T : Finset K) :
    ((fb A B T).card : ℤ) = fsize T A B := by
  classical
  unfold fsize
  have hmaps : ∀ P ∈ fb A B T, xco _ P ∈ T := fun P hP => (mem_filter.1 hP).2.2
  have h1 : (fb A B T).card = ∑ x ∈ T, ((fb A B T).filter (fun P => xco _ P = x)).card :=
    card_eq_sum_card_fiberwise (f := fun P => xco _ P) (fun P hP => hmaps P hP)
  have h2 : ∀ x ∈ T, ((fb A B T).filter (fun P => xco _ P = x)).card
      = (({y : K | y ^ 2 = x ^ 3 + A * x + B} : Set K).toFinset).card := by
    intro x hx
    refine card_bij (fun P _ => yco _ P) ?_ ?_ ?_
    · intro P hP
      simp only [mem_filter, fb, mem_univ, true_and] at hP
      obtain ⟨⟨hne, _⟩, hxe⟩ := hP
      cases P with
      | zero => simp [xc] at hne
      | some x1 y1 h1 =>
        simp only [xco] at hxe; subst hxe
        simpa [yco] using (shortW_nonsing hK A B h _ _).1 h1
    · intro P hP Q hQ hy
      simp only [mem_filter, fb, mem_univ, true_and] at hP hQ
      obtain ⟨⟨hne, _⟩, hxe⟩ := hP
      obtain ⟨⟨hne', _⟩, hxe'⟩ := hQ
      refine pt_ext _ ?_ hy
      cases P <;> cases Q <;> simp_all [xc, xco]
    · intro y hy
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hy
      refine ⟨Point.some x y ((shortW_nonsing hK A B h x y).2 hy), ?_, rfl⟩
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, by simp [xc], hx⟩, rfl⟩
  rw [h1, sum_congr rfl h2]
  push_cast
  refine sum_congr rfl (fun x _ => ?_)
  have := quadraticChar_card_sqrts hK (x ^ 3 + A * x + B)
  rw [show 1 + (quadraticChar K) (x ^ 3 + A * x + B) = (quadraticChar K) (x ^ 3 + A * x + B) + 1 from add_comm _ _]
  exact_mod_cast this

end short

end ECDLP.L43
