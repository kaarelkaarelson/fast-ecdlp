import Mathlib
import ECDLP.L40_Skeleton
import ECDLP.L46_Bridge

/-!
# L46 (2a): the relation `Rel` of L40's skeleton, in Mathlib's group law, and `SemaevNondeg`

`Rel m θ u` (for `θ = (A,B)`, `u : Fin (2m) → K × K`): `Δ(A,B) ≠ 0`, all `u i` are nonsingular points
of `y² = x³ + A x + B`, and `P_1 + … + P_m = Q_1 + … + Q_m` in Mathlib's group `(shortW A B).Point`,
where `P_j = u(lo j)`, `Q_j = u(hi j)`.

`SemaevNondeg m T D` : the single mathematical hypothesis (Semaev's vanishing, Lemma W, Lemma N).
-/
namespace ECDLP.L46

open Finset ECDLP.L40 ECDLP.L43

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- first half index -/
def lo (m : ℕ) (j : Fin m) : Fin (2 * m) := ⟨j, by omega⟩
/-- second half index -/
def hi (m : ℕ) (j : Fin m) : Fin (2 * m) := ⟨m + j, by omega⟩

theorem sum_split {G : Type*} [AddCommMonoid G] (m : ℕ) (g : Fin (2 * m) → G) :
    ∑ i, g i = ∑ j : Fin m, g (lo m j) + ∑ j : Fin m, g (hi m j) := by
  have h := Fin.sum_univ_add (a := m) (b := m) (fun i : Fin (m + m) => g (Fin.cast (two_mul m).symm i))
  have e : ∑ i : Fin (m + m), g (Fin.cast (two_mul m).symm i) = ∑ i, g i :=
    Equiv.sum_comp (finCongr (two_mul m).symm) g
  rw [← e, h]
  rfl

/-- the relation `P_1+…+P_m = Q_1+…+Q_m` in the group of `y² = x³+Ax+B`, for coordinates `u`. -/
def Rel (m : ℕ) (θ : Fin 2 → K) (u : Fin (2 * m) → K × K) : Prop :=
  disc (θ 0) (θ 1) ≠ 0 ∧ (∀ i, (shortW (θ 0) (θ 1)).Nonsingular (u i).1 (u i).2) ∧
    ∑ j : Fin m, ECDLP.L30.ptOf (shortW (θ 0) (θ 1)) (u (lo m j))
      = ∑ j : Fin m, ECDLP.L30.ptOf (shortW (θ 0) (θ 1)) (u (hi m j))

/-- **The one mathematical hypothesis** (Semaev's summation polynomials, Lemmas W and N):
there are polynomials `f t ∈ K[A,B]`, indexed by the `2m`-tuples `t` of x-values, with
* (W) `deg f t ≤ D`;
* (Semaev vanishing) if affine points `P_i` of `y² = x³+Ax+B` (`Δ ≠ 0`, `x(P_i) ∈ T`) sum to `O`
  in the group law then `f (x(P_1),…,x(P_{2m})) (A,B) = 0`;
* (N) `f t ≠ 0` whenever `t ∈ T^{2m}` is non-trivial (some value of odd multiplicity). -/
def SemaevNondeg (m : ℕ) (T : Finset K) (D : ℕ) : Prop :=
  ∃ f : (Fin (2 * m) → K) → MvPolynomial (Fin 2) K,
    (∀ t, (f t).totalDegree ≤ D) ∧
    (∀ A B : K, disc A B ≠ 0 → ∀ P : Fin (2 * m) → (shortW A B).Point,
      (∀ i, P i ≠ 0 ∧ xco _ (P i) ∈ T) → ∑ i, P i = 0 →
        MvPolynomial.eval ![A, B] (f (fun i => xco _ (P i))) = 0) ∧
    (∀ t, (∀ i, t i ∈ T) → ¬ TrivL (List.ofFn t) → f t ≠ 0)

theorem xco_neg {W : WeierstrassCurve.Affine K} (P : W.Point) : xco W (-P) = xco W P := by
  cases P with
  | zero => rw [show (WeierstrassCurve.Affine.Point.zero : W.Point) = 0 from rfl, neg_zero]
  | some x y h => simp [xco, WeierstrassCurve.Affine.Point.neg_some]

theorem neg_ne_zero' {W : WeierstrassCurve.Affine K} (P : W.Point) (h : P ≠ 0) : -P ≠ 0 :=
  neg_ne_zero.2 h

end ECDLP.L46
