import Mathlib
import ECDLP.L43_Curve

/-!
# L49 (1): the isomorphism `E → E_u`, `(x,y) ↦ (u²x, u³y)`, of Mathlib's point groups

`E : y² = x³ + A x + B`, `E_u : y² = x³ + u⁴A x + u⁶B`, `u ∈ Kˣ` (any field).  Mathlib has no
group map for `VariableChange`, so we build it by hand: `dil A B u : E.Point →+ E_u.Point`
and `xco (dil P) = u² xco P`; `dilEquiv` is an additive isomorphism.
-/
namespace ECDLP.L49

open WeierstrassCurve WeierstrassCurve.Affine ECDLP.L43

variable {K : Type*} [Field K] [DecidableEq K]

/-- the dilated curve `E_u` -/
abbrev Eu (A B : K) (u : Kˣ) : WeierstrassCurve.Affine K := shortW ((u : K) ^ 4 * A) ((u : K) ^ 6 * B)

theorem ns_dil (A B : K) (u : Kˣ) {x y : K} (h : (shortW A B).Nonsingular x y) :
    (Eu A B u).Nonsingular ((u : K) ^ 2 * x) ((u : K) ^ 3 * y) := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  rw [nonsingular_iff'] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [equation_iff] at he ⊢
    simp only [Eu, shortW] at he ⊢
    linear_combination (u : K) ^ 6 * he
  · simp only [Eu, shortW] at hn ⊢
    rcases hn with hn | hn
    · left
      have e : (0 : K) * ((u : K) ^ 3 * y) - (3 * ((u : K) ^ 2 * x) ^ 2 + 2 * 0 * ((u : K) ^ 2 * x)
          + (u : K) ^ 4 * A) = (u : K) ^ 4 * (0 * y - (3 * x ^ 2 + 2 * 0 * x + A)) := by ring
      rw [e]; exact mul_ne_zero (pow_ne_zero _ hu) hn
    · right
      have e : 2 * ((u : K) ^ 3 * y) + 0 * ((u : K) ^ 2 * x) + 0
          = (u : K) ^ 3 * (2 * y + 0 * x + 0) := by ring
      rw [e]; exact mul_ne_zero (pow_ne_zero _ hu) hn

/-- the map on points -/
def dilFun (A B : K) (u : Kˣ) : (shortW A B).Point → (Eu A B u).Point
  | .zero => .zero
  | .some x y h => .some _ _ (ns_dil A B u h)

theorem dilFun_zero (A B : K) (u : Kˣ) : dilFun A B u 0 = 0 := rfl

theorem dilFun_neg (A B : K) (u : Kˣ) (P : (shortW A B).Point) :
    dilFun A B u (-P) = -dilFun A B u P := by
  cases P with
  | zero => rw [show (Point.zero : (shortW A B).Point) = 0 from rfl, neg_zero]; rfl
  | some x y h =>
    simp only [Point.neg_some, dilFun]
    congr 1 <;> simp [negY, shortW, Eu] <;> ring

theorem slope_dil (A B : K) (u : Kˣ) (x1 x2 y1 y2 : K) :
    (Eu A B u).slope ((u : K) ^ 2 * x1) ((u : K) ^ 2 * x2) ((u : K) ^ 3 * y1) ((u : K) ^ 3 * y2)
      = (u : K) * (shortW A B).slope x1 x2 y1 y2 := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  unfold WeierstrassCurve.Affine.slope
  have hx : ((u : K) ^ 2 * x1 = (u : K) ^ 2 * x2) ↔ x1 = x2 :=
    mul_right_inj' (pow_ne_zero _ hu)
  have hy : ((u : K) ^ 3 * y1 = (Eu A B u).negY ((u : K) ^ 2 * x2) ((u : K) ^ 3 * y2)) ↔
      (y1 = (shortW A B).negY x2 y2) := by
    simp only [negY, Eu, shortW]
    constructor
    · intro h; have : (u : K) ^ 3 * y1 = (u : K) ^ 3 * (-y2 - 0 * x2 - 0) := by
        rw [h]; ring
      exact mul_left_cancel₀ (pow_ne_zero _ hu) this
    · intro h; rw [h]; ring
  by_cases hx1 : x1 = x2
  · by_cases hy1 : y1 = (shortW A B).negY x2 y2
    · rw [if_pos (hx.2 hx1), if_pos (hy.2 hy1), if_pos hx1, if_pos hy1, mul_zero]
    · rw [if_pos (hx.2 hx1), if_neg (fun h => hy1 (hy.1 h)), if_pos hx1, if_neg hy1]
      simp only [negY, Eu, shortW]
      have key : ∀ n d : K, ((u : K) ^ 4 * n) / ((u : K) ^ 3 * d) = (u : K) * (n / d) := by
        intro n d
        rw [show (u : K) ^ 4 * n = (u : K) ^ 3 * ((u : K) * n) by ring,
          mul_div_mul_left _ _ (pow_ne_zero 3 hu), mul_div_assoc]
      convert key (3 * x1 ^ 2 + A) (y1 - (-y1 - 0 * x1 - 0)) using 2 <;> ring
  · rw [if_neg (fun h => hx1 (hx.1 h)), if_neg hx1]
    field_simp

theorem dilFun_add (A B : K) (u : Kˣ) (P Q : (shortW A B).Point) :
    dilFun A B u (P + Q) = dilFun A B u P + dilFun A B u Q := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  cases P with
  | zero => rw [show (Point.zero : (shortW A B).Point) = 0 from rfl, zero_add, dilFun_zero, zero_add]
  | some x1 y1 h1 =>
    cases Q with
    | zero => rw [show (Point.zero : (shortW A B).Point) = 0 from rfl, add_zero, dilFun_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hxy : x1 = x2 ∧ y1 = (shortW A B).negY x2 y2
      · rw [Point.add_of_Y_eq hxy.1 hxy.2, dilFun_zero]
        symm
        simp only [dilFun]
        apply Point.add_of_Y_eq
        · rw [hxy.1]
        · rw [hxy.2]; simp [negY, Eu, shortW]
      · rw [Point.add_some hxy]
        simp only [dilFun]
        have hxy' : ¬((u : K) ^ 2 * x1 = (u : K) ^ 2 * x2 ∧
            (u : K) ^ 3 * y1 = (Eu A B u).negY ((u : K) ^ 2 * x2) ((u : K) ^ 3 * y2)) := by
          rintro ⟨a, b⟩
          apply hxy
          refine ⟨mul_left_cancel₀ (pow_ne_zero _ hu) a, ?_⟩
          simp only [negY, Eu, shortW] at b
          have : (u : K) ^ 3 * y1 = (u : K) ^ 3 * ((shortW A B).negY x2 y2) := by
            rw [b]; simp [negY, shortW]
          exact mul_left_cancel₀ (pow_ne_zero _ hu) this
        rw [Point.add_some hxy']
        congr 1
        · have hs := slope_dil A B u x1 x2 y1 y2
          simp only [addX, Eu, shortW] at hs ⊢
          rw [hs]
          ring
        · have hs := slope_dil A B u x1 x2 y1 y2
          simp only [addY, negAddY, negY, addX, Eu, shortW] at hs ⊢
          rw [hs]
          ring

/-- the group homomorphism `E → E_u` -/
def dil (A B : K) (u : Kˣ) : (shortW A B).Point →+ (Eu A B u).Point where
  toFun := dilFun A B u
  map_zero' := rfl
  map_add' := dilFun_add A B u

theorem xco_dil (A B : K) (u : Kˣ) (P : (shortW A B).Point) :
    ECDLP.L43.xco _ (dil A B u P) = (u : K) ^ 2 * ECDLP.L43.xco _ P := by
  show ECDLP.L43.xco _ (dilFun A B u P) = _
  cases P <;> simp [dilFun, ECDLP.L43.xco]

theorem dilFun_injective (A B : K) (u : Kˣ) : Function.Injective (dilFun A B u) := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some x y hh => cases h
  | some x y hh => cases Q with
    | zero => cases h
    | some x' y' hh' =>
      have h' := Point.some.inj h
      have e1 := mul_left_cancel₀ (pow_ne_zero 2 hu) h'.1
      have e2 := mul_left_cancel₀ (pow_ne_zero 3 hu) h'.2
      subst e1; subst e2; rfl

theorem dil_injective (A B : K) (u : Kˣ) : Function.Injective (dil A B u) :=
  dilFun_injective A B u

end ECDLP.L49
