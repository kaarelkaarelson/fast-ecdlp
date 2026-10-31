import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# L30 / Step: the generic-addition constraints are exactly the group law

For a Weierstrass curve `W` over a field `F` we define the constraint system of one
*generic addition* `S = A + B` (network gadgets "inv", "slope", "xsum", "ysum"):

* `w * (xB - xA) = 1`
* `λ = (yB - yA) * w`
* `xS = addX xA xB λ`,  `yS = addY xA xB yA λ`  (Mathlib's formulas)

and prove that, for nonsingular `A, B`, they hold iff `xA ≠ xB`, `w`, `λ` are the inverse and the
Mathlib slope, and `some xS yS _ = some xA yA _ + some xB yB _` in `W.Point`.
In the short Weierstrass case the formulas are exactly the network's.
-/

set_option linter.unusedSectionVars false

namespace ECDLP.L30

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Generic-addition constraints, with Mathlib's `addX`/`addY`. -/
def StepC (xA yA xB yB w l xS yS : F) : Prop :=
  w * (xB - xA) = 1 ∧ l = (yB - yA) * w ∧ xS = W.addX xA xB l ∧ yS = W.addY xA xB yA l

/-- Generic-addition constraints in the network's form for short Weierstrass curves
(`netlib.py`, gadgets inv/slope/xsum/ysum): all are polynomial identities
`E = 0` in `F`. -/
def StepL27 (xA yA xB yB w l xS yS : F) : Prop :=
  w * (xB - xA) - 1 = 0 ∧
  l * (xB - xA) - (yB - yA) = 0 ∧
  l * l - xA - xB - xS = 0 ∧
  l * xA - l * xS - yS - yA = 0

/-- **generic addition = group law**.** -/
theorem stepC_iff {xA yA xB yB : F} (hA : W.Nonsingular xA yA) (hB : W.Nonsingular xB yB)
    (w l xS yS : F) :
    StepC W xA yA xB yB w l xS yS ↔
      (xA ≠ xB ∧ w = (xB - xA)⁻¹ ∧ l = W.slope xA xB yA yB ∧
        ∃ hS : W.Nonsingular xS yS,
          Point.some xS yS hS = Point.some xA yA hA + Point.some xB yB hB) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hne : xA ≠ xB := by
      rintro rfl
      simp at h1
    have hsub : xB - xA ≠ 0 := sub_ne_zero.mpr hne.symm
    have hw : w = (xB - xA)⁻¹ := by
      field_simp at h1 ⊢
      linear_combination h1
    have hl : l = W.slope xA xB yA yB := by
      rw [slope_of_X_ne hne, h2, hw]
      have : xA - xB = -(xB - xA) := by ring
      rw [this, div_neg, ← neg_div, neg_sub]
      rw [div_eq_mul_inv]
    refine ⟨hne, hw, hl, ?_⟩
    rw [Point.add_of_X_ne hne]
    subst h3 h4
    rw [hl]
    exact ⟨nonsingular_add hA hB fun hxy => hne hxy.left, rfl⟩
  · rintro ⟨hne, hw, hl, hS, hEq⟩
    rw [Point.add_of_X_ne hne] at hEq
    simp only [Point.some.injEq] at hEq
    obtain ⟨hx, hy⟩ := hEq
    have hsub : xB - xA ≠ 0 := sub_ne_zero.mpr hne.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hw]; exact inv_mul_cancel₀ hsub
    · rw [hl, slope_of_X_ne hne, hw]
      have : xA - xB = -(xB - xA) := by ring
      rw [this, div_neg, ← neg_div, neg_sub, div_eq_mul_inv]
    · rw [hx, hl]
    · rw [hy, hl]

/-- Existential form: given nonsingular `A`, `B`, the constraints are satisfiable (for some `w, λ`)
iff `xA ≠ xB` and `(xS, yS) = A + B`. The witnesses are unique. -/
theorem exists_stepC_iff {xA yA xB yB : F} (hA : W.Nonsingular xA yA) (hB : W.Nonsingular xB yB)
    (xS yS : F) :
    (∃ w l, StepC W xA yA xB yB w l xS yS) ↔
      (xA ≠ xB ∧ ∃ hS : W.Nonsingular xS yS,
          Point.some xS yS hS = Point.some xA yA hA + Point.some xB yB hB) := by
  constructor
  · rintro ⟨w, l, h⟩
    obtain ⟨h1, _, _, h2⟩ := (stepC_iff W hA hB w l xS yS).1 h
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, _, (stepC_iff W hA hB _ _ xS yS).2 ⟨h1, rfl, rfl, h2⟩⟩

theorem stepC_unique {xA yA xB yB w l xS yS w' l' xS' yS' : F}
    (h : StepC W xA yA xB yB w l xS yS) (h' : StepC W xA yA xB yB w' l' xS' yS') :
    w = w' ∧ l = l' ∧ xS = xS' ∧ yS = yS' := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  have hw : w = w' := by
    have : (xB - xA) ≠ 0 := by
      intro h0; rw [h0] at a1; simp at a1
    apply mul_right_cancel₀ this
    rw [a1, b1]
  subst hw
  have hl : l = l' := by rw [a2, b2]
  subst hl
  exact ⟨rfl, rfl, by rw [a3, b3], by rw [a4, b4]⟩

/-- Short Weierstrass case: the network's equations and `StepC` coincide. -/
theorem stepL27_iff_stepC (hW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (xA yA xB yB w l xS yS : F) :
    StepL27 xA yA xB yB w l xS yS ↔ StepC W xA yA xB yB w l xS yS := by
  obtain ⟨h1, h2, h3⟩ := hW
  unfold StepL27 StepC
  simp only [addX, addY, negY, negAddY, h1, h2, h3]
  constructor
  · rintro ⟨e1, e2, e3, e4⟩
    have e1' : w * (xB - xA) = 1 := by linear_combination e1
    have hsub : xB - xA ≠ 0 := by
      intro h0; rw [h0] at e1'; simp at e1'
    refine ⟨e1', ?_, ?_, ?_⟩
    · linear_combination (-l) * e1' + w * e2
    · linear_combination -e3
    · have hx : xS = l ^ 2 + 0 * l - 0 - xA - xB := by linear_combination -e3
      subst hx
      linear_combination -e4
  · rintro ⟨e1, e2, e3, e4⟩
    refine ⟨by linear_combination e1, ?_, ?_, ?_⟩
    · rw [e2]
      linear_combination (yB - yA) * e1
    · linear_combination -e3
    · subst e3
      linear_combination -e4
  
end ECDLP.L30
