import Mathlib.Computability.TuringMachine.Computable
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Set.Finite.List

/-!
# A fast algorithm for elliptic-curve discrete logarithms: the statement

This file is the statement for audit. It imports Mathlib only. It is a verbatim copy of
`ECDLP/L35_Challenge.lean` as cited in the paper (the audit statement of module `L35_Challenge`).

* **Input** `(p, a, b, xR, yR, π)`: the curve `y² = x³ + a x + b` over `ZMod p`, the target
  `R = (xR, yR)` and a prefix `π`; numbers in binary (`Computability.encodeNat`).
* **Output** `lexLeast m`: the lexicographically least string (for each `i`, the bits of `x(P_i)`
  then a sign bit of `y(P_i)`) of a generic decomposition `R = P₁ + … + P_m` with
  `x(P_i) < ⌈p^{1/m}⌉` that begins with `π`, or `none`.
* **Machines and time** are Mathlib's (`Turing.TM2ComputableInTime`); every stack alphabet is finite.

**The claim** (`ECDLP.subexponentialRate m`): for every `m`, one machine computes `lexLeast m`
within `C_k · 2 ^ (L / k)` steps on inputs of length `L`, for every `k ≥ 1`. It is stated here
with proof `sorry` on purpose. `Solution.lean` states the same declarations with the same names
and types and proves the theorem.
-/
namespace ECDLP
open Turing Computability WeierstrassCurve.Affine

/-- Input `(p, a, b, xR, yR, prefix)`: curve `y² = x³ + a x + b` over `ZMod p`, target `R = (xR, yR)`. -/
abbrev Inst := ℕ × ℕ × ℕ × ℕ × ℕ × List Bool

/-- Each number by `encodeNat` then a `none` separator; then the prefix bits. -/
def enc : Inst → List (Option Bool)
  | (p, a, b, x, y, π) => [p, a, b, x, y].flatMap (fun n => (encodeNat n).map some ++ [none]) ++ π.map some

/-- The set of strings of generic decompositions `R = P₁ + … + P_m` on the elliptic curve (`p` prime,
discriminant `≠ 0`; empty otherwise): affine points with `x(P_i) < B`, `B` the least with `p ≤ B^m`; each
partial sum `P₁+…+P_k` (`0<k<m`) affine with x-coordinate `≠ x(P_{k+1})`; the full sum is `R ≠ 0`.  The string
of `P` is, for each `i`, the `Nat.size B` bits of `x(P_i)` (big-endian) then the bit `[(p-1)/2 < y(P_i)]`;
only strings beginning with the prefix are kept. -/
def strings (m : ℕ) : Inst → Set (List Bool)
  | (p, a, b, xR, yR, π) =>
    if hp : p.Prime then haveI := Fact.mk hp
      let W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, a, b⟩
      let B := sInf {B | p ≤ B ^ m}
      let xy : W.toAffine.Point → ZMod p × ZMod p := fun P => match P with | .zero => (0, 0) | .some x y _ => (x, y)
      let str (P : Fin m → W.toAffine.Point) : List Bool := (List.ofFn fun i =>
        (List.range (Nat.size B)).reverse.map (fun j => (xy (P i)).1.val.testBit j) ++
          [decide ((p - 1) / 2 < (xy (P i)).2.val)]).flatten
      {s | W.Δ ≠ 0 ∧ ∃ P : Fin m → W.toAffine.Point, str P = s ∧ π <+: s ∧
        (∀ i, P i ≠ 0 ∧ (xy (P i)).1.val < B) ∧
        (∀ k : Fin m, 0 < k.val → let S := ((List.ofFn P).take k).sum
          S ≠ 0 ∧ (xy S).1 ≠ (xy (P k)).1) ∧
        (List.ofFn P).sum ≠ 0 ∧ xy (List.ofFn P).sum = ((xR : ZMod p), (yR : ZMod p))}
    else ∅

open Classical in
/-- The lexicographically least string of `strings m x` (`false < true`), if there is one:
`none` if the set is empty (not prime, not elliptic, or no decomposition). -/
noncomputable def lexLeast (m : ℕ) (x : Inst) : Option (List Bool) :=
  if h : ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t then some h.choose else none

/-- Sanity: whenever a decomposition exists, a least string exists (all strings have equal length),
so `lexLeast` is `some` exactly on nonempty `strings`. -/
theorem lexLeast_isSome (m : ℕ) (x : Inst) (h : (strings m x).Nonempty) : (lexLeast m x).isSome := by
  classical
  have hfin : (strings m x).Finite := by
    obtain ⟨p, a, b, xR, yR, π⟩ := x
    refine (List.finite_length_eq Bool (m * (Nat.size (sInf {B | p ≤ B ^ m}) + 1))).subset ?_
    intro s hs
    simp only [strings] at hs
    split_ifs at hs with hp
    · obtain ⟨_, P, hP, -⟩ := hs
      subst hP
      simp [List.length_flatten, List.sum_ofFn]
    · exact absurd hs (by simp)
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image _ id hfin h
  have : ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t := ⟨s, hs, hmin⟩
  simp [lexLeast, this]

/-- Output: `[false]` for `none`, `true :: s` for `some s`. -/
def encOut : Option (List Bool) → List Bool
  | none => [false]
  | some s => true :: s

/-- **Claim.** For every fixed `m`, one machine with finite alphabets outputs `lexLeast m` within
`C_k · 2^{L/k}` steps (`L` = input length) for every `k ≥ 1`, i.e. time `p ^ o(1)`. -/
theorem subexponentialRate (m : ℕ) :
    ∃ M : TM2ComputableInTime enc encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  sorry
end ECDLP
#print axioms ECDLP.lexLeast_isSome
