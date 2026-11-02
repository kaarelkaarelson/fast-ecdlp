import Mathlib.Computability.TuringMachine.Computable
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Set.Finite.List

/-! Audit statement (L109): deterministic COUNTING of generic point decompositions in `p ^ o(1)`
(the paper's Theorem 2(i)).  Same input code, same set of strings as `L35_Challenge.lean`; the output is the
cardinality of the set, in binary (`encodeNat`, Mathlib's big-endian binary code of a natural number). -/
namespace ECDLP109
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
only strings beginning with the prefix are kept.  (Verbatim `ECDLP.strings` of `L35_Challenge.lean`.) -/
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

/-- **The count**: the number of strings of `strings m x` (they all have the same length, so the set is
finite; `count_eq_zero_iff` below).  It is the number of ordered generic decompositions whose
`(x, sign)`-string begins with the prefix of `x`; `0` for invalid inputs (not prime, not elliptic, ...). -/
noncomputable def count (m : ℕ) (x : Inst) : ℕ := (strings m x).ncard

/-- Output code: the binary code `encodeNat` of Mathlib. -/
def encCount (n : ℕ) : List Bool := encodeNat n

/-- Sanity: `strings m x` is finite (all its strings have length `m * (size B + 1)`), so `count` is the true
cardinality, and `count m x = 0` exactly when there is no decomposition. -/
theorem strings_finite (m : ℕ) (x : Inst) : (strings m x).Finite := by
  classical
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  refine (List.finite_length_eq Bool (m * (Nat.size (sInf {B | p ≤ B ^ m}) + 1))).subset ?_
  intro s hs
  simp only [strings] at hs
  split_ifs at hs with hp
  · obtain ⟨_, P, hP, -⟩ := hs
    subst hP
    simp [List.length_flatten, List.sum_ofFn]
  · exact absurd hs (by simp)

theorem count_eq_zero_iff (m : ℕ) (x : Inst) : count m x = 0 ↔ strings m x = ∅ := by
  unfold count
  rw [Set.ncard_eq_zero (strings_finite m x)]

/-- **Claim (Theorem 2(i)).**  For every fixed `m`, one machine with finite alphabets outputs `count m` (in
binary) within `C_k · 2^{L/k}` steps (`L` = input length) for every `k ≥ 1`, i.e. time `p ^ o(1)`. -/
theorem countingRate (m : ℕ) :
    ∃ M : TM2ComputableInTime enc encCount (count m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  sorry
end ECDLP109
#print axioms ECDLP109.count_eq_zero_iff
