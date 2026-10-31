import Mathlib
import ECDLP.L49_Cover
import ECDLP.L49_Transport

/-!
# L49 capstone: the coverage theorem for a fixed curve, over random dilations

Hypotheses (and only these, besides `ringChar K ≠ 2`, `Δ ≠ 0`, `12 n ≤ X`):
`DilationNondeg A B (n+1) T D'` and `FactorBaseVar A B T c`.
-/
namespace ECDLP.L49

open Finset ECDLP.L40 ECDLP.L43 ECDLP.L46

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

open Classical in
/-- **coverage, fixed curve**.**  Let `E : y² = x³ + A x + B` be a nonsingular curve over a
finite field `K` of odd characteristic, `T ⊆ K` with `|T| = X ≥ 12 n`.  Assume `DilationNondeg` and
`FactorBaseVar`.  Then there is `Bad ⊆ Kˣ` with `|Bad| ≤ |Kˣ|(1/Kc + 4c/X)` such that for every
`u ∉ Bad`, writing `f_u = |{P ∈ E_u : P ≠ O, x(P) ∈ T}|`: `f_u > X/2`, and the number of
`R ∈ E` having an ordered generic decomposition into `n+1` points of `E` with `u²x(P_i) ∈ T`
is at least `(f_u^{n+1}/2)² / (Kc · M)`, `M = Mdil`.  Moreover (L30 link) the number of affine
`R' ∈ E_u` with nonempty `GenSet` is, plus one, at least this number. -/
theorem corollary4_coverage (hK : ringChar K ≠ 2) (A B : K) (hd : disc A B ≠ 0) (T : Finset K)
    (hX : 0 < T.card) (n D' : ℕ) (hXn : 12 * n ≤ T.card) (Kc c : ℝ) (hKc : 0 < Kc)
    (hN : DilationNondeg A B (n + 1) T D') (hF : FactorBaseVar A B T c) :
    ∃ Bad : Finset Kˣ,
      (Bad.card : ℝ) ≤ (Fintype.card Kˣ : ℝ) * (1 / Kc + 4 * c / T.card) ∧
      ∀ u : Kˣ, u ∉ Bad →
        (T.card : ℝ) < 2 * (fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card ∧
        (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) ^ (n + 1) / 2) ^ 2
            / (Kc * Mdil K n T D') ≤
          (univ.filter (fun R : (shortW A B).Point =>
            (Dec (shortW A B) (fun x => (u : K) ^ 2 * x ∈ T) n R).Nonempty)).card ∧
        (univ.filter (fun R : (shortW A B).Point =>
            (Dec (shortW A B) (fun x => (u : K) ^ 2 * x ∈ T) n R).Nonempty)).card ≤
          (univ.filter (fun R : (shortW ((u : K) ^ 4 * A) ((u : K) ^ 6 * B)).Point => R ≠ 0 ∧
            (ECDLP.L30.GenSet (shortW ((u : K) ^ 4 * A) ((u : K) ^ 6 * B)) (fun x => x ∈ T)
              (ECDLP.L30.coord _ R) n).Nonempty)).card + 1 := by
  obtain ⟨Bad, hB, hBad⟩ := coverage_dilation hK A B hd T hX n D' hXn Kc c hKc hN hF
  refine ⟨Bad, hB, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hBad u hu
  rw [Gen_eq_E] at h2 h3
  exact ⟨h1, h2, h3⟩

end ECDLP.L49
