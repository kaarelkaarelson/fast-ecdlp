import Mathlib
import ECDLP.L46_Oracle
import ECDLP.L46_Cover

/-!
# L46 capstone: the average-over-curves coverage theorem over `ZMod p`, stated for the oracle's set

Single mathematical hypothesis: `SemaevNondeg (n+1) T D` (L46_Rel).  Everything else is Mathlib
(group law of `WeierstrassCurve.Affine.Point`) plus the Lean-proved chain L40 → L43 → L46.
-/
namespace ECDLP.L46

open Finset ECDLP.L40 ECDLP.L43

variable {p : ℕ} [Fact p.Prime]

theorem strings_nonempty_iff' (hp2 : p ≠ 2) (n : ℕ) (A B xR yR : ZMod p) :
    (ECDLP.strings (n + 1) (p, A.val, B.val, xR.val, yR.val, [])).Nonempty ↔
      disc A B ≠ 0 ∧ ∃ R : (shortW A B).Point, R ≠ 0 ∧ ECDLP.L30.coord _ R = (xR, yR) ∧
        (Dec (shortW A B) (fun x => x.val < sInf {B | p ≤ B ^ (n + 1)}) n R).Nonempty := by
  have h := strings_nonempty_iff (p := p) n A.val B.val xR.val yR.val
  have eA : ((A.val : ℕ) : ZMod p) = A := ZMod.natCast_zmod_val A
  have eB : ((B.val : ℕ) : ZMod p) = B := ZMod.natCast_zmod_val B
  generalize hA : ((A.val : ℕ) : ZMod p) = A' at h
  generalize hB : ((B.val : ℕ) : ZMod p) = B' at h
  rw [hA] at eA; rw [hB] at eB
  have eA' := eA.symm
  have eB' := eB.symm
  subst eA' eB'
  simp only [ZMod.natCast_zmod_val] at h
  have hK : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h16 : (-16 : ZMod p) ≠ 0 := by
    have : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hK
    have h' : (-16 : ZMod p) = -(2 ^ 4) := by norm_num
    rw [h']; exact neg_ne_zero.2 (pow_ne_zero _ this)
  have hΔ : ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) ↔ disc A B ≠ 0 := by
    have := shortW_Δ A B
    change (⟨0, 0, 0, A, B⟩ : WeierstrassCurve (ZMod p)).Δ = -16 * disc A B at this
    rw [this]
    constructor
    · intro h0 h1; exact h0 (by rw [h1, mul_zero])
    · intro h0 h1; rcases mul_eq_zero.1 h1 with h | h
      · exact h16 h
      · exact h0 h
  rw [hΔ] at h
  exact h

open Classical in
/-- **Capstone.**  `p` prime `≠ 2,3`; `T = {x | x.val < B}`, `B = sInf {B | p ≤ B^(n+1)}`.  Assume
`SemaevNondeg (n+1) T D` and `12 n ≤ |T|`.  Then outside a set `Bad ⊆ (ZMod p)²` of size
`≤ p²(1/Kc + 4/|T|) + p`, for `(A,B)`: the curve is nonsingular, `|F| > |T|/2`, and the number of
affine `R` for which L35's oracle set `strings (n+1) (p, A.val, B.val, x(R), y(R), [])` is nonempty
(i.e. `lexLeast` returns a decomposition) is, plus one, at least `(|F|^{n+1}/2)² / (Kc · M)`. -/
theorem coverage_oracle (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n D : ℕ) (T : Finset (ZMod p))
    (hT : T = univ.filter (fun x : ZMod p => x.val < sInf {B | p ≤ B ^ (n + 1)}))
    (hX : 0 < T.card) (hXn : 12 * n ≤ T.card) (Kc : ℝ) (hKc : 0 < Kc)
    (hS : SemaevNondeg (n + 1) T D) :
    ∃ Bad : Finset (ZMod p × ZMod p),
      (Bad.card : ℝ) ≤ (p : ℝ) ^ 2 * (1 / Kc + 4 / T.card) + p ∧
      ∀ q : ZMod p × ZMod p, q ∉ Bad →
        disc q.1 q.2 ≠ 0 ∧ (T.card : ℝ) < 2 * (fb q.1 q.2 T).card ∧
        (((fb q.1 q.2 T).card : ℝ) ^ (n + 1) / 2) ^ 2 / (Kc * Mconst (ZMod p) n T D) ≤
          ((univ.filter (fun R : (shortW q.1 q.2).Point => R ≠ 0 ∧
            (ECDLP.strings (n + 1) (p, q.1.val, q.2.val, (ECDLP.L30.coord _ R).1.val,
              (ECDLP.L30.coord _ R).2.val, [])).Nonempty)).card + 1 : ℕ) := by
  have hK : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 this)
  obtain ⟨Bad, hB, hBad⟩ := coverage_semaev hK h3 T hX n D hXn Kc hKc hS
  simp only [ZMod.card] at hB
  refine ⟨Bad, hB, fun q hq => ?_⟩
  obtain ⟨hd, hF, hcov⟩ := hBad q hq
  refine ⟨hd, hF, hcov.trans ?_⟩
  have : (univ.filter (fun R : (shortW q.1 q.2).Point => R ≠ 0 ∧
      (ECDLP.L30.GenSet (shortW q.1 q.2) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).Nonempty)) =
    (univ.filter (fun R : (shortW q.1 q.2).Point => R ≠ 0 ∧
      (ECDLP.strings (n + 1) (p, q.1.val, q.2.val, (ECDLP.L30.coord _ R).1.val,
        (ECDLP.L30.coord _ R).2.val, [])).Nonempty)) := by
    ext R
    simp only [mem_filter, mem_univ, true_and]
    refine and_congr_right (fun hR0 => ?_)
    rw [strings_nonempty_iff' hp2 n]
    have hmem : ∀ x : ZMod p, x ∈ T ↔ x.val < sInf {B | p ≤ B ^ (n + 1)} := by
      intro x; rw [hT]; simp
    have hDec : (Dec (shortW q.1 q.2) (fun x => x ∈ T) n R).card =
        (ECDLP.L30.GenSet (shortW q.1 q.2) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).card :=
      card_dec_eq_card_genSet _ n hR0
    have hDec' : Dec (shortW q.1 q.2) (fun x => x.val < sInf {B | p ≤ B ^ (n + 1)}) n R =
        Dec (shortW q.1 q.2) (fun x => x ∈ T) n R := by
      unfold Dec fbase; simp only [hmem]
    have hiff : (ECDLP.L30.GenSet (shortW q.1 q.2) (fun x => x ∈ T) (ECDLP.L30.coord _ R) n).Nonempty
        ↔ (Dec (shortW q.1 q.2) (fun x => x ∈ T) n R).Nonempty := by
      rw [← card_pos, ← card_pos, hDec]
    rw [hiff, ← hDec']
    constructor
    · intro hne
      exact ⟨hd, R, hR0, rfl, hne⟩
    · rintro ⟨-, R', hR0', hc, hne⟩
      have : R' = R := coord_inj hR0' hR0 hc
      subst this
      exact hne
  rw [this]

end ECDLP.L46
