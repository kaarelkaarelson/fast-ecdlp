import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# L30 / Int: mod-`p` equations versus integer identities with a bounded quotient

* `mul_modEq_iff`: for `0 ≤ u, v, r < p`: `u v ≡ r (mod p)` iff `∃! q ∈ [0,p)`, `u v = q p + r`.
* `zero_iff_window`: the signed/offset form used by the network: for an integer form value `E` with
  `|E| ≤ K p` and offset `O ≥ K`, window `[0,N)` with `O + K < N`:
  `(E : ZMod p) = 0 ↔ ∃! qc ∈ [0,N), E + O p = qc p`.
* bounds for the network's five quadratic forms (inverse, slope, x-sum, y-sum, curve).
-/

namespace ECDLP.L30

theorem mul_modEq_iff {p : ℤ} (hp : 0 < p) {u v r : ℤ} (hu0 : 0 ≤ u) (hu : u < p) (hv0 : 0 ≤ v)
    (hv : v < p) (hr0 : 0 ≤ r) (hr : r < p) :
    u * v ≡ r [ZMOD p] ↔ ∃! q : ℤ, 0 ≤ q ∧ q < p ∧ u * v = q * p + r := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨q, hq⟩
    have h1 : u * v = q * p + r := by linarith
    have hq0 : 0 ≤ q := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [mul_nonneg hu0 hv0]
    have hq1 : q < p := by
      by_contra hge
      rw [not_lt] at hge
      have : p * p ≤ q * p := by nlinarith
      nlinarith [mul_lt_mul'' hu hv hu0 hv0]
    refine ⟨q, ⟨hq0, hq1, h1⟩, ?_⟩
    rintro q' ⟨-, -, h'⟩
    have : (q' - q) * p = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hp.ne'
  · rintro ⟨q, ⟨-, -, h⟩, -⟩
    exact ⟨q, by linarith⟩

theorem zero_iff_window {p : ℕ} (hp : 0 < p) (E K O N : ℤ) (hE : |E| ≤ K * p) (hKO : K ≤ O)
    (hN : O + K < N) :
    ((E : ZMod p) = 0) ↔ ∃! qc : ℤ, 0 ≤ qc ∧ qc < N ∧ E + O * p = qc * p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨q, hq⟩
    have hqK : |q| ≤ K := by
      have h : |E| = p * |q| := by rw [hq, abs_mul, abs_of_pos hp']
      have h2 : (p : ℤ) * |q| ≤ p * K := by rw [← h]; linarith
      exact le_of_mul_le_mul_left h2 hp'
    obtain ⟨hq1, hq2⟩ := abs_le.1 hqK
    refine ⟨q + O, ⟨by linarith, by linarith, by rw [hq]; ring⟩, ?_⟩
    rintro qc' ⟨-, -, h⟩
    have : (qc' - (q + O)) * p = 0 := by rw [hq] at h; linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hp'.ne'
  · rintro ⟨qc, ⟨-, -, h⟩, -⟩
    exact ⟨qc - O, by linarith⟩

/-! ### Bounds for the five forms (variables in `[0,p)`) -/

section bounds
variable {p : ℤ} (hp : 2 ≤ p)
include hp

theorem bound_inv {a b w : ℤ} (ha0 : 0 ≤ a) (ha : a < p) (hb0 : 0 ≤ b) (hb : b < p)
    (hw0 : 0 ≤ w) (hw : w < p) : |w * (b - a) - 1| ≤ p * p := by
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hw0 ha0, mul_nonneg hw0 hb0]

theorem bound_slope {a b c d l : ℤ} (ha0 : 0 ≤ a) (ha : a < p) (hb0 : 0 ≤ b) (hb : b < p)
    (hc0 : 0 ≤ c) (hc : c < p) (hd0 : 0 ≤ d) (hd : d < p) (hl0 : 0 ≤ l) (hl : l < p) :
    |l * (b - a) - (d - c)| ≤ p * p := by
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hl0 ha0, mul_nonneg hl0 hb0]

theorem bound_xsum {a b s l : ℤ} (ha0 : 0 ≤ a) (ha : a < p) (hb0 : 0 ≤ b) (hb : b < p)
    (hs0 : 0 ≤ s) (hs : s < p) (hl0 : 0 ≤ l) (hl : l < p) :
    |l * l - a - b - s| ≤ p * p := by
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hl0 hl0]

theorem bound_ysum {a c s t l : ℤ} (ha0 : 0 ≤ a) (ha : a < p) (hc0 : 0 ≤ c) (hc : c < p)
    (hs0 : 0 ≤ s) (hs : s < p) (ht0 : 0 ≤ t) (ht : t < p) (hl0 : 0 ≤ l) (hl : l < p) :
    |l * a - l * s - t - c| ≤ p * p := by
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hl0 ha0, mul_nonneg hl0 hs0]

/-- Curve equation `y² − u x − a x − b` with `u = x²`, `x² ≤ p`. -/
theorem bound_curve {x y a b : ℤ} (hx0 : 0 ≤ x) (hxx : x * x ≤ p) (hy0 : 0 ≤ y) (hy : y < p)
    (ha0 : 0 ≤ a) (ha : a < p) (hb0 : 0 ≤ b) (hb : b < p) :
    |y * y - (x * x) * x - a * x - b| ≤ 2 * p * p := by
  have hxp : x ≤ p - 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  rw [abs_le]; constructor
  · nlinarith [mul_nonneg hx0 hx0, mul_nonneg hy0 hy0, mul_nonneg ha0 hx0,
      mul_le_mul hxx hxp hx0 (by linarith : (0:ℤ) ≤ p)]
  · nlinarith [mul_nonneg hy0 hy0, mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0,
      mul_nonneg ha0 hx0]

end bounds

end ECDLP.L30
