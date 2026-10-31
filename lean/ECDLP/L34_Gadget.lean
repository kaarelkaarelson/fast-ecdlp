import FactoringAux.Digits
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# L34 / Gadget: gate-level correctness of the combined Schoenhage-Strassen gadget

Generic part (any commutative ring): `ib_mid_fa_gen`, the three gate layers FA -> MID -> IB of
Rudich's `Transform.lean`, with the MID gate combining a whole quadratic form
`sum_t eps_t * X_{l t} * X_{r t}` in the transform domain, output the combined convolution coefficient.
Signed carry chain over `Z`: `chainZ_iff`.
-/
namespace ECDLP.L34

open Finset Factoring.Aux

section Generic

variable {R : Type*} [CommRing R] {ι : Type*}

/-- **Three layers on a quadratic form.** -/
theorem ib_mid_fa_gen (A : ℕ) (ω tInv : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1) (hA : A * A = 2 ^ (k + 1))
    (htInv : tInv * ((2 ^ (k + 1) : ℕ) : R) = 1) {n : ℕ} (ε : Fin n → R) (l r : Fin n → ι)
    (X : ι → ℕ → R) (hX : ∀ i m, 2 ^ k ≤ m → X i m = 0) (j₁ j₂ : ℕ) (h₁ : j₁ < A) (h₂ : j₂ < A) :
    ibOut A (ω ^ (2 ^ (k + 1) - 1)) tInv
        (fun r' => faOut A (ω ^ (2 ^ (k + 1) - 1)) r'
          (fun k₂ => ∑ t : Fin n, ε t *
            (hatOut A ω (fun s => faOut A ω s (fun i' => X (l t) (s + A * i')) r') k₂ *
             hatOut A ω (fun s => faOut A ω s (fun i' => X (r t) (s + A * i')) r') k₂)) j₁) j₂ =
      ∑ t : Fin n, ε t * cv (2 ^ (k + 1)) (X (l t)) (X (r t)) (j₁ + A * j₂) := by
  have hT := pow_T_eq_one ω k hω
  have hζ : ω ^ (A * A) = 1 := by rw [hA]; exact hT
  have hζ' : (ω ^ (2 ^ (k + 1) - 1)) ^ (A * A) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hfw : ∀ Y : ℕ → R, ∀ r' k₂,
      hatOut A ω (fun s => faOut A ω s (fun i' => Y (s + A * i')) r') k₂ = dft A ω Y (r' + A * k₂) :=
    fun Y r' k₂ => (stage A ω hζ Y r' k₂).symm
  set F : ℕ → R := fun t => ∑ u : Fin n, ε u * (dft A ω (X (l u)) t * dft A ω (X (r u)) t) with hF
  have hmid : ∀ r', faOut A (ω ^ (2 ^ (k + 1) - 1)) r'
          (fun k₂ => ∑ t : Fin n, ε t *
            (hatOut A ω (fun s => faOut A ω s (fun i' => X (l t) (s + A * i')) r') k₂ *
             hatOut A ω (fun s => faOut A ω s (fun i' => X (r t) (s + A * i')) r') k₂)) j₁ =
      faOut A (ω ^ (2 ^ (k + 1) - 1)) r' (fun k₂ => F (r' + A * k₂)) j₁ := by
    intro r'
    simp only [hfw, hF]
  unfold ibOut
  simp only [hmid]
  rw [← stage A _ hζ' F j₁ j₂]
  have hj : j₁ + A * j₂ < 2 ^ (k + 1) := by
    rw [← hA]
    calc j₁ + A * j₂ < A + A * j₂ := by omega
      _ = A * (j₂ + 1) := by ring
      _ ≤ A * A := Nat.mul_le_mul_left _ h₂
  have hu : ∀ u : Fin n, ∑ i ∈ range (2 ^ (k + 1)), ε u * (dft A ω (X (l u)) i * dft A ω (X (r u)) i) *
      (ω ^ (2 ^ (k + 1) - 1)) ^ (i * (j₁ + A * j₂)) = ε u * (((2 ^ (k + 1) : ℕ) : R) *
        cv (2 ^ (k + 1)) (X (l u)) (X (r u)) (j₁ + A * j₂)) := by
    intro u
    rw [← conv_thm ω k hω (X (l u)) (X (r u)) (hX _) (hX _) _ hj, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold dft
    rw [hA]; ring
  have key : ∑ i ∈ range (2 ^ (k + 1)), F i * (ω ^ (2 ^ (k + 1) - 1)) ^ (i * (j₁ + A * j₂)) =
      ∑ u : Fin n, ε u * (((2 ^ (k + 1) : ℕ) : R) * cv (2 ^ (k + 1)) (X (l u)) (X (r u)) (j₁ + A * j₂)) := by
    simp only [hF, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun u _ => hu u
  unfold dft
  rw [hA, key, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  calc tInv * (ε u * (((2 ^ (k + 1) : ℕ) : R) * cv (2 ^ (k + 1)) (X (l u)) (X (r u)) (j₁ + A * j₂)))
      = (tInv * ((2 ^ (k + 1) : ℕ) : R)) * (ε u * cv (2 ^ (k + 1)) (X (l u)) (X (r u)) (j₁ + A * j₂)) := by ring
    _ = _ := by rw [htInv, one_mul]

end Generic

/-! ### The signed carry chain over `Z` -/

/-- Carry chain over `Z`: from index `s`, `len` gates, incoming carry `u`: each gate needs `2^b ∣ u + c s`
and passes `(u + c s) / 2^b`; the last carry must be `0`. -/
def chainZ (b : ℕ) (c : ℕ → ℤ) : ℕ → ℕ → ℤ → Prop
  | 0, _, u => u = 0
  | len + 1, s, u => (2 ^ b : ℤ) ∣ u + c s ∧ chainZ b c len (s + 1) ((u + c s) / 2 ^ b)

theorem chainZ_iff (b : ℕ) (c : ℕ → ℤ) :
    ∀ len s (u : ℤ), chainZ b c len s u ↔ u + ∑ j ∈ range len, c (s + j) * 2 ^ (b * j) = 0
  | 0, s, u => by simp [chainZ]
  | len + 1, s, u => by
      have ih := chainZ_iff b c len (s + 1)
      have hp : (0 : ℤ) < 2 ^ b := by positivity
      simp only [chainZ, ih]
      rw [sum_range_succ']
      simp only [add_zero, mul_zero, pow_zero, mul_one]
      have hsum : ∑ k ∈ range len, c (s + (k + 1)) * 2 ^ (b * (k + 1)) =
          2 ^ b * ∑ j ∈ range len, c (s + 1 + j) * 2 ^ (b * j) := by
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
        rw [mul_add, mul_one, pow_add, show s + (j + 1) = s + 1 + j by ring]; ring
      rw [hsum]
      set S := ∑ j ∈ range len, c (s + 1 + j) * 2 ^ (b * j)
      constructor
      · rintro ⟨⟨q, hq⟩, h⟩
        rw [hq, Int.mul_ediv_cancel_left _ hp.ne'] at h
        have : q + S = 0 := h
        linear_combination hq + (2 ^ b : ℤ) * this
      · intro h
        have hq : u + c s = 2 ^ b * (-S) := by linear_combination h
        refine ⟨⟨-S, hq⟩, ?_⟩
        rw [hq, Int.mul_ediv_cancel_left _ hp.ne']; ring

end ECDLP.L34
