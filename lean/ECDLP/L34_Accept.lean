import ECDLP.L34_Gadget

/-!
# L34 / Accept: the gadget accepts a digit assignment iff the integer identity holds

Ring `Rg = ZMod (2^M+1)`, `M = 2^k * w`, `omega = 2^w` (so `omega^(2^k) = -1`), `T = A*A = 2^(k+1)`.
Slots `i : iota` carry `2^k` digits of `b` bits each (`dg i : Fin (2^k) -> Fin (2^b)`).
A `Form` is `sum_t eps_t * X_{l t} * X_{r t}`; linear terms and constants are products with slots whose
digits are public constants (the MID gate then holds their transform as a constant).
-/
namespace ECDLP.L34

open Finset Factoring.Aux

/-- Gadget parameters. -/
structure Par where
  k : ℕ
  A : ℕ
  w : ℕ
  b : ℕ
  hA : A * A = 2 ^ (k + 1)

namespace Par
variable (P : Par)

/-- bit length of the modulus exponent: `M = 2^k * w`. -/
def M : ℕ := 2 ^ P.k * P.w
/-- the ring `Z/(2^M+1)` -/
abbrev Rg : Type := ZMod (2 ^ P.M + 1)
def ω : P.Rg := 2 ^ P.w
def ωi : P.Rg := P.ω ^ (2 ^ (P.k + 1) - 1)
def tInv : P.Rg := 2 ^ ((2 * P.M - 1) * (P.k + 1))

theorem ω_pow : P.ω ^ (2 ^ P.k) = -1 := by
  unfold ω
  rw [← pow_mul, mul_comm]
  exact two_pow_eq_neg_one P.M

theorem tInv_mul (hM : 1 ≤ P.M) : P.tInv * ((2 ^ (P.k + 1) : ℕ) : P.Rg) = 1 := by
  have h := two_pow_eq_neg_one P.M
  have h2 : (2 : P.Rg) ^ (2 * P.M) = 1 := by rw [mul_comm, pow_mul, h]; norm_num
  unfold tInv
  push_cast
  rw [← pow_add, show (2 * P.M - 1) * (P.k + 1) + (P.k + 1) = 2 * P.M * (P.k + 1) by
    have : 2 * P.M - 1 + 1 = 2 * P.M := by omega
    calc (2 * P.M - 1) * (P.k + 1) + (P.k + 1) = (2 * P.M - 1 + 1) * (P.k + 1) := by ring
      _ = _ := by rw [this], pow_mul, h2, one_pow]

end Par

/-- A quadratic form `sum_t eps t * X (l t) * X (r t)` in slots `iota`. -/
structure Form (ι : Type) where
  n : ℕ
  l : Fin n → ι
  r : Fin n → ι
  ε : Fin n → ℤ

variable {ι : Type}

namespace Par
variable (P : Par) (F : Form ι)

/-- Digit vector of a slot, padded by zeros. -/
def sq (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) : ℕ → ℕ := fun j => if h : j < 2 ^ P.k then (x ⟨j, h⟩ : ℕ) else 0

/-- The integer a digit vector stands for. -/
def val (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) : ℕ := numOf P.b (P.sq x) (2 ^ P.k)

/-- FA gate `r` (holds digits `r + A i'`), message to MID `k₁`. -/
def faMsg (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) (r k₁ : ℕ) : P.Rg :=
  faOut P.A P.ω r (fun i' => (P.sq x (r + P.A * i') : P.Rg)) k₁

/-- MID gate `k₁`, receiving `Y i s` (= FA message of slot `i`, gate `s`, to `k₁`); message to IB `j₁`. -/
def midMsg (k₁ : ℕ) (Y : ι → ℕ → P.Rg) (j₁ : ℕ) : P.Rg :=
  faOut P.A P.ωi k₁ (fun k₂ => ∑ t : Fin F.n, (F.ε t : P.Rg) *
    (hatOut P.A P.ω (Y (F.l t)) k₂ * hatOut P.A P.ω (Y (F.r t)) k₂)) j₁

/-- CARRY gate `j` receives, from IB `j % A`, the coefficient `ibOut ... (j / A)`. -/
def coef (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (j : ℕ) : P.Rg :=
  ibOut P.A P.ωi P.tInv
    (fun r' => P.midMsg F r' (fun i s => P.faMsg (dg i) s r') (j % P.A)) (j / P.A)

/-- The carry chain reads the signed representatives. -/
def accept (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) : Prop :=
  chainZ P.b (fun j => (P.coef F dg j).valMinAbs) (P.A * P.A) 0 0

/-- The integer identity. -/
def Holds (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) : Prop :=
  ∑ t : Fin F.n, F.ε t * ((P.val (dg (F.l t)) : ℤ) * (P.val (dg (F.r t)) : ℤ)) = 0

end Par

/-- Sum of the absolute values of the coefficients. -/
def Form.mass (F : Form ι) : ℕ := ∑ t : Fin F.n, (F.ε t).natAbs

theorem cv_le (b D T : ℕ) (P Q : ℕ → ℕ) (hP : ∀ i, P i < 2 ^ b) (hQ : ∀ i, Q i < 2 ^ b)
    (hPs : ∀ i, D ≤ i → P i = 0) (j : ℕ) : cv T P Q j ≤ D * (2 ^ b * 2 ^ b) := by
  have inner : ∀ i, ∑ i' ∈ range T, (if i + i' = j then P i * Q i' else 0) ≤
      if i < D then 2 ^ b * 2 ^ b else 0 := by
    intro i
    split_ifs with hi
    · calc ∑ i' ∈ range T, (if i + i' = j then P i * Q i' else 0)
          ≤ ∑ i' ∈ range T, (if i' = j - i then P i * Q i' else 0) := by
            refine sum_le_sum fun i' _ => ?_
            split_ifs with h1 h2 <;> first | exact le_rfl | omega
        _ ≤ P i * Q (j - i) := by
            rw [sum_ite_eq']; split_ifs <;> simp
        _ ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul (hP i).le (hQ _).le
    · rw [hPs i (by omega)]; simp
  unfold cv
  calc ∑ i ∈ range T, ∑ i' ∈ range T, (if i + i' = j then P i * Q i' else 0)
      ≤ ∑ i ∈ range T, (if i < D then 2 ^ b * 2 ^ b else 0) := sum_le_sum fun i _ => inner i
    _ ≤ ∑ i ∈ range (max T D), (if i < D then 2 ^ b * 2 ^ b else 0) :=
        sum_le_sum_of_subset (range_subset_range.2 (le_max_left _ _))
    _ = D * (2 ^ b * 2 ^ b) := by
        have h1 : ∑ i ∈ range (max T D), (if i < D then 2 ^ b * 2 ^ b else 0) =
            ∑ i ∈ range D, (if i < D then 2 ^ b * 2 ^ b else 0) := by
          symm; apply sum_subset (range_subset_range.2 (le_max_right _ _))
          intro i hi hi'
          simp only [mem_range] at hi hi'
          rw [if_neg (by omega)]
        rw [h1, sum_congr rfl fun x hx => if_pos (mem_range.mp hx)]; simp

end ECDLP.L34
