import ECDLP.L56_EFinal

/-!
# L59 / Param: explicit edgeNet parameters as computable functions of the input bit length

Input bit length `L := Nat.size p`.  Target bit budget `B L := 2 L + 3` (every constant of the identities
is `< 2^(B L)`).  With `j = jm1 + 1`, `jm1 L = (Nat.log 2 L + 2)/4 - 1`:
`k = 2 jm1 + 1`, `A = 2^j`, `h = 2^jm1`, `D = 2^k = 2^(2j-1)`, `A*A = 2D`, `A*h = D`,
`b = B/D + 1`, ring exponent multiplier `w = (2 b + k + 4)/D + 1` (the same for every identity),
so `M = D w`.  `D^2 ≤ L ≤ 16 D^2` for `L ≥ 4` (see `D_sq_le`, `L_le_D_sq`).
-/
noncomputable section
namespace ECDLP.L59
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38 ECDLP.L51 ECDLP.L35 ECDLP.L54 ECDLP.L56

/-- bit budget for the constants -/
def Bits (L : ℕ) : ℕ := 2 * L + 3
def jm1 (L : ℕ) : ℕ := (Nat.log 2 L + 2) / 4 - 1
def kP (L : ℕ) : ℕ := 2 * jm1 L + 1
def AP (L : ℕ) : ℕ := 2 ^ (jm1 L + 1)
def hP (L : ℕ) : ℕ := 2 ^ jm1 L
def DP (L : ℕ) : ℕ := 2 ^ kP L
def bP (L : ℕ) : ℕ := Bits L / DP L + 1
def wP (L : ℕ) : ℕ := (2 * bP L + kP L + 4) / DP L + 1

theorem DP_pos (L : ℕ) : 0 < DP L := by unfold DP; positivity

def NParE (L : ℕ) : NPar where
  k := kP L
  A := AP L
  w := wP L
  b := bP L
  hA := by unfold AP kP; rw [← pow_add]; congr 1; omega
  h := hP L
  hAh := by unfold AP hP kP; rw [← pow_add]; congr 1; omega

/-- the parameters used for an instance with modulus `p` -/
def parOf (p : ℕ) : NPar × (Fin K → ℕ) := (NParE (Nat.size p), fun _ => wP (Nat.size p))

@[simp] theorem NParE_k (L : ℕ) : (NParE L).k = kP L := rfl
@[simp] theorem NParE_A (L : ℕ) : (NParE L).A = AP L := rfl
@[simp] theorem NParE_b (L : ℕ) : (NParE L).b = bP L := rfl
@[simp] theorem NParE_h (L : ℕ) : (NParE L).h = hP L := rfl

theorem bP_pos (L : ℕ) : 1 ≤ bP L := Nat.le_add_left _ _

theorem Bits_lt (L : ℕ) : Bits L < bP L * DP L := by
  unfold bP
  have := Nat.div_add_mod (Bits L) (DP L)
  have h2 := Nat.mod_lt (Bits L) (DP_pos L)
  nlinarith

theorem wP_mul (L : ℕ) : 2 * bP L + kP L + 4 < DP L * wP L := by
  unfold wP
  have := Nat.div_add_mod (2 * bP L + kP L + 4) (DP L)
  have h2 := Nat.mod_lt (2 * bP L + kP L + 4) (DP_pos L)
  nlinarith

theorem wP_pos (L : ℕ) : 1 ≤ wP L := Nat.le_add_left _ _

theorem AA_eq (L : ℕ) : AP L * AP L = 2 * DP L := by
  unfold AP DP kP; rw [← pow_add, show 2 * 2 ^ (2 * jm1 L + 1) = 2 ^ (2 * jm1 L + 1 + 1) by ring]
  congr 1; omega

/-- every constant of the instance is below `2^(Bits L)` -/
theorem cv_lt (p a b xR yR n : ℕ) (hp : 0 < p) (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (c : Cst) : (instOf p a b xR yR n).cv c < (2 : ℤ) ^ Bits (Nat.size p) := by
  have hpL : (p : ℤ) < 2 ^ Nat.size p := by exact_mod_cast Nat.lt_size_self p
  have hBd : Bd p n ≤ p := Bd_le hp n
  have hpow : (2 : ℤ) ^ Nat.size p ≤ 2 ^ Bits (Nat.size p) :=
    pow_le_pow_right₀ (by norm_num) (by unfold Bits; omega)
  have hpp : (0 : ℤ) < 2 ^ Nat.size p := by positivity
  have hsq : (2 : ℤ) * p * p < 2 ^ Bits (Nat.size p) := by
    have h1 : (p : ℤ) * p < 2 ^ Nat.size p * 2 ^ Nat.size p :=
      mul_lt_mul'' hpL hpL (by positivity) (by positivity)
    have h2 : (2 : ℤ) ^ Bits (Nat.size p) = 2 ^ 3 * (2 ^ Nat.size p * 2 ^ Nat.size p) := by
      unfold Bits; rw [pow_add, pow_mul']; ring
    rw [h2]; nlinarith
  have h4 : (4 : ℤ) * p + 1 < 2 ^ Bits (Nat.size p) := by
    have h2 : (2 : ℤ) ^ Bits (Nat.size p) = 2 ^ (Nat.size p + 3) * 2 ^ Nat.size p := by
      unfold Bits; rw [← pow_add]; congr 1; omega
    have h3 : (1 : ℤ) ≤ 2 ^ Nat.size p := one_le_pow₀ (by norm_num)
    have : (2:ℤ) ^ (Nat.size p + 3) = 8 * 2 ^ Nat.size p := by rw [pow_add]; ring
    rw [h2, this]; nlinarith
  have hpp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hc0 : (((p - 1) / 2 : ℕ) : ℤ) ≤ p := by
    have : (p - 1) / 2 ≤ p := by omega
    exact_mod_cast this
  have hX : (Bd p n : ℤ) ≤ p := by exact_mod_cast hBd
  have hpB : (p : ℤ) < 2 ^ Bits (Nat.size p) := lt_of_lt_of_le hpL hpow
  have h1B : (1 : ℤ) < 2 ^ Bits (Nat.size p) :=
    one_lt_pow₀ (show (1:ℤ) < 2 by norm_num) (show Bits (Nat.size p) ≠ 0 by unfold Bits; omega)
  have haB : (a : ℤ) < 2 ^ Bits (Nat.size p) := lt_trans (by exact_mod_cast ha) hpB
  have hbB : (b : ℤ) < 2 ^ Bits (Nat.size p) := lt_trans (by exact_mod_cast hb) hpB
  have hxB : (xR : ℤ) < 2 ^ Bits (Nat.size p) := lt_trans (by exact_mod_cast hx) hpB
  have hyB : (yR : ℤ) < 2 ^ Bits (Nat.size p) := lt_trans (by exact_mod_cast hy) hpB
  have hXB : (Bd p n : ℤ) < 2 ^ Bits (Nat.size p) := lt_of_le_of_lt hX hpB
  have hc0B : (((p - 1) / 2 : ℕ) : ℤ) < 2 ^ Bits (Nat.size p) := lt_of_le_of_lt hc0 hpB
  have hc1B : (((p - 1) / 2 : ℕ) : ℤ) + 1 < 2 ^ Bits (Nat.size p) := by
    have : (((p - 1) / 2 : ℕ) : ℤ) + 1 ≤ p := by
      have : (p - 1) / 2 + 1 ≤ p := by omega
      exact_mod_cast this
    exact lt_of_le_of_lt this hpB
  cases c <;> simp only [Inst.cv, instOf]
  · exact h1B
  · exact hpB
  · exact haB
  · exact hbB
  · linarith
  · exact hXB
  · linarith
  · exact hxB
  · exact hyB
  · exact hc0B
  · exact hc1B

end ECDLP.L59
end
