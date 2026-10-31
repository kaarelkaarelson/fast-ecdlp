import ECDLP.L92_Merge
import ECDLP.L92_LookOk

/-!
# L102 / Arith: pure arithmetic for the m = 1 oracle
-/
namespace ECDLP.L102
open Factoring.Aux Finset

theorem numCells_snoc (f : ℕ → ℕ) (o n : ℕ) :
    numCells f o (n + 1) = numCells f o n + (if f (o + n) = 0 then 0 else 1) * 2 ^ n := by
  unfold numCells; rw [Finset.sum_range_succ]

theorem numCells_lt (f : ℕ → ℕ) (o : ℕ) : ∀ n, numCells f o n < 2 ^ n
  | 0 => by simp [numCells]
  | n + 1 => by
      rw [numCells_snoc, pow_succ]
      have := numCells_lt f o n
      split_ifs <;> omega

theorem numCells_mono (f : ℕ → ℕ) (o n : ℕ) : ∀ d, numCells f o n ≤ numCells f o (n + d)
  | 0 => le_rfl
  | d + 1 => by
      rw [← Nat.add_assoc, numCells_snoc]
      have := numCells_mono f o n d
      omega

theorem size_snoc (M j : ℕ) (hM : M < 2 ^ j) (b : ℕ) (hb : b = 0 ∨ b = 1) :
    Nat.size (M + b * 2 ^ j) = if b = 0 then Nat.size M else j + 1 := by
  rcases hb with rfl | rfl
  · simp
  · simp only [one_mul, one_ne_zero, ite_false]
    apply le_antisymm
    · rw [Nat.size_le, pow_succ]; omega
    · have : j < Nat.size (M + 2 ^ j) := Nat.lt_size.mpr (by omega)
      omega

theorem size_numCells_succ (f : ℕ → ℕ) (o j : ℕ) :
    Nat.size (numCells f o (j + 1)) = if f (o + j) = 0 then Nat.size (numCells f o j) else j + 1 := by
  rw [numCells_snoc]
  have h := size_snoc (numCells f o j) j (numCells_lt f o j) (if f (o + j) = 0 then 0 else 1)
    (by split_ifs <;> simp)
  rw [h]
  by_cases h0 : f (o + j) = 0 <;> simp [h0]

theorem size_numCells_le (f : ℕ → ℕ) (o n : ℕ) : Nat.size (numCells f o n) ≤ n := by
  rw [Nat.size_le]; exact numCells_lt f o n

/-- bits of `numCells` above `size ℓ` vanish when the value is `≤ ℓ` -/
theorem numCells_trunc (f : ℕ → ℕ) (o ℓ : ℕ) (h : numCells f o ℓ ≤ ℓ) :
    numCells f o (Nat.size ℓ) = numCells f o ℓ := by
  have hJ : Nat.size ℓ ≤ ℓ := by rw [Nat.size_le]; exact Nat.lt_two_pow_self
  have key : ∀ d, Nat.size ℓ + d ≤ ℓ → numCells f o (Nat.size ℓ + d) = numCells f o (Nat.size ℓ) := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc, numCells_snoc, ih (by omega)]
      by_cases h0 : f (o + (Nat.size ℓ + d)) = 0
      · simp [h0]
      · exfalso
        have hm := numCells_mono f o (Nat.size ℓ + d + 1) (ℓ - (Nat.size ℓ + d + 1))
        rw [show Nat.size ℓ + d + 1 + (ℓ - (Nat.size ℓ + d + 1)) = ℓ by omega, numCells_snoc] at hm
        have h2 : 2 ^ Nat.size ℓ ≤ 2 ^ (Nat.size ℓ + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 := @Nat.lt_two_pow_self ℓ
        have h4 : ℓ < 2 ^ Nat.size ℓ := Nat.lt_size_self ℓ
        simp [h0] at hm
        omega
  have := key (ℓ - Nat.size ℓ) (by omega)
  rw [show Nat.size ℓ + (ℓ - Nat.size ℓ) = ℓ by omega] at this
  exact this.symm

theorem numCells_trunc1 (f : ℕ → ℕ) (o ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : numCells f o ℓ < 2 ^ (ℓ - 1)) :
    numCells f o (ℓ - 1) = numCells f o ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [numCells_snoc] at h ⊢
  by_cases h0 : f (o + k) = 0
  · simp [h0]
  · simp [h0] at h <;> omega

/-- `Σ_{i<j} [i ≠ 0 ∧ g i ≠ 0] 2^i` : the cells `1..j-1` of `g`, shifted up by one -/
def Bs (g : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, (if i = 0 ∨ g i = 0 then 0 else 1) * 2 ^ i

theorem Bs_succ (g : ℕ → ℕ) (j : ℕ) : Bs g (j + 1) = Bs g j + (if j = 0 ∨ g j = 0 then 0 else 1) * 2 ^ j := by
  unfold Bs; rw [Finset.sum_range_succ]

theorem Bs_lt (g : ℕ → ℕ) : ∀ j, Bs g j < 2 ^ j
  | 0 => by simp [Bs]
  | j + 1 => by
      rw [Bs_succ, pow_succ]
      have := Bs_lt g j
      split_ifs <;> omega

theorem Bs_eq (g : ℕ → ℕ) : ∀ k, Bs g (k + 1) = 2 * numCells g 1 k
  | 0 => by simp [Bs, numCells]
  | k + 1 => by
      rw [Bs_succ, Bs_eq g k, numCells_snoc, pow_succ]
      have e : (1 + k) = k + 1 := by omega
      rw [e]
      simp only [Nat.succ_ne_zero, false_or]
      split_ifs <;> ring

/-- one step of the low-to-high comparison -/
def cmpStep (res : ℕ) (a b : ℕ) : ℕ := if a < b then 1 else if b < a then 0 else res

theorem cmp_step (A B j res : ℕ) (hA : A < 2 ^ j) (hB : B < 2 ^ j) (a b : ℕ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hr : res = if A ≤ B then 1 else 0) :
    cmpStep res a b = if A + a * 2 ^ j ≤ B + b * 2 ^ j then 1 else 0 := by
  unfold cmpStep
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> split_ifs at hr ⊢ <;> omega

theorem p_le_iff (p y : ℕ) (hp : 2 ≤ p) : ((p - 1) / 2 < y) ↔ p ≤ 2 * y := by omega

end ECDLP.L102
