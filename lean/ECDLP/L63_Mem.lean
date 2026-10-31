import ECDLP.L63_Local

/-!
# L63 / Mem: the concrete input layout satisfies `Reads` (non-vacuity)
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51

/-- cells of the binary expansion of `v` starting at cell `o` -/
def bitCells (v o : ℕ) : ℕ → ℕ := fun c => if o ≤ c ∧ v.testBit (c - o) then 1 else 0

theorem numCells_bitCells : ∀ (n o v : ℕ), numCells (bitCells v o) o n = v % 2 ^ n := by
  intro n
  induction n with
  | zero => intro o v; simp [numCells, Nat.mod_one]
  | succ n ih =>
    intro o v
    rw [numCells_succ]
    have hc : numCells (bitCells v o) (o + 1) n = numCells (bitCells (v / 2) (o + 1)) (o + 1) n := by
      refine numCells_congr fun j hj _ => ?_
      simp only [bitCells]
      have : j - o = (j - (o + 1)) + 1 := by omega
      rw [this, Nat.testBit_succ]
      have : o ≤ j := by omega
      simp [this, hj]
    rw [hc, ih]
    have h0 : (if bitCells v o o = 0 then 0 else 1) = v % 2 := by
      simp only [bitCells, le_refl, Nat.sub_self, true_and, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [h0, pow_succ, mul_comm (2 ^ n) 2, Nat.mod_mul]

/-- the memory: arrays `0..5` the numbers `p,a,b,X,xR,yR`, `7` is `2p²`, `6` the prefix -/
def memIn (p a b X xR yR : ℕ) (π : List Bool) : ℕ → ℕ → ℕ
  | 0 => bitCells p 1
  | 1 => bitCells a 1
  | 2 => bitCells b 1
  | 3 => bitCells X 1
  | 4 => bitCells xR 1
  | 5 => bitCells yR 1
  | 6 => fun c => if h : 1 ≤ c ∧ c - 1 < π.length then (π[c - 1]'h.2).toNat else 0
  | 7 => bitCells (2 * p * p) 1
  | _ => fun _ => 0

/-- the scalars -/
def stIn (L ℓ bW : ℕ) (π : List Bool) : ℕ → ℕ
  | 0 => L | 1 => π.length | 2 => ℓ | 3 => bW | 4 => 2 * L + 1 | _ => 0

/-- **Non-vacuity of the input layout**: `Reads` holds for the concrete memory whenever all numbers fit in `L`
bits. -/
theorem reads_memIn (p a b X xR yR : ℕ) (π : List Bool) (L ℓ bW : ℕ) (hp : p < 2 ^ L) (ha : a < 2 ^ L)
    (hb : b < 2 ^ L) (hX : X < 2 ^ L) (hxR : xR < 2 ^ L) (hyR : yR < 2 ^ L) :
    Reads (stIn L ℓ bW π) (memIn p a b X xR yR π) p a b X xR yR π ℓ bW where
  hp := by
    show numCells (bitCells p 1) 1 L = p
    rw [numCells_bitCells, Nat.mod_eq_of_lt hp]
  ha := by
    show numCells (bitCells a 1) 1 L = a
    rw [numCells_bitCells, Nat.mod_eq_of_lt ha]
  hb := by
    show numCells (bitCells b 1) 1 L = b
    rw [numCells_bitCells, Nat.mod_eq_of_lt hb]
  hX := by
    show numCells (bitCells X 1) 1 L = X
    rw [numCells_bitCells, Nat.mod_eq_of_lt hX]
  hxR := by
    show numCells (bitCells xR 1) 1 L = xR
    rw [numCells_bitCells, Nat.mod_eq_of_lt hxR]
  hyR := by
    show numCells (bitCells yR 1) 1 L = yR
    rw [numCells_bitCells, Nat.mod_eq_of_lt hyR]
  hOp := by
    show numCells (bitCells (2 * p * p) 1) 1 (2 * L + 1) = 2 * p * p
    rw [numCells_bitCells, Nat.mod_eq_of_lt]
    calc 2 * p * p = 2 * (p * p) := by ring
      _ < 2 * 2 ^ (2 * L) := by
        have : p * p < 2 ^ (2 * L) := by rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' hp hp
        omega
      _ = 2 ^ (2 * L + 1) := by ring
  hlen := rfl
  hl := rfl
  hbW := rfl
  hpi := by
    intro q h
    show (memIn p a b X xR yR π 6 (q + 1) ≠ 0) ↔ _
    simp only [memIn]
    rw [dif_pos ⟨by omega, by simpa using h⟩]
    simp only [Nat.add_sub_cancel]
    cases π[q] <;> simp

end ECDLP.L63
end
