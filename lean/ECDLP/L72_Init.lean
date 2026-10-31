import ECDLP.L72_Core
import ECDLP.L63_Main
import ECDLP.L65_Rate

/-!
# L72 / Init: the initial state of the zero test, and its layout spec (item 5)

The engine reads `sc 0 = n` (the input length) and `sc 2 = k`, and overwrites the array `3` (its table) and the
scalars `5 .. 15`; `ShapeData` quantifies over ALL contexts with only `sc 0, 2, 10, 11` fixed.  So (NEGATIVE for
L63's layout) the instance data cannot live in scalars `1, 2, 3, 4` and the number `X` cannot live in array `3`.
New layout, everything in ARRAYS (cells `1 ..`, little endian, nonzero = 1), widths read from `sc 0 = len`:
`0..2 = p, a, b`; `3` unused (zero; the engine's table); `4, 5 = xR, yR`; `6 =` prefix; `7 = 2p^2` (width `2 len + 1`);
`8 = X = Bd p r`; `9 = |pi|`; `10 = ell`; `11 = bW` (width of a pinned constant).
`stOf r i`: scalars all `0` except `sc 0 = len i`; `Reads72`: the layout predicate; `reads72_stOf`: it holds.
-/
noncomputable section
namespace ECDLP.L72
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L63 ECDLP.L65 ECDLP.L51 ECDLP.L59 ECDLP.L60

/-- the memory (array `3` is zero) -/
def memE (p a b X xR yR : ℕ) (π : List Bool) (ℓ bW : ℕ) : ℕ → ℕ → ℕ
  | 0 => bitCells p 1
  | 1 => bitCells a 1
  | 2 => bitCells b 1
  | 4 => bitCells xR 1
  | 5 => bitCells yR 1
  | 6 => fun c => if h : 1 ≤ c ∧ c - 1 < π.length then (π[c - 1]'h.2).toNat else 0
  | 7 => bitCells (2 * p * p) 1
  | 8 => bitCells X 1
  | 9 => bitCells π.length 1
  | 10 => bitCells ℓ 1
  | 11 => bitCells bW 1
  | _ => fun _ => 0

/-- the pinned-constant width of the explicit parameters -/
def bWof (L : ℕ) : ℕ := (NParE L).b * 2 ^ (NParE L).k

def memOf (r : ℕ) (i : EdgeInp) : ℕ → ℕ → ℕ :=
  memE i.p i.a i.b (Bd i.p r) i.xR i.yR i.π (ell i.p r) (bWof (Nat.size i.p))

/-- **The initial state**: `sc 0 = len`, every other scalar `0`, memory `memOf`. -/
def stOf (r : ℕ) (i : EdgeInp) : St := ⟨fun x => if x = 0 then i.len else 0, memOf r i⟩

theorem stOf_sc0 (r : ℕ) (i : EdgeInp) : (stOf r i).sc 0 = i.len := by simp [stOf]

theorem stOf_sc2 (r : ℕ) (i : EdgeInp) : (stOf r i).sc 2 < (stOf r i).sc 0 := by
  simp [stOf, EdgeInp.len]

theorem stOf_array3 (r : ℕ) (i : EdgeInp) : (stOf r i).ar 3 = fun _ => 0 := rfl

/-- **The layout predicate** (arrays only; `σ 0` is the width). -/
structure Reads72 (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (p a b X xR yR : ℕ) (π : List Bool) (ℓ bW : ℕ) : Prop where
  hp : numCells (A 0) 1 (σ 0) = p
  ha : numCells (A 1) 1 (σ 0) = a
  hb : numCells (A 2) 1 (σ 0) = b
  hxR : numCells (A 4) 1 (σ 0) = xR
  hyR : numCells (A 5) 1 (σ 0) = yR
  hOp : numCells (A 7) 1 (2 * σ 0 + 1) = 2 * p * p
  hX : numCells (A 8) 1 (σ 0) = X
  hlen : numCells (A 9) 1 (σ 0) = π.length
  hl : numCells (A 10) 1 (σ 0) = ℓ
  hbW : numCells (A 11) 1 (σ 0) = bW
  hpi : ∀ (q : ℕ) (h : q < π.length), (A 6 (q + 1) ≠ 0 ↔ π[q] = true)
  h3 : ∀ j, A 3 j = 0

theorem reads72_memE (p a b X xR yR : ℕ) (π : List Bool) (ℓ bW n : ℕ) (hp : p < 2 ^ n) (ha : a < 2 ^ n)
    (hb : b < 2 ^ n) (hX : X < 2 ^ n) (hxR : xR < 2 ^ n) (hyR : yR < 2 ^ n) (hlen : π.length < 2 ^ n)
    (hl : ℓ < 2 ^ n) (hbW : bW < 2 ^ n) :
    Reads72 (fun x => if x = 0 then n else 0) (memE p a b X xR yR π ℓ bW) p a b X xR yR π ℓ bW where
  hp := by show numCells (bitCells p 1) 1 n = p; rw [numCells_bitCells, Nat.mod_eq_of_lt hp]
  ha := by show numCells (bitCells a 1) 1 n = a; rw [numCells_bitCells, Nat.mod_eq_of_lt ha]
  hb := by show numCells (bitCells b 1) 1 n = b; rw [numCells_bitCells, Nat.mod_eq_of_lt hb]
  hxR := by show numCells (bitCells xR 1) 1 n = xR; rw [numCells_bitCells, Nat.mod_eq_of_lt hxR]
  hyR := by show numCells (bitCells yR 1) 1 n = yR; rw [numCells_bitCells, Nat.mod_eq_of_lt hyR]
  hOp := by
    show numCells (bitCells (2 * p * p) 1) 1 (2 * n + 1) = 2 * p * p
    rw [numCells_bitCells, Nat.mod_eq_of_lt]
    calc 2 * p * p = 2 * (p * p) := by ring
      _ < 2 * 2 ^ (2 * n) := by
        have : p * p < 2 ^ (2 * n) := by rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' hp hp
        omega
      _ = 2 ^ (2 * n + 1) := by ring
  hX := by show numCells (bitCells X 1) 1 n = X; rw [numCells_bitCells, Nat.mod_eq_of_lt hX]
  hlen := by show numCells (bitCells π.length 1) 1 n = π.length; rw [numCells_bitCells, Nat.mod_eq_of_lt hlen]
  hl := by show numCells (bitCells ℓ 1) 1 n = ℓ; rw [numCells_bitCells, Nat.mod_eq_of_lt hl]
  hbW := by show numCells (bitCells bW 1) 1 n = bW; rw [numCells_bitCells, Nat.mod_eq_of_lt hbW]
  hpi := by
    intro q h
    show (memE p a b X xR yR π ℓ bW 6 (q + 1) ≠ 0) ↔ _
    simp only [memE]
    rw [dite_cond_eq_true (eq_true ⟨by omega, by simpa using h⟩)]
    simp only [Nat.add_sub_cancel]
    cases π[q] <;> simp
  h3 _ := rfl

theorem thirtysix_lt : ∀ L : ℕ, 9 ≤ L → 36 * L < 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have : 36 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL : 2 ^ 9 ≤ 2 ^ L)
    rw [pow_succ]; omega

/-- **The initial state satisfies the layout** (for `size p >= 9`, so that the pinned-constant width fits). -/
theorem reads72_stOf (r : ℕ) (i : EdgeInp) (h : i.adm r) (h9 : 9 ≤ Nat.size i.p) :
    Reads72 (stOf r i).sc (stOf r i).ar i.p i.a i.b (Bd i.p r) i.xR i.yR i.π (ell i.p r) (bWof (Nat.size i.p)) := by
  obtain ⟨hpr, ha, hb, hx, hy, -, -, -⟩ := h
  have hp0 : 0 < i.p := hpr.pos
  have hsz : Nat.size i.p ≤ i.len := by unfold EdgeInp.len; omega
  have hlt : ∀ v, v < i.p → v < 2 ^ i.len := fun v hv =>
    lt_of_lt_of_le (lt_trans hv (Nat.lt_size_self i.p)) (Nat.pow_le_pow_right (by norm_num) hsz)
  have hX : Bd i.p r ≤ i.p := Bd_le hp0 r
  have hbW : bWof (Nat.size i.p) < 2 ^ i.len := by
    have h1 := bW_le (Nat.size i.p) (by omega)
    have h2 := thirtysix_lt (Nat.size i.p) h9
    exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) (Nat.pow_le_pow_right (by norm_num) hsz)
  have hℓ : ell i.p r < 2 ^ i.len := by
    have : ell i.p r ≤ Nat.size i.p := by unfold ell; exact Nat.size_le_size hX
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (le_trans this hsz))
  have hπ : i.π.length < 2 ^ i.len :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by unfold EdgeInp.len; omega))
  have hXl : Bd i.p r < 2 ^ i.len :=
    lt_of_le_of_lt hX (lt_of_lt_of_le (Nat.lt_size_self i.p) (Nat.pow_le_pow_right (by norm_num) hsz))
  exact reads72_memE _ _ _ _ _ _ _ _ _ i.len (lt_of_lt_of_le (Nat.lt_size_self i.p)
    (Nat.pow_le_pow_right (by norm_num) hsz)) (hlt _ ha) (hlt _ hb) hXl (hlt _ hx) (hlt _ hy) hπ hℓ hbW

end ECDLP.L72
