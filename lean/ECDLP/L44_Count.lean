import ECDLP.L44_Corr

/-!
# L44 / Count: valuations satisfying the bit checks and identities  ↔  `IntOK` solutions with sign and bit constraints

`count_corr`: the number of `V : Slot n → Fin (2^bW)` with the bit constraints `Cl` and all identities equals
the number of `IntAssign`s with `IntOK`, `SignOK` and the `x`-bit constraints `XB`.
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst ECDLP.L34 ECDLP.L38

def pinList (bW c : ℕ) : List (ℕ × Bool) := (List.range bW).map fun j => (j, c.testBit j)

theorem pin_iff {bW V c : ℕ} (hV : V < 2 ^ bW) (hc : c < 2 ^ bW) :
    (∀ jb ∈ pinList bW c, V.testBit jb.1 = jb.2) ↔ V = c := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < bW
    · exact h (j, c.testBit j) (by simp [pinList, hj])
    · have h1 : V < 2 ^ j := lt_of_lt_of_le hV (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : c < 2 ^ j := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  · rintro rfl jb hjb
    simp only [pinList, List.mem_map, List.mem_range] at hjb
    obtain ⟨j, -, rfl⟩ := hjb
    rfl

variable {n : ℕ} (I : Inst)

/-- bit constraints per slot: pinned constants, `tg_i = 0` if no sign requirement, `x`-bits -/
def Cl (bW : ℕ) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool)) : Slot n → List (ℕ × Bool)
  | .cst c => pinList bW (I.cv c).toNat
  | .tg i => match sg i with | .none => pinList bW 0 | _ => []
  | .v (.x i) => xc i
  | _ => []

/-- `x`-bit constraints on an integer assignment -/
def XB (xc : Fin (n + 1) → List (ℕ × Bool)) (t : IntAssign n) : Prop :=
  ∀ i, ∀ jb ∈ xc i, ((t.P i).1.toNat).testBit jb.1 = jb.2

theorem Cl_iff (bW : ℕ) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool))
    (V : Slot n → ℕ) (hlt : ∀ s, V s < 2 ^ bW) (hc : ∀ c, (I.cv c).toNat < 2 ^ bW) :
    (∀ s, ∀ jb ∈ Cl I bW sg xc s, (V s).testBit jb.1 = jb.2) ↔
      (∀ c, V (.cst c) = (I.cv c).toNat) ∧ (∀ i, sg i = .none → V (.tg i) = 0) ∧
        (∀ i, ∀ jb ∈ xc i, (V (.v (.x i))).testBit jb.1 = jb.2) := by
  constructor
  · intro h
    refine ⟨fun c => (pin_iff (hlt _) (hc c)).1 (h (.cst c)), fun i hi => ?_, fun i => h (.v (.x i))⟩
    have := h (.tg i)
    simp only [Cl, hi] at this
    exact (pin_iff (hlt _) (by positivity)).1 this
  · rintro ⟨h1, h2, h3⟩ s
    cases s with
    | cst c => exact (pin_iff (hlt _) (hc c)).2 (h1 c)
    | tg i =>
      cases hg : sg i
      · simp only [Cl, hg]; exact (pin_iff (hlt _) (by positivity)).2 (h2 i hg)
      · simp [Cl, hg]
      · simp [Cl, hg]
    | v a =>
      cases a with
      | x i => exact h3 i
      | _ => simp [Cl]
    | sl a => simp [Cl]
    | u i => simp [Cl]

/-! ### ranges of the canonical valuation -/

theorem iok_range (t : IntAssign n) (h : IOK I t) (a : Var n) :
    0 ≤ Var.get t a ∧ Var.get t a < I.cv (bnd a) := by
  obtain ⟨hr, hu, hc, hS, h0, hlast, hk⟩ := h
  cases a with
  | x i => exact ⟨(hr i).1, (hr i).2.1⟩
  | y i => exact ⟨(hr i).2.2.1, (hr i).2.2.2⟩
  | sx i => exact ⟨(hS i).1, (hS i).2.1⟩
  | sy i => exact ⟨(hS i).2.2.1, (hS i).2.2.2⟩
  | w j => exact (hk j).1
  | l j => exact (hk j).2.1
  | qc i => exact ⟨(hc i).1, (hc i).2.1⟩
  | q0 j => exact ⟨(hk j).2.2.1.1, (hk j).2.2.1.2.1⟩
  | q1 j => exact ⟨(hk j).2.2.2.1.1, (hk j).2.2.2.1.2.1⟩
  | q2 j => exact ⟨(hk j).2.2.2.2.1.1, (hk j).2.2.2.2.1.2.1⟩
  | q3 j => exact ⟨(hk j).2.2.2.2.2.1, (hk j).2.2.2.2.2.2.1⟩

section
variable (hcv0 : ∀ c, 0 ≤ I.cv c) (bW : ℕ) (hcvB : ∀ c, I.cv c < 2 ^ bW)
  (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
include hcv0 hcvB hXX

theorem Vt_nonneg (sg : Fin (n + 1) → Sg) (t : IntAssign n) (h : IOK I t) (hs : SignOK I sg t) (s : Slot n) :
    0 ≤ Vt I sg t s := by
  cases s with
  | v a => exact (iok_range I t h a).1
  | sl a => have := (iok_range I t h a).2; simp only [Vt]; linarith
  | u i => show 0 ≤ t.u i; rw [(h.2.1) i]; have := (h.1 i).1; positivity
  | tg i =>
    have := hs i
    cases hg : sg i <;> simp only [Vt, tgv, hg] <;> simp [hg, SgP] at this ⊢ <;> linarith
  | cst c => exact hcv0 c

theorem Vt_lt (sg : Fin (n + 1) → Sg) (t : IntAssign n) (h : IOK I t) (hs : SignOK I sg t) (s : Slot n) :
    Vt I sg t s < 2 ^ bW := by
  have hp : (I.p : ℤ) < 2 ^ bW := by simpa using hcvB .cp
  cases s with
  | v a => exact lt_trans (iok_range I t h a).2 (hcvB _)
  | sl a =>
    have := (iok_range I t h a).1
    have := hcvB (bnd a)
    simp only [Vt]; linarith
  | u i =>
    show t.u i < _
    rw [(h.2.1) i]
    have := hXX _ (h.1 i).1 (h.1 i).2.1
    linarith
  | tg i =>
    have h1 := hs i
    have h2 := (h.1 i).2.2.1
    have h3 := (h.1 i).2.2.2
    have h4 := hcvB .cc0
    have h5 := hcvB .cc1
    have h6 := hcv0 .cc0
    have h7 := hcv0 .cc1
    cases hg : sg i <;> simp only [Vt, tgv, hg] <;> simp [hg, SgP] at h1 h4 h5 h6 h7 ⊢ <;> linarith
  | cst c => exact hcvB c

end

end ECDLP.L44
end
