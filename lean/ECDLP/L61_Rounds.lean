import ECDLP.L61_Parse
import ECDLP.L61_Facts

/-!
# L61 / Rounds: the oracle contract and one round of the search at the source level

`Keep c`  : the oracle command preserves scalars `< 10` other than `3` and arrays `< 3`.
`Orc c A L Z ok T` : on a state holding the input `A` (array 0, length `L` in scalar 0), the prefix `τ` in array 1
   (`bitN` cells, length in scalar 2), with `ok τ`, the command leaves `[0 < Z τ]` in scalar 3 within `T` steps.
`roundBody c` : one round of `stepF` (`L61_Facts`): scalar 5 is the done flag.
-/
namespace ECDLP.L61
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

structure Keep (c : Cmd) : Prop where
  sc : ∀ st i, i < 10 → i ≠ 3 → (Cmd.run c st).1.sc i = st.sc i
  ar : ∀ st a, a < 3 → (Cmd.run c st).1.ar a = st.ar a

structure Orc (c : Cmd) (A : ℕ → ℕ) (L : ℕ) (Z : List Bool → ℕ) (ok : List Bool → Prop) (T : ℕ) : Prop where
  val : ∀ (st : St) (τ : List Bool), st.sc 0 = L → st.ar 0 = A → st.sc 2 = τ.length →
    (∀ j, j < τ.length → st.ar 1 j = bitN (τ.getD j false)) → ok τ →
    (Cmd.run c st).1.sc 3 = (if 0 < Z τ then 1 else 0) ∧ (Cmd.run c st).2 ≤ T

/-- Append a bit: write `k` into cell `sc 2` of array 1 and increase the length. -/
def bitCmd (k : ℕ) : Cmd := .seq (.setK 4 k) (.seq (.wr 1 2 0 4) (.incr 2))

def innerBody (c : Cmd) : Cmd :=
  .seq (.decr 2) (.seq (bitCmd 1) (.seq c
    (.ifZero 3 (.seq (.decr 2) (.setK 5 1)) .skip)))

def roundBody (c : Cmd) : Cmd :=
  .ifZero 5
    (.seq (bitCmd 0) (.seq c (.ifZero 3 (innerBody c) .skip)))
    .skip

/-- The state after `bitCmd k`. -/
def addBit (s : St) (k : ℕ) : St := ((s.setSc 4 k).setAr 1 (s.sc 2) k).setSc 2 (s.sc 2 + 1)

theorem run_bitCmd (k : ℕ) (s : St) : Cmd.run (bitCmd k) s = (addBit s k, 5) := by
  simp [bitCmd, addBit, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, Cmd.run_incr]

/-- The invariant of the round loop: model state `(τ, d)`. -/
def RInv (A : ℕ → ℕ) (L R : ℕ) (τ : List Bool) (d : Bool) (s : St) : Prop :=
  s.sc 0 = L ∧ s.ar 0 = A ∧ s.sc 9 = R ∧ s.sc 2 = τ.length ∧
    (∀ j, j < τ.length → s.ar 1 j = bitN (τ.getD j false)) ∧ s.sc 5 = (if d then 1 else 0)

theorem addBit_inv {A L R τ d} {s : St} (h : RInv A L R τ d s) (b : Bool) :
    (addBit s (bitN b)).sc 0 = L ∧ (addBit s (bitN b)).ar 0 = A ∧ (addBit s (bitN b)).sc 9 = R ∧
    (addBit s (bitN b)).sc 2 = (τ ++ [b]).length ∧
    (∀ j, j < (τ ++ [b]).length → (addBit s (bitN b)).ar 1 j = bitN ((τ ++ [b]).getD j false)) ∧
    (addBit s (bitN b)).sc 5 = (if d then 1 else 0) := by
  obtain ⟨h0, hA, h9, h2, hc, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [addBit, h0]
  · simp [addBit, hA]
  · simp [addBit, h9]
  · simp [addBit, h2]
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    simp only [addBit, St.setSc_ar, St.setAr_ar, Function.update_apply, h2]
    by_cases hjt : j = τ.length
    · subst hjt; simp [List.getD_append_right]
    · have hjl : j < τ.length := by omega
      simp only [if_true, Function.update_apply, if_neg hjt]
      rw [List.getD_append _ _ _ _ hjl]
      exact hc j hjl
  · simp [addBit, h5]


theorem round_true (c : Cmd) {A L R} {τ : List Bool} {s : St} (hs : RInv A L R τ true s) :
    Cmd.run (roundBody c) s = (s, 2) := by
  have h5 : s.sc 5 ≠ 0 := by rw [hs.2.2.2.2.2]; simp
  simp [roundBody, Cmd.run_ifZero, h5, Cmd.run_skip]

/-- Second half of a round: the state after the first `0`-child failed (`sc 2 = |τ| + 1`). -/
theorem inner_spec (c : Cmd) (A : ℕ → ℕ) (L R T : ℕ) (Z : List Bool → ℕ) (ok : List Bool → Prop)
    (hk : Keep c) (ho : Orc c A L Z ok T) (τ : List Bool) (r : St)
    (h0 : r.sc 0 = L) (hA : r.ar 0 = A) (h9 : r.sc 9 = R) (h2 : r.sc 2 = τ.length + 1)
    (hc : ∀ j, j < τ.length → r.ar 1 j = bitN (τ.getD j false)) (h5 : r.sc 5 = 0)
    (hok : ok (τ ++ [true])) :
    RInv A L R (if 0 < Z (τ ++ [true]) then τ ++ [true] else τ) (!decide (0 < Z (τ ++ [true])))
        (Cmd.run (innerBody c) r).1 ∧ (Cmd.run (innerBody c) r).2 ≤ T + 20 := by
  have hr' : RInv A L R τ false (r.setSc 2 (r.sc 2 - 1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h0, hA, h9, h2, hc, h5]
    · exact fun j hj => hc j hj
  obtain ⟨i0, iA, i9, i2, ic, i5⟩ := addBit_inv hr' true
  obtain ⟨v1, c1⟩ := ho.val (addBit (r.setSc 2 (r.sc 2 - 1)) (bitN true)) (τ ++ [true]) i0 iA i2 ic hok
  have k1sc := hk.sc (addBit (r.setSc 2 (r.sc 2 - 1)) (bitN true))
  have k1ar := hk.ar (addBit (r.setSc 2 (r.sc 2 - 1)) (bitN true))
  generalize hr3 : Cmd.run c (addBit (r.setSc 2 (r.sc 2 - 1)) (bitN true)) = r3 at v1 c1 k1sc k1ar
  simp only [innerBody, Cmd.run_seq, Cmd.run_decr, show bitCmd 1 = bitCmd (bitN true) from rfl, run_bitCmd, hr3]
  by_cases hp : 0 < Z (τ ++ [true])
  · have h3 : r3.1.sc 3 ≠ 0 := by rw [v1]; simp [hp]
    simp only [Cmd.run_ifZero, h3, if_false, Cmd.run_skip, hp, if_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [k1sc 0 (by norm_num) (by norm_num), i0]
    · rw [k1ar 0 (by norm_num), iA]
    · rw [k1sc 9 (by norm_num) (by norm_num), i9]
    · rw [k1sc 2 (by norm_num) (by norm_num), i2]
    · intro j hj; rw [k1ar 1 (by norm_num)]; exact ic j hj
    · rw [k1sc 5 (by norm_num) (by norm_num), i5]; simp
  · have h3 : r3.1.sc 3 = 0 := by rw [v1]; simp [hp]
    simp only [Cmd.run_ifZero, h3, if_true, Cmd.run_seq, Cmd.run_decr, Cmd.run_setK, hp, if_false]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
    · simp [k1sc 0 (by norm_num) (by norm_num), i0]
    · simp [k1ar 0 (by norm_num), iA]
    · simp [k1sc 9 (by norm_num) (by norm_num), i9]
    · simp [k1sc 2 (by norm_num) (by norm_num), i2]
    · intro j hj
      simp only [St.setSc_ar]
      rw [k1ar 1 (by norm_num)]
      have := ic j (by simp; omega)
      rwa [List.getD_append _ _ _ _ hj] at this
    · simp

theorem round_false (c : Cmd) (A : ℕ → ℕ) (L R T : ℕ) (Z : List Bool → ℕ) (ok : List Bool → Prop)
    (hk : Keep c) (ho : Orc c A L Z ok T) (τ : List Bool) (s : St) (hs : RInv A L R τ false s)
    (hok : ok (τ ++ [false]) ∧ ok (τ ++ [true])) :
    RInv A L R (stepF Z (τ, false)).1 (stepF Z (τ, false)).2 (Cmd.run (roundBody c) s).1 ∧
      (Cmd.run (roundBody c) s).2 ≤ 2 * T + 30 := by
  have h5 : s.sc 5 = 0 := by rw [hs.2.2.2.2.2]; simp
  have hI0 := addBit_inv hs false
  obtain ⟨i0, iA, i9, i2, ic, i5⟩ := hI0
  have hbit0 : bitN false = 0 := rfl
  obtain ⟨v1, c1⟩ := ho.val (addBit s (bitN false)) (τ ++ [false]) i0 iA i2 ic hok.1
  have k1sc := hk.sc (addBit s (bitN false))
  have k1ar := hk.ar (addBit s (bitN false))
  generalize hr1 : Cmd.run c (addBit s (bitN false)) = r1 at v1 c1 k1sc k1ar
  simp only [roundBody, Cmd.run_ifZero, h5, if_true, Cmd.run_seq, show bitCmd 0 = bitCmd (bitN false) from rfl,
    run_bitCmd, hr1]
  by_cases hp0 : 0 < Z (τ ++ [false])
  · have h3 : r1.1.sc 3 ≠ 0 := by rw [v1]; simp [hp0]
    have hst : stepF Z (τ, false) = (τ ++ [false], false) := by simp [stepF, hp0]
    simp only [h3, if_false, Cmd.run_skip, hst]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [k1sc 0 (by norm_num) (by norm_num), i0]
    · rw [k1ar 0 (by norm_num), iA]
    · rw [k1sc 9 (by norm_num) (by norm_num), i9]
    · rw [k1sc 2 (by norm_num) (by norm_num), i2]
    · intro j hj; rw [k1ar 1 (by norm_num)]; exact ic j hj
    · rw [k1sc 5 (by norm_num) (by norm_num), i5]
  · have h3 : r1.1.sc 3 = 0 := by rw [v1]; simp [hp0]
    simp only [h3, if_true]
    obtain ⟨hI, hC⟩ := inner_spec c A L R T Z ok hk ho τ r1.1
      (by rw [k1sc 0 (by norm_num) (by norm_num), i0])
      (by rw [k1ar 0 (by norm_num), iA])
      (by rw [k1sc 9 (by norm_num) (by norm_num), i9])
      (by rw [k1sc 2 (by norm_num) (by norm_num), i2]; simp)
      (fun j hj => by
        rw [k1ar 1 (by norm_num)]
        have := ic j (by simp; omega)
        rwa [List.getD_append _ _ _ _ hj] at this)
      (by rw [k1sc 5 (by norm_num) (by norm_num), i5]; simp) hok.2
    have hst : stepF Z (τ, false) = (if 0 < Z (τ ++ [true]) then τ ++ [true] else τ,
        !decide (0 < Z (τ ++ [true]))) := by
      by_cases hp1 : 0 < Z (τ ++ [true]) <;> simp [stepF, hp0, hp1]
    rw [hst]
    exact ⟨hI, by omega⟩

theorem round_step (c : Cmd) (A : ℕ → ℕ) (L R T : ℕ) (Z : List Bool → ℕ) (ok : List Bool → Prop)
    (hk : Keep c) (ho : Orc c A L Z ok T) (τ : List Bool) (d : Bool) (s : St) (hs : RInv A L R τ d s)
    (hok : d = false → ok (τ ++ [false]) ∧ ok (τ ++ [true])) :
    RInv A L R (stepF Z (τ, d)).1 (stepF Z (τ, d)).2 (Cmd.run (roundBody c) s).1 ∧
      (Cmd.run (roundBody c) s).2 ≤ 2 * T + 30 := by
  cases d
  · exact round_false c A L R T Z ok hk ho τ s hs (hok rfl)
  · rw [round_true c hs]
    exact ⟨hs, by omega⟩

end ECDLP.L61
