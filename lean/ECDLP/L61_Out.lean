import ECDLP.L61_Rounds

/-!
# L61 / Out: the round count `m (L+1) + 1` and the output commands

`boundCmd m` : scalar 9 := `m * (sc 0 + 1) + 1` (scalar 6 is the loop counter).
`noneOut`, `someOut` write `encOut none = [false]`, `encOut (some τ) = true :: τ` into array 2
(cell 0 the length, cell `1 + i` bit `i`, as `outOf` reads it).
-/
namespace ECDLP.L61
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def addL : Cmd := .seq (.loop 0 6 (.incr 9)) (.incr 9)

def boundCmd : ℕ → Cmd
  | 0 => .seq (.setK 9 0) (.incr 9)
  | m + 1 => .seq (boundCmd m) addL

theorem addL_run (st : St) :
    (Cmd.run addL st).1.sc 9 = st.sc 9 + st.sc 0 + 1 ∧ (Cmd.run addL st).1.sc 0 = st.sc 0 ∧
    (∀ y, y ≠ 6 → y ≠ 9 → (Cmd.run addL st).1.sc y = st.sc y) ∧
    (∀ a, (Cmd.run addL st).1.ar a = st.ar a) ∧ (Cmd.run addL st).2 ≤ 2 * st.sc 0 + 3 := by
  let P : ℕ → St → Prop := fun j s => s.sc 9 = st.sc 9 + j ∧ s.sc 0 = st.sc 0 ∧
    (∀ y, y ≠ 6 → y ≠ 9 → s.sc y = st.sc y) ∧ (∀ a, s.ar a = st.ar a)
  have h0 : P 0 st := ⟨rfl, rfl, fun _ _ _ => rfl, fun _ => rfl⟩
  have hstep : ∀ j s, j < st.sc 0 → P j s → P (j + 1) (Cmd.run (.incr 9) (s.setSc 6 j)).1 := by
    intro j s _ ⟨a, b, c, d⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Cmd.run_incr, a] <;> ring
    · simp [Cmd.run_incr, b]
    · intro y h6 h9; simp [Cmd.run_incr, h6, h9, c y h6 h9]
    · intro a'; simp [Cmd.run_incr, d a']
  have hI := Cmd.loop_inv P h0 hstep
  have hC := Cmd.loop_cost_le P 1 h0 hstep (fun j s _ _ => by simp [Cmd.run_incr])
  obtain ⟨a, b, c, d⟩ := hI
  simp only [addL, Cmd.run_seq, Cmd.run_incr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [a] <;> ring
  · simp [b]
  · intro y h6 h9; simp [h9, c y h6 h9]
  · intro a'; simp [d a']
  · have := hC; omega

theorem boundCmd_run (m : ℕ) : ∀ st : St,
    (Cmd.run (boundCmd m) st).1.sc 9 = m * (st.sc 0 + 1) + 1 ∧ (Cmd.run (boundCmd m) st).1.sc 0 = st.sc 0 ∧
    (∀ y, y ≠ 6 → y ≠ 9 → (Cmd.run (boundCmd m) st).1.sc y = st.sc y) ∧
    (∀ a, (Cmd.run (boundCmd m) st).1.ar a = st.ar a) ∧
    (Cmd.run (boundCmd m) st).2 ≤ (m + 1) * (2 * st.sc 0 + 4) := by
  induction m with
  | zero =>
    intro st
    simp [boundCmd, Cmd.run_seq, Cmd.run_setK, Cmd.run_incr]
    intro y _ h9; simp [Function.update_apply, h9]
  | succ m ih =>
    intro st
    obtain ⟨a, b, c, d, e⟩ := ih st
    obtain ⟨a', b', c', d', e'⟩ := addL_run (Cmd.run (boundCmd m) st).1
    simp only [boundCmd, Cmd.run_seq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [a', a, b]; ring
    · rw [b', b]
    · intro y h6 h9; rw [c' y h6 h9, c y h6 h9]
    · intro a''; rw [d', d]
    · rw [b] at e'
      nlinarith

def noneOut : Cmd :=
  .seq (.setK 6 1) (.seq (.setK 7 0) (.seq (.wr 2 7 0 6) (.seq (.setK 7 1) (.seq (.setK 6 0) (.wr 2 7 0 6)))))

theorem noneOut_run (st : St) :
    outOf ((Cmd.run noneOut st).1.ar 2) = [false] ∧ (Cmd.run noneOut st).2 ≤ 20 := by
  have : (Cmd.run noneOut st).1.ar 2 = Function.update (Function.update (st.ar 2) 0 1) 1 0 := by
    simp [noneOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]
  refine ⟨?_, by simp [noneOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]⟩
  rw [this]
  simp [outOf]

def someHead : Cmd :=
  .seq (.copy 6 2) (.seq (.incr 6) (.seq (.setK 7 0) (.seq (.wr 2 7 0 6) (.seq (.setK 6 1)
    (.seq (.setK 7 1) (.wr 2 7 0 6))))))

def copyLoop : Cmd := .loop 2 1 (.seq (.rd 6 1 1 0) (.wr 2 1 2 6))

def someOut : Cmd := .seq someHead copyLoop

theorem someHead_run (st : St) :
    (Cmd.run someHead st).1.sc 2 = st.sc 2 ∧ (Cmd.run someHead st).1.ar 1 = st.ar 1 ∧
    (Cmd.run someHead st).1.ar 2 0 = st.sc 2 + 1 ∧ (Cmd.run someHead st).1.ar 2 1 = 1 ∧
    (Cmd.run someHead st).2 ≤ 20 := by
  simp [someHead, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy, Cmd.run_incr, Cmd.run_wr, Function.update_apply]

theorem copyLoop_run (st : St) :
    (Cmd.run copyLoop st).1.sc 2 = st.sc 2 ∧ (Cmd.run copyLoop st).1.ar 1 = st.ar 1 ∧
    (Cmd.run copyLoop st).1.ar 2 0 = st.ar 2 0 ∧ (Cmd.run copyLoop st).1.ar 2 1 = st.ar 2 1 ∧
    (∀ i, i < st.sc 2 → (Cmd.run copyLoop st).1.ar 2 (i + 2) = st.ar 1 i) ∧
    (Cmd.run copyLoop st).2 ≤ 4 * st.sc 2 + 1 := by
  let P : ℕ → St → Prop := fun j s => s.sc 2 = st.sc 2 ∧ s.ar 1 = st.ar 1 ∧ s.ar 2 0 = st.ar 2 0 ∧
    s.ar 2 1 = st.ar 2 1 ∧ ∀ i, i < j → s.ar 2 (i + 2) = st.ar 1 i
  have h0 : P 0 st := ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hstep : ∀ j s, j < st.sc 2 → P j s →
      P (j + 1) (Cmd.run (.seq (.rd 6 1 1 0) (.wr 2 1 2 6)) (s.setSc 1 j)).1 := by
    intro j s _ ⟨a, b, c, d, e⟩
    simp only [Cmd.run_seq, Cmd.run_rd, Cmd.run_wr, St.setSc_sc, St.setSc_ar, St.setAr_sc, St.setAr_ar]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [a]
    · simp [b]
    · simp [Function.update_apply, c]
    · simp [Function.update_apply, d]
    · intro i hi
      by_cases hij : i = j
      · subst hij; simp [b]
      · simp [Function.update_apply, show i + 2 ≠ j + 2 from by omega, e i (by omega)]
        intro h; exact absurd h hij
  have hI := Cmd.loop_inv P h0 hstep
  have hC := Cmd.loop_cost_le P 3 h0 hstep (fun j s _ _ => by simp [Cmd.run_seq, Cmd.run_rd, Cmd.run_wr])
  obtain ⟨a, b, c, d, e⟩ := hI
  exact ⟨a, b, c, d, e, by unfold copyLoop; omega⟩

theorem someOut_run (τ : List Bool) (st : St) (h2 : st.sc 2 = τ.length)
    (hc : ∀ j, j < τ.length → st.ar 1 j = bitN (τ.getD j false)) :
    outOf ((Cmd.run someOut st).1.ar 2) = true :: τ ∧ (Cmd.run someOut st).2 ≤ 4 * τ.length + 30 := by
  obtain ⟨h1, h2', h3, h4, h5⟩ := someHead_run st
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := copyLoop_run (Cmd.run someHead st).1
  simp only [someOut, Cmd.run_seq]
  refine ⟨?_, by rw [h1] at l6; omega⟩
  rw [h1] at l5 l6
  apply List.ext_getElem
  · simp [outOf, l3, h3, h2]
  · intro i hi1 hi2
    simp only [outOf, List.getElem_ofFn]
    cases i with
    | zero => simp [l4, h4]
    | succ k =>
      have hk : k < τ.length := by simp at hi2; omega
      have := l5 k (by omega)
      rw [h2'] at this
      simp [this, hc k hk, bitN, List.getD_eq_getElem?_getD, hk]

end ECDLP.L61
