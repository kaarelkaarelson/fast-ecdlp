import ECDLP.L61_Challenge
import FactoringAux.Time
import FactoringAux.Copied.PlibLogic

/-!
# L61 / Parse: the source-level loop that reads the prefix block of the input

Adapted from the style of `FactoringAux/UniDrv.lean` (Rudich); the input is `startingMemory xs`
(array 0: cell 0 the length, cell `1 + i` the bit `i`), `xs = block π ++ r`.

`parseBody` (one turn `j`, loop counter in scalar 1, read pointer `2 j` in scalar 7, stop flag in scalar 8):
while not stopped, read the pair at `2j`: first bit `1` -> append the second bit to array 1, `len` (scalar 2)
increases; first bit `0` -> stop.
-/
namespace ECDLP.L61
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- A bit as a number. -/
def bitN (b : Bool) : ℕ := if b then 1 else 0

def parseBody : Cmd :=
  .seq (.ifZero 8
      (.seq (.rd 6 0 7 1) (.ifZero 6 (.setK 8 1) (.seq (.rd 6 0 7 2) (.seq (.wr 1 2 0 6) (.incr 2)))))
      .skip)
    (.seq (.incr 7) (.incr 7))

theorem block_cons' (b : Bool) (l : List Bool) : block (b :: l) = true :: b :: block l := by
  simp [block]

theorem block_getD_even (r : List Bool) : ∀ (π : List Bool) (j : ℕ), j < π.length →
    (block π ++ r).getD (2 * j) false = true
  | [], j, h => by simp at h
  | b :: π, 0, _ => by simp [block_cons']
  | b :: π, j + 1, h => by
      have := block_getD_even r π j (by simpa using h)
      rw [block_cons', show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simpa using this

theorem block_getD_odd (r : List Bool) : ∀ (π : List Bool) (j : ℕ), j < π.length →
    (block π ++ r).getD (2 * j + 1) false = π.getD j false
  | [], j, h => by simp at h
  | b :: π, 0, _ => by simp [block_cons']
  | b :: π, j + 1, h => by
      have := block_getD_odd r π j (by simpa using h)
      rw [block_cons', show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring]
      simpa using this

theorem block_getD_end (r : List Bool) : ∀ (π : List Bool), (block π ++ r).getD (2 * π.length) false = false
  | [] => by simp [block]
  | b :: π => by
      have := block_getD_end r π
      rw [block_cons', List.length_cons, show 2 * (π.length + 1) = 2 * π.length + 1 + 1 by ring]
      simpa using this

theorem block_length (π : List Bool) : (block π).length = 2 * π.length + 1 := by
  induction π with
  | nil => simp [block]
  | cons b π ih => rw [block_cons']; simp [ih]; ring


theorem startingMemory_succ (xs : List Bool) (q : ℕ) : startingMemory xs (q + 1) = bitN (xs.getD q false) := by
  simp [startingMemory, bitN]

def ParseInv (π : List Bool) (st : St) (j : ℕ) (s : St) : Prop :=
  s.sc 0 = st.sc 0 ∧ s.ar 0 = st.ar 0 ∧ s.sc 7 = 2 * j ∧
  (j ≤ π.length → s.sc 8 = 0 ∧ s.sc 2 = j) ∧
  (π.length < j → s.sc 8 = 1 ∧ s.sc 2 = π.length) ∧
  (∀ i, i < π.length → i < j → s.ar 1 i = bitN (π.getD i false)) ∧
  (∀ y, y ≠ 1 → y ≠ 2 → y ≠ 6 → y ≠ 7 → y ≠ 8 → s.sc y = st.sc y) ∧
  (∀ a, a ≠ 1 → s.ar a = st.ar a)

theorem parse_step (π r : List Bool) (st : St) (hA : st.ar 0 = startingMemory (block π ++ r))
    (j : ℕ) (s : St) (hs : ParseInv π st j s) :
    ParseInv π st (j + 1) (Cmd.run parseBody (s.setSc 1 j)).1 ∧ (Cmd.run parseBody (s.setSc 1 j)).2 ≤ 20 := by
  obtain ⟨h0, hA0, h7, hrun, hstop, hbits, hsc, har⟩ := hs
  have hA0' : s.ar 0 = startingMemory (block π ++ r) := by rw [hA0, hA]
  rcases lt_trichotomy j π.length with hj | hj | hj
  · obtain ⟨h8, h2⟩ := hrun hj.le
    have e1 : startingMemory (block π ++ r) (2 * j + 1) = 1 := by
      rw [startingMemory_succ, block_getD_even r π j hj]; rfl
    have e2 : startingMemory (block π ++ r) (2 * j + 1 + 1) = bitN (π.getD j false) := by
      rw [startingMemory_succ, block_getD_odd r π j hj]
    simp [parseBody, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_wr, Cmd.run_incr, Cmd.run_setK,
      Cmd.run_skip, Function.update_apply, hA0', h7, h8, h2, e1, e2, ParseInv]
    refine ⟨h0, hA0'.symm.trans hA0, by omega, hj, ?_, ?_, ?_⟩
    · intro i hi hij
      by_cases hij' : i = j
      · subst hij'; simp
      · rw [if_neg hij']
        have := hbits i hi (by omega)
        simpa [List.getD_eq_getElem?_getD] using this
    · intro y h1 h2' h6 h7' h8'
      simp only [if_neg h7', if_neg h2', if_neg h6, if_neg h1]
      exact hsc y h1 h2' h6 h7' h8'
    · intro a ha
      rw [if_neg ha]; exact har a ha
  · obtain ⟨h8, h2⟩ := hrun hj.le
    have e1 : startingMemory (block π ++ r) (2 * j + 1) = 0 := by
      rw [startingMemory_succ, hj, block_getD_end r π]; rfl
    simp [parseBody, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_wr, Cmd.run_incr, Cmd.run_setK,
      Cmd.run_skip, Function.update_apply, hA0', h7, h8, h2, e1, ParseInv]
    refine ⟨h0, hA0'.symm.trans hA0, by omega, hj.ge, fun _ => hj, ?_, ?_, ?_⟩
    · intro i hi hij
      have := hbits i hi (by omega)
      simpa [List.getD_eq_getElem?_getD] using this
    · intro y h1 h2' h6 h7' h8'
      simp only [if_neg h7', if_neg h8', if_neg h6, if_neg h1]
      exact hsc y h1 h2' h6 h7' h8'
    · intro a ha
      exact har a ha
  · obtain ⟨h8, h2⟩ := hstop hj
    simp [parseBody, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_wr, Cmd.run_incr, Cmd.run_setK,
      Cmd.run_skip, Function.update_apply, hA0', h7, h8, h2, ParseInv]
    refine ⟨h0, hA0'.symm.trans hA0, by omega, hj.le, ?_, ?_, ?_⟩
    · intro i hi hij
      exact (by simpa [List.getD_eq_getElem?_getD] using hbits i hi (by omega))
    · intro y h1 h2' h6 h7' h8'
      simp only [if_neg h7', if_neg h1]
      exact hsc y h1 h2' h6 h7' h8'
    · intro a ha
      exact har a ha

theorem parse_run (π r : List Bool) (st : St) (hA : st.ar 0 = startingMemory (block π ++ r))
    (hL : st.sc 0 = (block π ++ r).length) (h2 : st.sc 2 = 0) (h7 : st.sc 7 = 0) (h8 : st.sc 8 = 0) :
    (Cmd.run (.loop 0 1 parseBody) st).1.sc 2 = π.length ∧
    (∀ i, i < π.length → (Cmd.run (.loop 0 1 parseBody) st).1.ar 1 i = bitN (π.getD i false)) ∧
    (Cmd.run (.loop 0 1 parseBody) st).1.sc 0 = st.sc 0 ∧
    (Cmd.run (.loop 0 1 parseBody) st).1.ar 0 = st.ar 0 ∧
    (∀ y, y ≠ 1 → y ≠ 2 → y ≠ 6 → y ≠ 7 → y ≠ 8 → (Cmd.run (.loop 0 1 parseBody) st).1.sc y = st.sc y) ∧
    (∀ a, a ≠ 1 → (Cmd.run (.loop 0 1 parseBody) st).1.ar a = st.ar a) ∧
    (Cmd.run (.loop 0 1 parseBody) st).2 ≤ 21 * st.sc 0 + 1 := by
  have h0 : ParseInv π st 0 st := by
    refine ⟨rfl, rfl, by simp [h7], fun _ => ⟨h8, by simp [h2]⟩, fun h => absurd h (Nat.not_lt_zero _),
      fun i _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hstep : ∀ j s, j < st.sc 0 → ParseInv π st j s →
      ParseInv π st (j + 1) (Cmd.run parseBody (s.setSc 1 j)).1 := fun j s _ hs => (parse_step π r st hA j s hs).1
  have hI := Cmd.loop_inv (ParseInv π st) h0 hstep
  have hC := Cmd.loop_cost_le (ParseInv π st) 20 h0 hstep
    (fun j s _ hs => (parse_step π r st hA j s hs).2)
  have hlen : π.length + 1 ≤ st.sc 0 := by
    rw [hL]; have := block_length π; simp only [List.length_append]; omega
  obtain ⟨i0, iA, i7, ir, is, ib, isc, iar⟩ := hI
  have hlt : π.length < st.sc 0 := by omega
  obtain ⟨_, i2⟩ := is hlt
  refine ⟨i2, fun i hi => ib i hi (by omega), i0, iA, ?_, iar, by omega⟩
  intro y h1 h2' h6 h7' h8'
  exact isc y h1 h2' h6 h7' h8'

end ECDLP.L61
