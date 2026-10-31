import ECDLP.L76_Env2

/-!
# L76 / Size: `Nat.size` of a bit array, a small number as bit array, and the `|τ| ≤ nlen` test (scalars `780 .. 789`)
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `z := Nat.size (V arr W)`: scan, remembering the position of the last set cell -/
def sizeBody (arr z : ℕ) : Cmd := .seq (.rd 781 arr 780 1) (.ifZero 781 .skip (.seq (.copy z 780) (.incr z)))

def sizeC (arr z : ℕ) : Cmd := .seq (.setK z 0) (.loop 710 780 (sizeBody arr z))

theorem size_step (arr z : ℕ) (hz : z ≠ 780 ∧ z ≠ 781) (s : St) (j : ℕ) :
    let r := Cmd.run (sizeBody arr z) (s.setSc 780 j)
    r.1.sc z = (if s.ar arr (j + 1) = 0 then s.sc z else j + 1) ∧ r.1.ar = s.ar ∧
    (∀ y, y ≠ 780 → y ≠ 781 → y ≠ z → r.1.sc y = s.sc y) ∧ r.2 ≤ 6 := by
  intro r
  by_cases h : s.ar arr (j + 1) = 0
  · simp [r, sizeBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Function.update_apply, h, hz.1, hz.2]
    intro y h1 h2 h3; simp [h1, h2]
  · simp [r, sizeBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_copy, Cmd.run_incr, Function.update_apply, h, hz.1, hz.2]
    all_goals first | omega | (intro y h1 h2 h3; split_ifs <;> first | rfl | (exfalso; omega))

theorem size_snoc (f : ℕ → ℕ) (j : ℕ) :
    Nat.size (V f (j + 1)) = if f (j + 1) = 0 then Nat.size (V f j) else j + 1 := by
  rw [V_snoc]
  by_cases h : f (j + 1) = 0
  · simp [bt, h]
  · have hb : bt f (j + 1) = 1 := by simp [bt, h]
    rw [hb, if_neg h, one_mul]
    apply le_antisymm
    · apply Nat.size_le.2
      have := V_lt f j
      rw [pow_succ]; omega
    · apply Nat.lt_size.2
      omega

theorem sizeC_run (arr z : ℕ) (hz : z ≠ 780 ∧ z ≠ 781) (st : St) (W : ℕ) (hW : st.sc 710 = W) (hz710 : z ≠ 710) :
    let r := Cmd.run (sizeC arr z) st
    r.1.sc z = Nat.size (V (st.ar arr) W) ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ 780 → y ≠ 781 → y ≠ z → r.1.sc y = st.sc y) ∧
    r.2 ≤ 7 * W + 4 := by
  intro r
  set st1 := st.setSc z 0 with hst1
  let P : ℕ → St → Prop := fun j t => t.sc z = Nat.size (V (st.ar arr) j) ∧ t.ar = st.ar ∧
    (∀ y, y ≠ 780 → y ≠ 781 → y ≠ z → t.sc y = st.sc y)
  have h710 : st1.sc 710 = W := by simp [hst1, St.setSc, Function.update_apply, hW, Ne.symm hz710]
  have h0 : P 0 st1 := by
    refine ⟨by simp [hst1, St.setSc, V, numCells], rfl, fun y _ _ hy => by simp [hst1, St.setSc, Function.update_apply, hy]⟩
  have hstep : ∀ j t, j < st1.sc 710 → P j t → P (j + 1) (Cmd.run (sizeBody arr z) (t.setSc 780 j)).1 := by
    intro j t _ ⟨p1, p2, p3⟩
    obtain ⟨q1, q2, q3, q4⟩ := size_step arr z hz t j
    refine ⟨?_, by rw [q2, p2], fun y h1 h2 h3 => by rw [q3 y h1 h2 h3, p3 y h1 h2 h3]⟩
    rw [q1, size_snoc, p2, p1]
  have hI := Cmd.loop_inv (b := 710) (c := 780) (body := sizeBody arr z) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 710) (c := 780) (body := sizeBody arr z) P 6 h0 hstep
    (fun j t _ ht => (size_step arr z hz t j).2.2.2)
  rw [h710] at hI hC
  have hr : r = ((Cmd.run (.loop 710 780 (sizeBody arr z)) st1).1, 1 + (Cmd.run (.loop 710 780 (sizeBody arr z)) st1).2 + 1) := by
    simp only [r, sizeC, Cmd.run_seq, Cmd.run_setK, hst1]
  rw [hr]
  obtain ⟨i1, i2, i3⟩ := hI
  refine ⟨i1, i2, ?_, by omega⟩
  intro y h1 h2 h3
  rw [i3 y h1 h2 h3]

end ECDLP.L76
