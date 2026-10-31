import ECDLP.L76_Size

/-!
# L76 / Flags: `nlen = m (ℓ+1)`, the test `|τ| ≤ nlen`, and the conjunction of the four flags (scalars `785 .. 789`)
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `acc := acc + (ℓ + 1)` where `ℓ` is in scalar `l` -/
def addL (l : ℕ) : Cmd := .seq (.loop l 786 (.incr 785)) (.incr 785)

def repAdd (l : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (repAdd l k) (addL l)

theorem addL_run (l : ℕ) (hl : l ≠ 785 ∧ l ≠ 786) (s : St) :
    let r := Cmd.run (addL l) s
    r.1.sc 785 = s.sc 785 + s.sc l + 1 ∧ r.1.ar = s.ar ∧ r.1.sc l = s.sc l ∧ (∀ y, y ≠ 785 → y ≠ 786 → r.1.sc y = s.sc y) ∧
    r.2 ≤ 2 * s.sc l + 4 := by
  intro r
  let P : ℕ → St → Prop := fun j t => t.sc 785 = s.sc 785 + j ∧ t.ar = s.ar ∧ t.sc l = s.sc l ∧
    (∀ y, y ≠ 785 → y ≠ 786 → t.sc y = s.sc y)
  have h0 : P 0 s := ⟨by simp, rfl, rfl, fun _ _ _ => rfl⟩
  have hstep : ∀ j t, j < s.sc l → P j t → P (j + 1) (Cmd.run (.incr 785) (t.setSc 786 j)).1 := by
    intro j t _ ⟨p1, p2, p3, p4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Cmd.run_incr, St.setSc, Function.update_apply, p1]; omega
    · simp [Cmd.run_incr, St.setSc, p2]
    · simp [Cmd.run_incr, St.setSc, Function.update_apply, p3, hl.1, hl.2]
    · intro y h1 h2; simp [Cmd.run_incr, St.setSc, Function.update_apply, h1, h2, p4 y h1 h2]
  have hI := Cmd.loop_inv (b := l) (c := 786) (body := .incr 785) P h0 hstep
  have hC := Cmd.loop_cost_le (b := l) (c := 786) (body := .incr 785) P 1 h0 hstep (fun _ _ _ _ => by simp [Cmd.run_incr])
  obtain ⟨i1, i2, i3, i4⟩ := hI
  have hr : r = (((Cmd.run (.loop l 786 (.incr 785)) s).1).setSc 785 (((Cmd.run (.loop l 786 (.incr 785)) s).1).sc 785 + 1),
      (Cmd.run (.loop l 786 (.incr 785)) s).2 + 1 + 1) := by
    simp only [r, addL, Cmd.run_seq, Cmd.run_incr]
  rw [hr]
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · simp [St.setSc, i1]
  · simp [St.setSc, i2]
  · simp [St.setSc, Function.update_apply, i3, hl.1]
  · intro y h1 h2; simp [St.setSc, Function.update_apply, h1, i4 y h1 h2]

theorem repAdd_run (l : ℕ) (hl : l ≠ 785 ∧ l ≠ 786) : ∀ (k : ℕ) (s : St),
    let r := Cmd.run (repAdd l k) s
    r.1.sc 785 = s.sc 785 + k * (s.sc l + 1) ∧ r.1.ar = s.ar ∧ r.1.sc l = s.sc l ∧
    (∀ y, y ≠ 785 → y ≠ 786 → r.1.sc y = s.sc y) ∧ r.2 ≤ k * (2 * s.sc l + 6) + 1 := by
  intro k
  induction k with
  | zero => intro s; simp [repAdd, Cmd.run_skip]
  | succ k ih =>
    intro s
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih s
    obtain ⟨j1, j2, j3, j4, j5⟩ := addL_run l hl (Cmd.run (repAdd l k) s).1
    simp only [repAdd, Cmd.run_seq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [j1, i1, i3]; ring
    · rw [j2, i2]
    · rw [j3, i3]
    · intro y h1 h2; rw [j4 y h1 h2, i4 y h1 h2]
    · rw [i3] at j5; nlinarith [i5, j5]

def nlenFlag (m l f : ℕ) : Cmd :=
  .seq (.setK 785 0) (.seq (repAdd l m) (.ifLt 785 2 (.setK f 0) (.setK f 1)))

theorem nlenFlag_run (m l f : ℕ) (hl : l ≠ 785 ∧ l ≠ 786) (hf : f ≠ 785 ∧ f ≠ 786) (hf2 : f ≠ 2) (hl2 : l ≠ 2) (s : St) :
    let r := Cmd.run (nlenFlag m l f) s
    r.1.sc f = (if s.sc 2 ≤ m * (s.sc l + 1) then 1 else 0) ∧ r.1.ar = s.ar ∧ r.1.sc 2 = s.sc 2 ∧
    (∀ y, y ≠ 785 → y ≠ 786 → y ≠ f → r.1.sc y = s.sc y) ∧ r.2 ≤ m * (2 * s.sc l + 6) + 6 := by
  intro r
  have e1 : (s.setSc 785 0).sc l = s.sc l := by simp [St.setSc, Function.update_apply, hl.1]
  obtain ⟨i1, i2, i3, i4, i5⟩ := repAdd_run l hl m (s.setSc 785 0)
  generalize hs2 : Cmd.run (repAdd l m) (s.setSc 785 0) = s2 at i1 i2 i3 i4 i5
  have e2 : s2.1.sc 2 = s.sc 2 := by
    rw [i4 2 (by norm_num) (by norm_num)]; simp [St.setSc]
  simp only [r, nlenFlag, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, hs2]
  have hv : s2.1.sc 785 = m * (s.sc l + 1) := by rw [i1, e1]; simp [St.setSc]
  by_cases h : s2.1.sc 785 < s2.1.sc 2
  · rw [if_pos h]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [St.setSc]; rw [hv, e2] at h; have : ¬ (s.sc 2 ≤ m * (s.sc l + 1)) := by omega
      simp [this]; omega
    · simp [St.setSc, i2]
    · simp [St.setSc, Function.update_apply, hf2.symm, e2]
    · intro y h1 h2 h3; simp [St.setSc, Function.update_apply, h3, i4 y h1 h2]; simp [St.setSc, Function.update_apply, h1]
    · rw [e1] at i5; omega
  · rw [if_neg h]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [St.setSc]; rw [hv, e2] at h; have : s.sc 2 ≤ m * (s.sc l + 1) := by omega
      simp [this]
    · simp [St.setSc, i2]
    · simp [St.setSc, Function.update_apply, hf2.symm, e2]
    · intro y h1 h2 h3; simp [St.setSc, Function.update_apply, h3, i4 y h1 h2]; simp [St.setSc, Function.update_apply, h1]
    · rw [e1] at i5; omega

end ECDLP.L76
