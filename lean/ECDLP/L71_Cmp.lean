import ECDLP.L71_MinFac

/-!
# L71 / Cmp: copy an array into scratch, and compare two input-format arrays

Scalars used (all `≥ 1200`, above Rudich's `drvC (uniC UP)` footprint `< 1180`): `1200` (bound), `1201` (counter),
`1202, 1203` (temporaries), `1204` (flag), `1205` (`n`), `1206` (`0`), `1207` (`2`).
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

/-- set `f := 0` unless `x` and `y` hold equal values -/
def neqSet (x y f : ℕ) : Cmd := .ifLt x y (.setK f 0) (.ifLt y x (.setK f 0) .skip)

theorem neqSet_run (x y f : ℕ) (s : St) :
    Cmd.run (neqSet x y f) s = (if s.sc x = s.sc y then s else s.setSc f 0, if s.sc x = s.sc y then 3 else if s.sc x < s.sc y then 2 else 3) := by
  rcases lt_trichotomy (s.sc x) (s.sc y) with h | h | h
  · simp [neqSet, Cmd.run_ifLt, Cmd.run_setK, h, h.ne]
  · simp [neqSet, Cmd.run_ifLt, Cmd.run_skip, h]
  · simp [neqSet, Cmd.run_ifLt, Cmd.run_setK, Cmd.run_skip, h, h.ne', Nat.lt_asymm h]

/-- normalise `x` to `0/1` -/
def normB (x : ℕ) : Cmd := .ifZero x .skip (.setK x 1)

theorem normB_run (x : ℕ) (s : St) :
    Cmd.run (normB x) s = (if s.sc x = 0 then s else s.setSc x 1, 2) := by
  by_cases h : s.sc x = 0 <;> simp [normB, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_setK, h]

def cmpBody (q o : ℕ) : Cmd :=
  .seq (.rd 1202 q 1201 1) (.seq (.rd 1203 o 1201 1)
    (.seq (normB 1202) (.seq (normB 1203) (neqSet 1202 1203 1204))))

def cmpPre (q o : ℕ) : Cmd :=
  .seq (.setK 1204 1) (.seq (.copy 1205 1200) (.seq (.decr 1205) (.seq (.setK 1206 0) (.seq (.setK 1207 2)
    (.seq (.ifLt 1205 1207 (.setK 1204 0) .skip) (.seq (.rd 1202 q 1206 0) (.seq (.rd 1203 o 1206 0)
      (neqSet 1202 1203 1204))))))))

/-- compare array 5 (the saved input, `n + 1` cells) with array 2 (the output): flag in scalar 1204 -/
def cmpC (q o : ℕ) : Cmd := .seq (cmpPre q o) (.loop 1205 1201 (cmpBody q o))

theorem cmpPre_run (q o : ℕ) (s : St) (n : ℕ) (h : s.sc 1200 = n + 1) :
    (Cmd.run (cmpPre q o) s).1.sc 1204 = (if 2 ≤ n ∧ s.ar q 0 = s.ar o 0 then 1 else 0) ∧
    (Cmd.run (cmpPre q o) s).1.sc 1205 = n ∧ (Cmd.run (cmpPre q o) s).1.ar = s.ar ∧ (Cmd.run (cmpPre q o) s).2 ≤ 20 := by
  by_cases h2 : n ≤ 1
  · have : ¬ (2 ≤ n) := by omega
    simp [cmpPre, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy, Cmd.run_decr, Cmd.run_ifLt, Cmd.run_rd, Cmd.run_skip,
      neqSet_run, Function.update_apply, h, h2, this]
    split_ifs <;> simp_all
  · have : 2 ≤ n := by omega
    simp [cmpPre, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy, Cmd.run_decr, Cmd.run_ifLt, Cmd.run_rd, Cmd.run_skip,
      neqSet_run, Function.update_apply, h, h2, this]
    split_ifs <;> simp_all

theorem cmpBody_step (q o : ℕ) (s : St) (i f : ℕ) (hf : s.sc 1204 = f) :
    (Cmd.run (cmpBody q o) (s.setSc 1201 i)).1.sc 1204 =
      (if f = 0 then 0 else if (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0) then f else 0) ∧
    (Cmd.run (cmpBody q o) (s.setSc 1201 i)).1.ar = s.ar ∧
    (∀ y, y ≠ 1201 → y ≠ 1202 → y ≠ 1203 → y ≠ 1204 → (Cmd.run (cmpBody q o) (s.setSc 1201 i)).1.sc y = s.sc y) ∧
    (Cmd.run (cmpBody q o) (s.setSc 1201 i)).2 ≤ 14 := by
  by_cases a : s.ar q (i + 1) = 0 <;> by_cases b : s.ar o (i + 1) = 0
  all_goals
    simp [cmpBody, Cmd.run_seq, Cmd.run_rd, normB_run, neqSet_run, Function.update_apply, hf, a, b]
    try (split_ifs <;> simp_all <;> omega)
    all_goals (intro y h1 h2 h3 h4; simp [h1, h2, h3, h4])


theorem cmpC_run (q o : ℕ) (s : St) (n : ℕ) (h : s.sc 1200 = n + 1) :
    (Cmd.run (cmpC q o) s).1.sc 1204 = (if 2 ≤ n ∧ s.ar q 0 = s.ar o 0 ∧
        ∀ i, i < n → (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0) then 1 else 0) ∧
    (Cmd.run (cmpC q o) s).1.ar = s.ar ∧ (Cmd.run (cmpC q o) s).2 ≤ 15 * n + 40 := by
  obtain ⟨p1, p2, p3, p4⟩ := cmpPre_run q o s n h
  generalize hp : Cmd.run (cmpPre q o) s = r at p1 p2 p3 p4
  let P : ℕ → St → Prop := fun j t => t.ar = s.ar ∧
    t.sc 1204 = (if (2 ≤ n ∧ s.ar q 0 = s.ar o 0) ∧ ∀ i, i < j → (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0) then 1 else 0)
  have h0 : P 0 r.1 := ⟨p3, by rw [p1]; simp⟩
  have hstep : ∀ j t, j < r.1.sc 1205 → P j t → P (j + 1) (Cmd.run (cmpBody q o) (t.setSc 1201 j)).1 := by
    intro j t _ ⟨q1, q2⟩
    obtain ⟨c1, c2, c3, c4⟩ := cmpBody_step q o t j _ rfl
    refine ⟨by rw [c2, q1], ?_⟩
    rw [c1, q2, q1]
    have key : (∀ i, i < j + 1 → (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0)) ↔
        ((∀ i, i < j → (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0)) ∧ (s.ar q (j + 1) = 0 ↔ s.ar o (j + 1) = 0)) := by
      constructor
      · intro H; exact ⟨fun i hi => H i (by omega), H j (by omega)⟩
      · rintro ⟨H, hb⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact H i hi
        · subst hi; exact hb
    simp only [key]
    by_cases hE : (2 ≤ n ∧ s.ar q 0 = s.ar o 0) <;> by_cases hv : (∀ i, i < j → (s.ar q (i + 1) = 0 ↔ s.ar o (i + 1) = 0)) <;>
      by_cases hb : (s.ar q (j + 1) = 0 ↔ s.ar o (j + 1) = 0) <;> simp [hE, hv, hb]
  have hI := Cmd.loop_inv (b := 1205) (c := 1201) (body := cmpBody q o) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 1205) (c := 1201) (body := cmpBody q o) P 14 h0 hstep
    (fun j t _ ⟨q1, q2⟩ => (cmpBody_step q o t j _ rfl).2.2.2)
  rw [p2] at hI hC
  have hrun : Cmd.run (cmpC q o) s = ((Cmd.run (.loop 1205 1201 (cmpBody q o)) r.1).1,
      r.2 + (Cmd.run (.loop 1205 1201 (cmpBody q o)) r.1).2 + 1) := by
    simp only [cmpC, Cmd.run_seq, hp]
  rw [hrun]
  obtain ⟨i1, i2⟩ := hI
  refine ⟨?_, i1, ?_⟩
  · rw [i2]
    simp only [and_assoc]
  · simp only
    omega

end ECDLP.L71
