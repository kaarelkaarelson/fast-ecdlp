import ECDLP.L76_Root

/-!
# L76 / Const: constants given by a list of set bits
`constA arr l` : `arr := ∑_{i ∈ l} 2^(i-1)` (the cells `i ∈ l`, `1 ≤ i ≤ W`, are set); scalars `745, 746`.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def setBit (arr i : ℕ) : Cmd := .seq (.setK 746 i) (.wr arr 746 0 745)

def setBits (arr : ℕ) : List ℕ → Cmd
  | [] => .skip
  | i :: l => .seq (setBits arr l) (setBit arr i)

def constA (arr : ℕ) (l : List ℕ) : Cmd :=
  .seq (zeroA arr) (.seq (.setK 745 1) (setBits arr l))

theorem setBits_run (arr : ℕ) (W : ℕ) : ∀ (l : List ℕ) (st : St), l.Nodup → (∀ i ∈ l, 1 ≤ i ∧ i ≤ W) → st.sc 745 = 1 →
    (∀ i, 1 ≤ i → i ≤ W → st.ar arr i = 0) →
    let r := Cmd.run (setBits arr l) st
    (∀ i, 1 ≤ i → i ≤ W → r.1.ar arr i = if i ∈ l then 1 else 0) ∧ r.1.sc 745 = 1 ∧ (∀ a, a ≠ arr → r.1.ar a = st.ar a) ∧
    (∀ y, y ≠ 746 → r.1.sc y = st.sc y) ∧ r.2 ≤ 4 * l.length + 1 ∧
    V (r.1.ar arr) W = (l.map (fun i => 2 ^ (i - 1))).sum := by
  intro l
  induction l with
  | nil =>
    intro st _ _ h745 hz
    refine ⟨fun i h1 h2 => by simp [setBits, Cmd.run_skip, hz i h1 h2], by simpa [setBits, Cmd.run_skip] using h745,
      fun a _ => by simp [setBits, Cmd.run_skip], fun y _ => by simp [setBits, Cmd.run_skip], by simp [setBits, Cmd.run_skip], ?_⟩
    simp only [setBits, Cmd.run_skip, List.map_nil, List.sum_nil]
    exact V_zero_of_cells hz
  | cons j l ih =>
    intro st hnd hb h745 hz
    obtain ⟨hj, hl⟩ := List.nodup_cons.1 hnd
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih st hl (fun i hi => hb i (List.mem_cons_of_mem _ hi)) h745 hz
    generalize hs : Cmd.run (setBits arr l) st = s1 at i1 i2 i3 i4 i5 i6
    have hjb := hb j (List.mem_cons_self ..)
    have e : ((s1.1.setSc 746 j).setAr arr (((s1.1.setSc 746 j)).sc 746 + 0) ((s1.1.setSc 746 j).sc 745)).ar arr =
        Function.update (s1.1.ar arr) j 1 := by
      simp only [St.setSc, St.setAr, St.putAr, Function.update_self, Nat.add_zero,
        Function.update_of_ne (by norm_num : (745:ℕ) ≠ 746), i2]
    simp only [setBits, setBit, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i h1 h2
      rw [e]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_apply, if_neg hij, i1 i h1 h2]
        simp [List.mem_cons, hij]
    · simp only [St.setSc_sc, St.setAr_sc]
      rw [Function.update_of_ne (by norm_num : (745:ℕ) ≠ 746)]; exact i2
    · intro a ha
      simp only [St.setAr_ar, Function.update_of_ne ha]
      exact i3 a ha
    · intro y hy
      simp only [St.setSc_sc, St.setAr_sc, Function.update_of_ne hy]
      exact i4 y hy
    · simp only [List.length_cons]; omega
    · rw [e]
      have hcell : s1.1.ar arr j = 0 := by
        have := i1 j hjb.1 hjb.2
        rw [if_neg hj] at this; exact this
      rw [V_update_one (s1.1.ar arr) j W hjb.1 hjb.2 hcell, i6]
      simp [List.map_cons, List.sum_cons]; ring

theorem constA_run (arr : ℕ) (l : List ℕ) (hnd : l.Nodup) (st : St) (W : ℕ) (hW : st.sc 710 = W) (hb : ∀ i ∈ l, 1 ≤ i ∧ i ≤ W) :
    let r := Cmd.run (constA arr l) st
    V (r.1.ar arr) W = (l.map (fun i => 2 ^ (i - 1))).sum ∧ r.1.sc 710 = W ∧ ArKeep arr st r.1 ∧ ScKeep ZK st r.1 ∧
    r.2 ≤ 5 * W + 4 * l.length + 10 := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run arr st W hW
  have zc := zeroA_cells arr st W hW
  generalize hz : Cmd.run (zeroA arr) st = s0 at z1 z2 z3 z4 z5 zc
  have n745 : s0.1.sc 710 = W := by rw [z4 710 (by simp [ZC])]; exact hW
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := setBits_run arr W l (s0.1.setSc 745 1) hnd hb (by simp [St.setSc])
    (fun i h1 h2 => by simpa [St.setSc] using zc i h1 h2)
  generalize hs : Cmd.run (setBits arr l) (s0.1.setSc 745 1) = s1 at i1 i2 i3 i4 i5 i6
  simp only [r, constA, Cmd.run_seq, Cmd.run_setK, hz, hs]
  refine ⟨i6, ?_, ?_, ?_, by omega⟩
  · rw [i4 710 (by norm_num)]; simp [St.setSc]; exact n745
  · intro a ha
    rw [i3 a ha]; simp only [St.setSc_ar]; exact z3 a ha
  · intro y hy
    have h745 : y ≠ 745 := fun h => hy (Or.inr (Or.inl h))
    have h746 : y ≠ 746 := fun h => hy (Or.inr (Or.inr h))
    rw [i4 y h746]
    simp only [St.setSc_sc]
    rw [Function.update_of_ne h745]
    exact z4 y (fun h => hy (Or.inl h))

end ECDLP.L76
