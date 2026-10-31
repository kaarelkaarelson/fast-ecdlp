import ECDLP.L76_Mul

/-!
# L76 / Ops: the comparison flag, the constants `1` and `2^(W-1)`, reduction, plain product
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- scalar 722 := `[V B ≤ V A]`; `tmp` is clobbered -/
def geC (tmp A B : ℕ) : Cmd := .seq (copyA tmp A) (addC true tmp B)

theorem geC_run (tmp A B : ℕ) (h1 : tmp ≠ A) (h2 : tmp ≠ B) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    let r := Cmd.run (geC tmp A B) st
    (r.1.sc 722 = if V (st.ar B) n ≤ V (st.ar A) n then 1 else 0) ∧ ArK (fun a => a = tmp) st r.1 ∧
    ScKeep ZB st r.1 ∧ r.2 ≤ 40 * n + 20 := by
  intro r
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := copyA_run tmp A h1 st n hW
  generalize hs1 : Cmd.run (copyA tmp A) st = s1 at a1 a2 a3 a4 a5 a6
  have w1 : s1.1.sc 710 = n := by rw [a5 710 (by simp [ZC])]; exact hW
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sub_run tmp B h2 s1.1 n w1
  have kB : s1.1.ar B = st.ar B := a4 B (Ne.symm h2)
  rw [kB, a3] at b2
  simp only [r, geC, Cmd.run_seq, hs1]
  refine ⟨?_, ?_, ?_, by omega⟩
  · have := V_lt (((Cmd.run (addC true tmp B) s1.1).1).ar tmp) n
    split_ifs with h
    · by_contra hne; have : (Cmd.run (addC true tmp B) s1.1).1.sc 722 = 0 := by omega
      rw [this] at b2; omega
    · by_contra hne; have : (Cmd.run (addC true tmp B) s1.1).1.sc 722 = 1 := by omega
      rw [this] at b2; omega
  · exact (ArK.trans (D := (· = tmp)) (D' := (· = tmp)) a4 b4).mono (fun a ha => by rcases ha with h | h <;> exact h)
  · exact (a5.trans b5).mono (fun y hy => by rcases hy with h | h; exact Or.inr h; exact Or.inl h)

/-- the constant `1` in `arr` -/
def oneA (arr : ℕ) : Cmd := .seq (zeroA arr) (.seq (.setK 745 1) (.seq (.setK 746 0) (.wr arr 746 1 745)))

/-- the constant `2^(W-1)` in `arr` -/
def powA (arr : ℕ) : Cmd := .seq (zeroA arr) (.seq (.setK 745 1) (.wr arr 710 0 745))

def ZK (y : ℕ) : Prop := ZC y ∨ y = 745 ∨ y = 746

theorem V_zero_of_cells {f : ℕ → ℕ} {m : ℕ} (h : ∀ i, 1 ≤ i → i ≤ m → f i = 0) : V f m = 0 := by
  have : V f m = V (fun _ => 0) m := V_congr fun j h1 h2 => by simpa using h j h1 h2
  rw [this]; simp [V, numCells]

theorem oneA_run (arr : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) (hn : 1 ≤ n) :
    let r := Cmd.run (oneA arr) st
    Cells n (r.1.ar arr) (st.ar arr) ∧ V (r.1.ar arr) n = 1 ∧ ArKeep arr st r.1 ∧ ScKeep ZK st r.1 ∧ r.2 ≤ 5 * n + 10 := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run arr st n hW
  have zc := zeroA_cells arr st n hW
  generalize hz : Cmd.run (zeroA arr) st = s0 at z1 z2 z3 z4 z5 zc
  simp only [r, oneA, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, hz]
  have e : ((((s0.1.setSc 745 1).setSc 746 0).setAr arr (((s0.1.setSc 745 1).setSc 746 0).sc 746 + 1)
      (((s0.1.setSc 745 1).setSc 746 0).sc 745))).ar arr = Function.update (s0.1.ar arr) 1 1 := by
    simp only [St.setSc, St.setAr, St.putAr, Function.update_self, Function.update_of_ne (by norm_num : (745:ℕ) ≠ 746)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]
    intro i
    obtain ⟨h1, h2⟩ := z1 i
    by_cases hi : i = 1
    · subst hi; simp; omega
    · simp only [Function.update_apply, if_neg hi]; exact ⟨h1, h2⟩
  · rw [e]
    have h1 : ∀ m, 1 ≤ m → m ≤ n → V (Function.update (s0.1.ar arr) 1 1) m = 1 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => intro _; simp [V_snoc, V, numCells, bt]
      | succ m hm ih =>
        intro hmn
        rw [V_snoc, ih (by omega)]
        have : bt (Function.update (s0.1.ar arr) 1 1) (m + 1) = 0 := by
          simp only [bt, Function.update_apply, show m + 1 ≠ 1 by omega, if_false]
          rw [zc (m + 1) (by omega) hmn]; simp
        rw [this]; simp
    exact h1 n hn le_rfl
  · intro a ha
    simp only [St.setSc, St.setAr, St.putAr, Function.update_apply, ha, if_false]
    exact z3 a ha
  · intro y hy
    have h745 : y ≠ 745 := fun h => hy (Or.inr (Or.inl h))
    have h746 : y ≠ 746 := fun h => hy (Or.inr (Or.inr h))
    show (Function.update (Function.update s0.1.sc 745 1) 746 0) y = st.sc y
    rw [Function.update_of_ne h746, Function.update_of_ne h745]
    exact z4 y (fun h => hy (Or.inl h))
  · omega

theorem powA_run (arr : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) (hn : 1 ≤ n) :
    let r := Cmd.run (powA arr) st
    Cells n (r.1.ar arr) (st.ar arr) ∧ V (r.1.ar arr) n = 2 ^ (n - 1) ∧ ArKeep arr st r.1 ∧ ScKeep ZK st r.1 ∧
    r.2 ≤ 5 * n + 10 := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run arr st n hW
  have zc := zeroA_cells arr st n hW
  generalize hz : Cmd.run (zeroA arr) st = s0 at z1 z2 z3 z4 z5 zc
  have w0 : s0.1.sc 710 = n := by rw [z4 710 (by simp [ZC])]; exact hW
  simp only [r, powA, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, hz]
  have e : (((s0.1.setSc 745 1).setAr arr (((s0.1.setSc 745 1)).sc 710 + 0)
      (((s0.1.setSc 745 1)).sc 745))).ar arr = Function.update (s0.1.ar arr) n 1 := by
    simp only [St.setSc, St.setAr, St.putAr, Function.update_self, Function.update_of_ne (by norm_num : (710:ℕ) ≠ 745), w0,
      Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]
    intro i
    obtain ⟨h1, h2⟩ := z1 i
    by_cases hi : i = n
    · subst hi; simp; omega
    · simp only [Function.update_apply, if_neg hi]; exact ⟨h1, h2⟩
  · rw [e]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [V_update_succ _ (le_refl 1)]
    rw [V_zero_of_cells (f := s0.1.ar arr) (m := m) (fun i h1 h2 => zc i h1 (by omega))]
    simp
  · intro a ha
    simp only [St.setSc, St.setAr, St.putAr, Function.update_apply, ha, if_false]
    exact z3 a ha
  · intro y hy
    have h745 : y ≠ 745 := fun h => hy (Or.inr (Or.inl h))
    show (Function.update s0.1.sc 745 1) y = st.sc y
    rw [Function.update_of_ne h745]
    exact z4 y (fun h => hy (Or.inl h))
  · omega

end ECDLP.L76
