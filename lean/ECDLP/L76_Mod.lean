import ECDLP.L76_Map

/-!
# L76 / Mod: conditional subtraction, modular addition and doubling, comparison flag
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- arrays outside `D` are unchanged -/
def ArK (D : ℕ → Prop) (s t : St) : Prop := ∀ a, ¬ D a → t.ar a = s.ar a

theorem ArK.trans {D D' : ℕ → Prop} {s t u : St} (h : ArK D s t) (h' : ArK D' t u) :
    ArK (fun a => D a ∨ D' a) s u := fun a ha => by
  rw [h' a (fun h => ha (Or.inr h)), h a (fun h => ha (Or.inl h))]

theorem ArK.mono {D D' : ℕ → Prop} {s t : St} (h : ArK D s t) (hD : ∀ a, D a → D' a) : ArK D' s t :=
  fun a ha => h a (fun h' => ha (hD a h'))

theorem ScKeep.trans {Z Z' : ℕ → Prop} {s t u : St} (h : ScKeep Z s t) (h' : ScKeep Z' t u) :
    ScKeep (fun y => Z y ∨ Z' y) s u := fun y hy => by
  rw [h' y (fun h => hy (Or.inr h)), h y (fun h => hy (Or.inl h))]

theorem ScKeep.mono {Z Z' : ℕ → Prop} {s t : St} (h : ScKeep Z s t) (hZ : ∀ y, Z y → Z' y) : ScKeep Z' s t :=
  fun y hy => h y (fun h' => hy (hZ y h'))

theorem Cells.trans {n : ℕ} {f g h : ℕ → ℕ} (h1 : Cells n f g) (h2 : Cells n g h) : Cells n f h := fun i =>
  ⟨(h1 i).1, fun hn => ((h1 i).2 hn).trans ((h2 i).2 hn)⟩

/-- registers of `addC` and `copyA` -/
def ZB (y : ℕ) : Prop := ZA y ∨ ZC y

def condSub (dst src tmp : ℕ) : Cmd :=
  .seq (copyA tmp dst) (.seq (addC true dst src) (.ifZero 722 (copyA dst tmp) .skip))

theorem condSub_run (dst src tmp : ℕ) (h1 : dst ≠ src) (h2 : dst ≠ tmp) (h3 : src ≠ tmp) (st : St) (n : ℕ)
    (hW : st.sc 710 = n) :
    let r := Cmd.run (condSub dst src tmp) st
    Cells n (r.1.ar dst) (st.ar dst) ∧
    V (r.1.ar dst) n = (if V (st.ar src) n ≤ V (st.ar dst) n then V (st.ar dst) n - V (st.ar src) n else V (st.ar dst) n) ∧
    ArK (fun a => a = dst ∨ a = tmp) st r.1 ∧ ScKeep ZB st r.1 ∧ r.2 ≤ 60 * n + 20 := by
  intro r
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := copyA_run tmp dst (Ne.symm h2) st n hW
  generalize hs1 : Cmd.run (copyA tmp dst) st = s1 at a1 a2 a3 a4 a5 a6
  have w1 : s1.1.sc 710 = n := by rw [a5 710 (by unfold ZC; omega)]; exact hW
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sub_run dst src h1 s1.1 n w1
  generalize hs2 : Cmd.run (addC true dst src) s1.1 = s2 at b1 b2 b3 b4 b5 b6
  have d1 : s1.1.ar dst = st.ar dst := a4 dst h2
  have d2 : s1.1.ar src = st.ar src := a4 src h3
  have d3 : s1.1.ar tmp = (fun i => 0) ∨ True := Or.inr trivial
  have e2 : s2.1.ar tmp = s1.1.ar tmp := b4 tmp (Ne.symm h2)
  have e710 : s2.1.sc 710 = n := by rw [b5 710 (by unfold ZA; omega), w1]
  rw [d1, d2] at b2
  rw [d1] at b1
  simp only [r, condSub, Cmd.run_seq, Cmd.run_ifZero, hs1, hs2]
  by_cases hc : s2.1.sc 722 = 0
  · -- borrow: restore
    simp only [hc, if_true]
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := copyA_run dst tmp h2 s2.1 n e710
    generalize hs3 : Cmd.run (copyA dst tmp) s2.1 = s3 at c1 c2 c3 c4 c5 c6
    have hlt : V (st.ar dst) n < V (st.ar src) n := by
      have := V_lt (s2.1.ar dst) n; rw [hc] at b2; omega
    have hnle : ¬ V (st.ar src) n ≤ V (st.ar dst) n := by omega
    refine ⟨c1.trans b1, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hnle, c3, e2, a3]
    · exact ((ArK.trans (D := (· = tmp)) (D' := (· = dst)) a4 b4).trans (D' := (· = dst)) c4).mono (by intro a ha; tauto)
    · exact ((a5.trans b5).trans c5).mono (by intro y hy; simp only [ZB] at hy ⊢; tauto)
    · omega
  · simp only [hc, if_false, Cmd.run_skip]
    have hc1 : s2.1.sc 722 = 1 := by omega
    rw [hc1] at b2
    have hle : V (st.ar src) n ≤ V (st.ar dst) n := by omega
    refine ⟨b1, ?_, ?_, ?_, ?_⟩
    · rw [if_pos hle]; omega
    · exact (ArK.trans (D := (· = tmp)) (D' := (· = dst)) a4 b4).mono (by intro a ha; tauto)
    · exact (a5.trans b5).mono (by intro y hy; simp only [ZB] at hy ⊢; tauto)
    · omega

/-! ### zeroing -/

def zeroBody (dst : ℕ) : Cmd := .seq (.setK 733 0) (.wr dst 731 1 733)
/-- `dst[1..W] := 0` -/
def zeroA (dst : ℕ) : Cmd := .loop 710 731 (zeroBody dst)

theorem zeroA_run (dst : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    Cells n ((Cmd.run (zeroA dst) st).1.ar dst) (st.ar dst) ∧ V ((Cmd.run (zeroA dst) st).1.ar dst) n = 0 ∧
    ArKeep dst st (Cmd.run (zeroA dst) st).1 ∧ ScKeep ZC st (Cmd.run (zeroA dst) st).1 ∧
    (Cmd.run (zeroA dst) st).2 ≤ 5 * n + 1 := by
  have key := mapLoop (b := 710) (c := 731) (body := zeroBody dst) dst (fun _ => 0) ZC 4 st n hW
    (by unfold ZC; omega) (fun j => by omega) (by
      intro t j hj h3 h4
      simp [zeroBody, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, Function.update_apply]
      intro y hy; simp only [ZC, not_and, not_le] at hy
      split_ifs <;> first | rfl | (exfalso; omega))
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  unfold zeroA
  refine ⟨k1, ?_, k3, k4, by omega⟩
  have : V ((Cmd.run (.loop 710 731 (zeroBody dst)) st).1.ar dst) n = V (fun _ => 0) n :=
    V_congr fun j h1 h2 => by have := k2 j h1 h2; simpa using this
  rw [this]; simp [V, numCells]

theorem zeroA_cells (dst : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    ∀ i, 1 ≤ i → i ≤ n → (Cmd.run (zeroA dst) st).1.ar dst i = 0 := by
  have key := mapLoop (b := 710) (c := 731) (body := zeroBody dst) dst (fun _ => 0) ZC 4 st n hW
    (by unfold ZC; omega) (fun j => by omega) (by
      intro t j hj h3 h4
      simp [zeroBody, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, Function.update_apply]
      intro y hy; simp only [ZC, not_and, not_le] at hy
      split_ifs <;> first | rfl | (exfalso; omega))
  intro i h1 h2
  exact key.2.1 i h1 h2

/-! ### modular addition and doubling -/

def addMod (dst src P tmp : ℕ) : Cmd := .seq (addC false dst src) (condSub dst P tmp)

theorem addMod_run (dst src P tmp : ℕ) (h1 : dst ≠ src) (h2 : dst ≠ P) (h3 : dst ≠ tmp) (h4 : src ≠ P) (h5 : P ≠ tmp)
    (h6 : src ≠ tmp) (st : St) (n : ℕ) (hW : st.sc 710 = n)
    (hA : V (st.ar dst) n < V (st.ar P) n) (hB : V (st.ar src) n < V (st.ar P) n)
    (hP : 2 * V (st.ar P) n ≤ 2 ^ n) :
    let r := Cmd.run (addMod dst src P tmp) st
    Cells n (r.1.ar dst) (st.ar dst) ∧
    V (r.1.ar dst) n = (V (st.ar dst) n + V (st.ar src) n) % V (st.ar P) n ∧
    ArK (fun a => a = dst ∨ a = tmp) st r.1 ∧ ScKeep ZB st r.1 ∧ r.2 ≤ 90 * n + 40 := by
  intro r
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := add_run dst src h1 st n hW
  generalize hs1 : Cmd.run (addC false dst src) st = s1 at a1 a2 a3 a4 a5 a6
  have w1 : s1.1.sc 710 = n := by rw [a5 710 (by unfold ZA; omega)]; exact hW
  have hc : s1.1.sc 722 = 0 := by
    by_contra hne
    have : s1.1.sc 722 = 1 := by omega
    rw [this] at a2
    have := V_lt (st.ar dst) n
    omega
  rw [hc] at a2
  have kP : s1.1.ar P = st.ar P := a4 P (Ne.symm h2)
  have kS : s1.1.ar src = st.ar src := a4 src (Ne.symm h1)
  obtain ⟨b1, b2, b3, b4, b5⟩ := condSub_run dst P tmp h2 h3 h5 s1.1 n w1
  rw [kP] at b2
  simp only [r, addMod, Cmd.run_seq, hs1]
  refine ⟨b1.trans a1, ?_, ?_, ?_, by omega⟩
  · rw [b2]
    simp only [zero_mul, add_zero] at a2
    rw [a2]
    split_ifs with hle
    · have : V (st.ar dst) n + V (st.ar src) n < 2 * V (st.ar P) n := by omega
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  · exact (ArK.trans (D := (· = dst)) (D' := fun a => a = dst ∨ a = tmp) a4 b3).mono (by intro a ha; tauto)
  · exact (a5.trans b4).mono (by intro y hy; simp only [ZB] at hy ⊢; tauto)

def dblMod (dst P tmp tmp2 : ℕ) : Cmd := .seq (copyA tmp2 dst) (addMod dst tmp2 P tmp)

theorem dblMod_run (dst P tmp tmp2 : ℕ) (h1 : dst ≠ P) (h2 : dst ≠ tmp) (h3 : dst ≠ tmp2) (h4 : P ≠ tmp)
    (h5 : P ≠ tmp2) (h6 : tmp ≠ tmp2) (st : St) (n : ℕ) (hW : st.sc 710 = n)
    (hA : V (st.ar dst) n < V (st.ar P) n) (hP : 2 * V (st.ar P) n ≤ 2 ^ n) :
    let r := Cmd.run (dblMod dst P tmp tmp2) st
    Cells n (r.1.ar dst) (st.ar dst) ∧
    V (r.1.ar dst) n = (2 * V (st.ar dst) n) % V (st.ar P) n ∧
    ArK (fun a => a = dst ∨ a = tmp ∨ a = tmp2) st r.1 ∧ ScKeep ZB st r.1 ∧ r.2 ≤ 100 * n + 50 := by
  intro r
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := copyA_run tmp2 dst (Ne.symm h3) st n hW
  generalize hs1 : Cmd.run (copyA tmp2 dst) st = s1 at a1 a2 a3 a4 a5 a6
  have w1 : s1.1.sc 710 = n := by rw [a5 710 (by unfold ZC; omega)]; exact hW
  have kP : s1.1.ar P = st.ar P := a4 P h5
  have kD : s1.1.ar dst = st.ar dst := a4 dst h3
  obtain ⟨b1, b2, b3, b4, b5⟩ := addMod_run dst tmp2 P tmp h3 h1 h2 (Ne.symm h5) h4 (Ne.symm h6) s1.1 n w1
    (by rw [kD, kP]; exact hA) (by rw [a3, kP]; exact hA) (by rw [kP]; exact hP)
  rw [kD, kP, a3] at b2
  simp only [r, dblMod, Cmd.run_seq, hs1]
  rw [kD] at b1
  refine ⟨b1, ?_, ?_, ?_, by omega⟩
  · rw [b2, two_mul]
  · have a4' : ArK (fun a => a = tmp2) st s1.1 := a4
    exact (ArK.trans a4' b3).mono (by intro a ha; rcases ha with h | h | h <;> simp [h])
  · have := ScKeep.trans a5 b4
    exact this.mono (fun y hy => by
      rcases hy with h | h
      · exact Or.inr h
      · exact h)

end ECDLP.L76
