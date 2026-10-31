import ECDLP.L76_Parse
import ECDLP.L76_Ops

/-!
# L78 / Piece: the scalar-level pieces of the per-call length test

* `setW m` : `sc 710 := (m+2) * sc 0 + 5` (the global bignum width), scratch `950`;
* `scanC` : `sc 951 := Nat.size (V (ar 47) (sc 710))` (index of the top set cell), scratch `950, 952`;
* `finC m` : `sc 3 := [sc 2 ≤ m * (sc 951 + 1)]`, scratch `951, 953, 954`.
-/
namespace ECDLP.L78
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

/-! ### the width -/
def addN : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (addTo 710 0 950) (addN k)

def setW (m : ℕ) : Cmd := .seq (.setK 710 5) (addN (m + 2))

theorem addN_run (k : ℕ) : ∀ (st : St),
    (Cmd.run (addN k) st).1.sc 710 = st.sc 710 + k * st.sc 0 ∧ (Cmd.run (addN k) st).1.sc 0 = st.sc 0 ∧
    (Cmd.run (addN k) st).1.ar = st.ar ∧
    (∀ y, y ≠ 710 → y ≠ 950 → (Cmd.run (addN k) st).1.sc y = st.sc y) ∧
    (Cmd.run (addN k) st).2 ≤ k * (2 * st.sc 0 + 7) + 1 := by
  induction k with
  | zero => intro st; simp [addN, Cmd.run]
  | succ k ih =>
    intro st
    obtain ⟨h1, h2⟩ := run_addTo (x := 710) (y := 0) (t := 950) (by decide) st
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih ((st.setSc 710 (st.sc 710 + st.sc 0)).setSc 950 0)
    simp only [addN, Cmd.run_seq, h1, h2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [i1]; simp; ring
    · rw [i2]; simp
    · rw [i3]; simp
    · intro y hy1 hy2
      rw [i4 y hy1 hy2]; simp [hy1, hy2]
    · have := i5; simp at this ⊢; nlinarith

theorem setW_run (st : St) :
    (Cmd.run (setW m) st).1.sc 710 = (m + 2) * st.sc 0 + 5 ∧ (Cmd.run (setW m) st).1.sc 0 = st.sc 0 ∧
    (Cmd.run (setW m) st).1.ar = st.ar ∧
    (∀ y, y ≠ 710 → y ≠ 950 → (Cmd.run (setW m) st).1.sc y = st.sc y) ∧
    (Cmd.run (setW m) st).2 ≤ (m + 2) * (2 * st.sc 0 + 7) + 4 := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := addN_run (m + 2) (st.setSc 710 5)
  simp only [St.setSc_sc, St.setSc_ar, Function.update_apply] at i1 i2 i3 i4 i5
  simp only [setW, Cmd.run_seq, Cmd.run_setK]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp at i1 ⊢; rw [i1]; ring
  · simpa using i2
  · simpa using i3
  · intro y h1 h2; have := i4 y h1 h2; simpa [h1] using this
  · simp at i5 ⊢; omega


/-! ### the size of the top set cell -/
def scanBody : Cmd := .seq (.rd 952 47 950 1) (.ifZero 952 .skip (.seq (.copy 951 950) (.incr 951)))

def scanC : Cmd := .seq (.setK 951 0) (.loop 710 950 scanBody)

theorem size_snoc (v j : ℕ) (hv : v < 2 ^ j) : Nat.size (v + 2 ^ j) = j + 1 := by
  apply le_antisymm
  · rw [Nat.size_le]; rw [pow_succ]; omega
  · rw [Nat.succ_le_iff, Nat.lt_size]; omega

theorem scan_run (st : St) (W : ℕ) (hW : st.sc 710 = W) :
    (Cmd.run scanC st).1.sc 951 = Nat.size (V (st.ar 47) W) ∧ (Cmd.run scanC st).1.ar = st.ar ∧
    (∀ y, y ≠ 950 → y ≠ 951 → y ≠ 952 → (Cmd.run scanC st).1.sc y = st.sc y) ∧
    (Cmd.run scanC st).2 ≤ 7 * W + 3 := by
  let P : ℕ → St → Prop := fun j t => t.sc 951 = Nat.size (V (st.ar 47) j) ∧ t.ar = st.ar ∧
    (∀ y, y ≠ 950 → y ≠ 951 → y ≠ 952 → t.sc y = st.sc y)
  have h0 : P 0 (st.setSc 951 0) := by
    refine ⟨by simp [V, numCells], rfl, fun y _ h _ => by simp [h]⟩
  have hstep : ∀ j t, j < (st.setSc 951 0).sc 710 → P j t → P (j + 1) (Cmd.run scanBody (t.setSc 950 j)).1 := by
    intro j t _ ⟨p1, p2, p3⟩
    have hV := V_lt (st.ar 47) j
    by_cases hz : st.ar 47 (j + 1) = 0
    · have hb : bt (st.ar 47) (j + 1) = 0 := by simp [bt, hz]
      simp only [P, scanBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, St.setSc_sc, St.setSc_ar, p2, Function.update_apply]
      simp [hz, V_snoc, hb, p1]
      refine ⟨p2, fun y h1 h2 h3 => ?_⟩
      simp [h1, h2, h3, p3 y h1 h2 h3]
    · have hb : bt (st.ar 47) (j + 1) = 1 := by simp [bt, hz]
      simp only [P, scanBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_copy, Cmd.run_incr, St.setSc_sc, St.setSc_ar, p2, Function.update_apply]
      simp [hz]
      refine ⟨?_, p2, fun y h1 h2 h3 => ?_⟩
      · rw [V_snoc, hb, one_mul, size_snoc _ _ hV]
      · simp [h1, h2, h3, p3 y h1 h2 h3]
  have hI := Cmd.loop_inv (b := 710) (c := 950) (body := scanBody) (st := st.setSc 951 0) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 710) (c := 950) (body := scanBody) (st := st.setSc 951 0) P 6 h0 hstep
    (by
      intro j t _ ⟨p1, p2, p3⟩
      by_cases hz : st.ar 47 (j + 1) = 0 <;>
      simp [scanBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_copy, Cmd.run_incr, p2, hz, Cmd.run_skip])
  simp only [St.setSc_sc, Function.update_self, Function.update_of_ne (show (710:ℕ) ≠ 951 by decide), hW] at hI hC
  simp only [scanC, Cmd.run_seq, Cmd.run_setK]
  obtain ⟨i1, i2, i3⟩ := hI
  refine ⟨i1, i2, i3, ?_⟩
  omega


/-! ### the final comparison -/
def decrM : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (.decr 953) (decrM k)

theorem decrM_run (k : ℕ) : ∀ st : St, (Cmd.run (decrM k) st).1.sc 953 = st.sc 953 - k ∧
    (Cmd.run (decrM k) st).1.ar = st.ar ∧ (∀ y, y ≠ 953 → (Cmd.run (decrM k) st).1.sc y = st.sc y) ∧
    (Cmd.run (decrM k) st).2 ≤ 2 * k + 1 := by
  induction k with
  | zero => intro st; simp [decrM, Cmd.run]
  | succ k ih =>
    intro st
    obtain ⟨i1, i2, i3, i4⟩ := ih (st.setSc 953 (st.sc 953 - 1))
    simp only [decrM, Cmd.run_seq, Cmd.run_decr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [i1]; simp; omega
    · rw [i2]; simp
    · intro y hy; rw [i3 y hy]; simp [hy]
    · omega

def finC (m : ℕ) : Cmd :=
  .seq (.incr 951) (.seq (.copy 953 2) (.seq (.loop 951 954 (decrM m)) (.ifZero 953 (.setK 3 1) (.setK 3 0))))

theorem fin_run (m : ℕ) (st : St) :
    (Cmd.run (finC m) st).1.sc 3 = (if st.sc 2 ≤ m * (st.sc 951 + 1) then 1 else 0) ∧
    (Cmd.run (finC m) st).1.ar = st.ar ∧
    (∀ y, y ≠ 3 → y ≠ 951 → y ≠ 953 → y ≠ 954 → (Cmd.run (finC m) st).1.sc y = st.sc y) ∧
    (Cmd.run (finC m) st).2 ≤ (st.sc 951 + 1) * (2 * m + 2) + 8 := by
  set s1 : St := (st.setSc 951 (st.sc 951 + 1)).setSc 953 (st.sc 2) with hs1
  have s1_951 : s1.sc 951 = st.sc 951 + 1 := by simp [hs1]
  let P : ℕ → St → Prop := fun j t => t.sc 953 = st.sc 2 - j * m ∧ t.ar = st.ar ∧
    (∀ y, y ≠ 953 → y ≠ 954 → t.sc y = s1.sc y)
  have h0 : P 0 s1 := ⟨by simp [hs1], rfl, fun _ _ _ => rfl⟩
  have hstep : ∀ j t, j < s1.sc 951 → P j t → P (j + 1) (Cmd.run (decrM m) (t.setSc 954 j)).1 := by
    intro j t _ ⟨p1, p2, p3⟩
    obtain ⟨i1, i2, i3, i4⟩ := decrM_run m (t.setSc 954 j)
    refine ⟨?_, ?_, fun y h1 h2 => ?_⟩
    · rw [i1]; simp [p1]; rw [Nat.sub_sub]; congr 1; ring
    · rw [i2]; simp [p2]
    · rw [i3 y h1]; simp [h2, p3 y h1 h2]
  have hI := Cmd.loop_inv (b := 951) (c := 954) (body := decrM m) (st := s1) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 951) (c := 954) (body := decrM m) (st := s1) P (2 * m + 1) h0 hstep
    (fun j t _ _ => (decrM_run m (t.setSc 954 j)).2.2.2)
  obtain ⟨q1, q2, q3⟩ := hI
  rw [s1_951] at q1 hC
  simp only [finC, Cmd.run_seq, Cmd.run_incr, Cmd.run_copy, Cmd.run_ifZero]
  have e2 : (st.setSc 951 (st.sc 951 + 1)).sc 2 = st.sc 2 := by simp
  rw [e2, ← hs1]
  generalize hL : Cmd.run (.loop 951 954 (decrM m)) s1 = L at q1 q2 q3 hC
  have hz : L.1.sc 953 = 0 ↔ st.sc 2 ≤ m * (st.sc 951 + 1) := by
    rw [q1]; constructor
    · intro h; have := Nat.sub_eq_zero_iff_le.1 h; nlinarith
    · intro h; apply Nat.sub_eq_zero_of_le; nlinarith
  have hC2 : L.2 ≤ (st.sc 951 + 1) * (2 * m + 2) + 1 := by
    have : (st.sc 951 + 1) * (2 * m + 1 + 1) = (st.sc 951 + 1) * (2 * m + 2) := by ring
    omega
  by_cases h : L.1.sc 953 = 0
  · have h' := hz.1 h
    simp only [h, if_true, Cmd.run_setK, h', St.setSc_sc, Function.update_self, St.setSc_ar]
    refine ⟨trivial, q2, fun y h3 h951 h953 h954 => ?_, by omega⟩
    simp [h3, q3 y h953 h954, hs1, h951, h953]
  · have h' : ¬ st.sc 2 ≤ m * (st.sc 951 + 1) := fun hh => h (hz.2 hh)
    simp only [h, if_false, Cmd.run_setK, h', St.setSc_sc, Function.update_self, St.setSc_ar]
    refine ⟨trivial, q2, fun y h3 h951 h953 h954 => ?_, by omega⟩
    simp [h3, q3 y h953 h954, hs1, h951, h953]

end ECDLP.L78
