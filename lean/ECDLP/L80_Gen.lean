import ECDLP.L80_Lo
import ECDLP.L76_Layer

/-!
# L80 / Gen: scalar arithmetic by loops (`addS`, `dbl`) and the zero-padded cell copy `padCopy`
Scratch scalars `810 .. 899` (L76 uses `710 .. 799`).
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `z := z + (scalar x)`, counter `c` -/
def addS (z x c : ℕ) : Cmd := .loop x c (.incr z)

theorem addS_run (z x c : ℕ) (hzx : z ≠ x) (hxc : x ≠ c) (hzc : z ≠ c) (st : St) :
    let r := Cmd.run (addS z x c) st
    r.1.sc z = st.sc z + st.sc x ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → r.1.sc y = st.sc y) ∧ r.2 ≤ 2 * st.sc x + 1 := by
  intro r
  let P : ℕ → St → Prop := fun j t => t.sc z = st.sc z + j ∧ t.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → t.sc y = st.sc y)
  have h0 : P 0 st := ⟨by simp, rfl, fun _ _ _ => rfl⟩
  have hstep : ∀ j t, j < st.sc x → P j t → P (j + 1) (Cmd.run (.incr z) (t.setSc c j)).1 := by
    intro j t _ ⟨p1, p2, p3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [Cmd.run_incr, St.setSc, Function.update_apply, hzc, p1]; omega
    · simp [Cmd.run_incr, St.setSc, p2]
    · intro y hy1 hy2; simp [Cmd.run_incr, St.setSc, Function.update_apply, hy1, hy2, p3 y hy1 hy2]
  have hI := Cmd.loop_inv (b := x) (c := c) (body := .incr z) P h0 hstep
  have hC := Cmd.loop_cost_le (b := x) (c := c) (body := .incr z) P 1 h0 hstep (fun _ _ _ _ => by simp [Cmd.run_incr])
  obtain ⟨i1, i2, i3⟩ := hI
  exact ⟨i1, i2, i3, by simp only [r, addS]; omega⟩

/-- `z := 2 z` through the temporary `tmp` -/
def dbl (z tmp c : ℕ) : Cmd := .seq (.copy tmp z) (addS z tmp c)

theorem dbl_run (z tmp c : ℕ) (hzt : z ≠ tmp) (htc : tmp ≠ c) (hzc : z ≠ c) (st : St) :
    let r := Cmd.run (dbl z tmp c) st
    r.1.sc z = 2 * st.sc z ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → y ≠ tmp → r.1.sc y = st.sc y) ∧ r.2 ≤ 2 * st.sc z + 3 := by
  intro r
  obtain ⟨a1, a2, a3, a4⟩ := addS_run z tmp c hzt htc hzc (st.setSc tmp (st.sc z))
  simp only [dbl, Cmd.run_seq, Cmd.run_copy, r]
  simp only [St.setSc_sc, Function.update_self, Function.update_of_ne hzt] at a1 a4
  refine ⟨by omega, by simpa using a2, ?_, by omega⟩
  intro y h1 h2 h3
  rw [a3 y h1 h2]; simp [St.setSc, Function.update_apply, h3]

/-! ### the zero-padded copy -/

/-- `dst[c+1] := if c < sc wS then bit src[c+1] else 0`, for `c < sc nS` -/
def padBody (dst src wS : ℕ) : Cmd :=
  .ifLt 818 wS (.seq (.rd 819 src 818 1) (.seq (.ifZero 819 .skip (.setK 819 1)) (.wr dst 818 1 819)))
    (.seq (.setK 819 0) (.wr dst 818 1 819))

def padCopy (dst src nS wS : ℕ) : Cmd := .loop nS 818 (padBody dst src wS)

def ZP2 (y : ℕ) : Prop := y = 818 ∨ y = 819

theorem padBody_step (dst src wS : ℕ) (t : St) (j w : ℕ) (hwt : t.sc wS = w) (hwS : wS ≠ 818 ∧ wS ≠ 819) :
    (Cmd.run (padBody dst src wS) (t.setSc 818 j)).1.ar =
      Function.update t.ar dst (Function.update (t.ar dst) (j + 1) (if j < w then bt (t.ar src) (j + 1) else 0)) ∧
    (∀ y, ¬ ZP2 y → (Cmd.run (padBody dst src wS) (t.setSc 818 j)).1.sc y = t.sc y) ∧
    (Cmd.run (padBody dst src wS) (t.setSc 818 j)).2 ≤ 8 := by
  have e818 : (t.setSc 818 j).sc 818 = j := by simp [St.setSc]
  have ew : (t.setSc 818 j).sc wS = w := by simp [St.setSc, Function.update_apply, hwS.1, hwt]
  by_cases hjw : j < w
  · have hlt : (t.setSc 818 j).sc 818 < (t.setSc 818 j).sc wS := by rw [e818, ew]; exact hjw
    by_cases a : t.ar src (j + 1) = 0
    · simp only [padBody, Cmd.run_ifLt, if_pos hlt, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_wr]
      have : (t.setSc 818 j).ar src (j + 1) = 0 := a
      simp only [St.setSc_sc, St.setSc_ar, Function.update_self, this, if_true, St.setAr, St.putAr]
      refine ⟨?_, ?_, by omega⟩
      · simp [bt, a, hjw]
      · intro y hy; simp only [ZP2, not_or] at hy; simp [St.setSc, Function.update_apply, hy.1, hy.2]
    · simp only [padBody, Cmd.run_ifLt, if_pos hlt, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_wr]
      have : (t.setSc 818 j).ar src (j + 1) = t.ar src (j + 1) := rfl
      simp only [St.setSc_sc, St.setSc_ar, Function.update_self, this, a, if_false, St.setAr, St.putAr]
      refine ⟨?_, ?_, by omega⟩
      · simp [bt, a, hjw]
      · intro y hy; simp only [ZP2, not_or] at hy; simp [St.setSc, Function.update_apply, hy.1, hy.2]
  · have hlt : ¬ (t.setSc 818 j).sc 818 < (t.setSc 818 j).sc wS := by rw [e818, ew]; exact hjw
    simp only [padBody, Cmd.run_ifLt, if_neg hlt, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]
    simp only [St.setSc_sc, St.setSc_ar, Function.update_self, St.setAr, St.putAr]
    refine ⟨?_, ?_, by omega⟩
    · simp [hjw]
    · intro y hy; simp only [ZP2, not_or] at hy; simp [St.setSc, Function.update_apply, hy.1, hy.2]

theorem padCopy_run (dst src nS wS : ℕ) (hds : dst ≠ src) (st : St) (n w : ℕ) (hn : st.sc nS = n) (hw : st.sc wS = w)
    (hwS : wS ≠ 818 ∧ wS ≠ 819) :
    Cells n ((Cmd.run (padCopy dst src nS wS) st).1.ar dst) (st.ar dst) ∧
    (∀ i, 1 ≤ i → i ≤ n → (Cmd.run (padCopy dst src nS wS) st).1.ar dst i = if i ≤ w then bt (st.ar src) i else 0) ∧
    ArKeep dst st (Cmd.run (padCopy dst src nS wS) st).1 ∧ ScKeep ZP2 st (Cmd.run (padCopy dst src nS wS) st).1 ∧
    (Cmd.run (padCopy dst src nS wS) st).2 ≤ n * 9 + 1 := by
  have key := mapLoop (b := nS) (c := 818) (body := padBody dst src wS) dst (fun j => if j < w then bt (st.ar src) (j + 1) else 0)
    ZP2 8 st n hn (by unfold ZP2; omega) (fun j => by split_ifs; exact bt_le _ _; omega) (by
      intro t j hj h3 h4
      have hs : t.ar src = st.ar src := h3 src (Ne.symm hds)
      have hwt : t.sc wS = w := by rw [h4 wS (by unfold ZP2; omega)]; exact hw
      have := padBody_step dst src wS t j w hwt hwS
      rw [hs] at this
      exact this)
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  refine ⟨k1, ?_, k3, k4, by unfold padCopy; omega⟩
  intro i h1 h2
  have := k2 i h1 h2
  beta_reduce at this
  simp only [show i - 1 + 1 = i by omega] at this
  show ((Cmd.loop nS 818 (padBody dst src wS)).run st).1.ar dst i = _
  rw [this]
  by_cases h : i - 1 < w
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

end ECDLP.L80
