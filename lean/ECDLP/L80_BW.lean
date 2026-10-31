import ECDLP.L80_Gen
import ECDLP.L72_Init

/-!
# L80 / BW: the pinned-constant width `bW = bP L * DP L` (`L = size p`) computed by loops
`Dcmd` : `t = (log2 L + 2)/4`, `D = 2^(2 (t-1) + 1) = DP L` (scalars 832, 833).  `Qcmd` : `bW = (2L+3)/D*D + D` (scalar 836).
Scratch scalars `831 .. 841`; the input `L` is in scalar 810 (kept).
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L59

def dblN (z tmp c : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (dblN z tmp c k) (dbl z tmp c)

theorem dblN_run (z tmp c : ℕ) (hzt : z ≠ tmp) (htc : tmp ≠ c) (hzc : z ≠ c) (k : ℕ) (st : St) :
    let r := Cmd.run (dblN z tmp c k) st
    r.1.sc z = 2 ^ k * st.sc z ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → y ≠ tmp → r.1.sc y = st.sc y) ∧
    r.2 ≤ 2 * 2 ^ k * st.sc z + 4 * k + 1 := by
  induction k with
  | zero => simp [dblN, Cmd.run_skip]
  | succ k ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    obtain ⟨d1, d2, d3, d4⟩ := dbl_run z tmp c hzt htc hzc (Cmd.run (dblN z tmp c k) st).1
    simp only [dblN, Cmd.run_seq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [d1, i1, pow_succ]; ring
    · rw [d2, i2]
    · intro y h1 h2 h3; rw [d3 y h1 h2 h3, i3 y h1 h2 h3]
    · rw [i1] at d4
      have : 2 * 2 ^ (k + 1) * st.sc z = 4 * (2 ^ k * st.sc z) := by ring
      nlinarith [i4, d4]

def Dstep : Cmd := .ifLt 810 831 .skip (.seq (.ifZero 832 .skip (dblN 833 839 838 2)) (.seq (.incr 832) (dblN 831 839 838 4)))

def Dcmd : Cmd := .seq (.setK 831 4) (.seq (.setK 832 0) (.seq (.setK 833 2) (.loop 810 837 Dstep)))

def ZBW (y : ℕ) : Prop := 831 ≤ y ∧ y ≤ 841

theorem T_iff (L t : ℕ) (hL : 1 ≤ L) : 4 * 16 ^ t ≤ L ↔ t < (Nat.log 2 L + 2) / 4 := by
  have : 4 * 16 ^ t = 2 ^ (4 * t + 2) := by rw [pow_add, pow_mul]; norm_num; ring
  rw [this, ← Nat.le_log_iff_pow_le (by norm_num) (by omega)]
  omega

theorem Dstep_run (s0 : St) (L T : ℕ) (hL : s0.sc 810 = L) (hT : ∀ t, 4 * 16 ^ t ≤ L ↔ t < T)
    (hpw : s0.sc 831 = 4 * 16 ^ (s0.sc 832)) :
    let r := Cmd.run Dstep s0
    (s0.sc 832 < T → r.1.sc 832 = s0.sc 832 + 1 ∧ r.1.sc 831 = 16 * s0.sc 831 ∧
      r.1.sc 833 = (if s0.sc 832 = 0 then s0.sc 833 else 4 * s0.sc 833)) ∧
    (¬ s0.sc 832 < T → r.1.sc 832 = s0.sc 832 ∧ r.1.sc 831 = s0.sc 831 ∧ r.1.sc 833 = s0.sc 833) ∧
    r.1.ar = s0.ar ∧ (∀ y, ¬ ZBW y → r.1.sc y = s0.sc y) ∧ r.2 ≤ 32 * s0.sc 831 + 8 * s0.sc 833 + 60 := by
  intro r
  have hiff := hT (s0.sc 832)
  rw [← hpw] at hiff
  by_cases hc : s0.sc 832 < T
  · have hle : s0.sc 831 ≤ L := hiff.2 hc
    have hn : ¬ s0.sc 810 < s0.sc 831 := by omega
    have hr1 : r.1 = (Cmd.run (.seq (.ifZero 832 .skip (dblN 833 839 838 2)) (.seq (.incr 832) (dblN 831 839 838 4))) s0).1 := by
      simp only [r, Dstep, Cmd.run_ifLt, if_neg hn]
    have hr2 : r.2 = (Cmd.run (.seq (.ifZero 832 .skip (dblN 833 839 838 2)) (.seq (.incr 832) (dblN 831 839 838 4))) s0).2 + 1 := by
      simp only [r, Dstep, Cmd.run_ifLt, if_neg hn]
    rw [hr1, hr2]
    simp only [Cmd.run_seq]
    obtain ⟨sA, A1, A2, A3, A4, A5, A6, A7⟩ : ∃ sA : St × ℕ, sA = Cmd.run (.ifZero 832 .skip (dblN 833 839 838 2)) s0 ∧
        sA.1.sc 832 = s0.sc 832 ∧ sA.1.sc 831 = s0.sc 831 ∧ sA.1.sc 833 = (if s0.sc 832 = 0 then s0.sc 833 else 4 * s0.sc 833) ∧
        sA.1.ar = s0.ar ∧ (∀ y, ¬ ZBW y → sA.1.sc y = s0.sc y) ∧ sA.2 ≤ 8 * s0.sc 833 + 12 := by
      by_cases h0 : s0.sc 832 = 0
      · refine ⟨_, rfl, ?_⟩
        simp only [Cmd.run_ifZero, h0, if_true, Cmd.run_skip]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega | (intro _ _; rfl) | simp [h0]
      · refine ⟨_, rfl, ?_⟩
        simp only [Cmd.run_ifZero, h0, if_false]
        obtain ⟨a1, a2, a3, a4⟩ := dblN_run 833 839 838 (by norm_num) (by norm_num) (by norm_num) 2 s0
        refine ⟨?_, ?_, ?_, a2, ?_, ?_⟩
        · rw [a3 832 (by norm_num) (by norm_num) (by norm_num)]
        · rw [a3 831 (by norm_num) (by norm_num) (by norm_num)]
        · rw [a1]; simp [h0]
        · intro y hy; rw [a3 y (fun h => hy (by subst h; unfold ZBW; omega)) (fun h => hy (by subst h; unfold ZBW; omega))
            (fun h => hy (by subst h; unfold ZBW; omega))]
        · omega
    rw [← A1]
    -- stage B, C
    have hB : (Cmd.run (.incr 832) sA.1).1.sc 832 = s0.sc 832 + 1 := by simp [Cmd.run_incr, St.setSc, A2]
    obtain ⟨c1, c2, c3, c4⟩ := dblN_run 831 839 838 (by norm_num) (by norm_num) (by norm_num) 4 (Cmd.run (.incr 832) sA.1).1
    have hB831 : (Cmd.run (.incr 832) sA.1).1.sc 831 = s0.sc 831 := by simp [Cmd.run_incr, St.setSc, A3]
    have hB833 : (Cmd.run (.incr 832) sA.1).1.sc 833 = sA.1.sc 833 := by simp [Cmd.run_incr, St.setSc]
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd hc h, ?_, ?_, ?_⟩
    · rw [c3 832 (by norm_num) (by norm_num) (by norm_num), hB]
    · rw [c1, hB831]; norm_num
    · rw [c3 833 (by norm_num) (by norm_num) (by norm_num), hB833, A4]
    · rw [c2]; simp [Cmd.run_incr, St.setSc, A5]
    · intro y hy
      rw [c3 y (fun h => hy (by subst h; unfold ZBW; omega)) (fun h => hy (by subst h; unfold ZBW; omega))
        (fun h => hy (by subst h; unfold ZBW; omega))]
      simp [Cmd.run_incr, St.setSc, Function.update_apply]
      split_ifs with hh
      · exfalso; apply hy; subst hh; unfold ZBW; omega
      · exact A6 y hy
    · have hi : (Cmd.run (.incr 832) sA.1).2 = 1 := rfl
      rw [hB831] at c4
      rw [hi]
      omega
  · have hn : s0.sc 810 < s0.sc 831 := by
      by_contra h; exact hc (hiff.1 (by omega))
    have hr1 : r.1 = (Cmd.run .skip s0).1 := by simp only [r, Dstep, Cmd.run_ifLt, if_pos hn]
    have hr2 : r.2 = (Cmd.run .skip s0).2 + 1 := by simp only [r, Dstep, Cmd.run_ifLt, if_pos hn]
    rw [hr1, hr2]
    refine ⟨fun h => absurd h hc, fun _ => ⟨rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, by show 1 + 1 ≤ _; omega⟩

theorem pw_le (L T t : ℕ) (hL : 1 ≤ L) (hT : ∀ t, 4 * 16 ^ t ≤ L ↔ t < T) : 4 * 16 ^ (min t T) ≤ 16 * L := by
  rcases Nat.eq_zero_or_pos (min t T) with h | h
  · rw [h]; norm_num; omega
  · have h1 : min t T - 1 < T := by have := min_le_right t T; omega
    have := (hT (min t T - 1)).2 h1
    have e : 4 * 16 ^ (min t T) = 16 * (4 * 16 ^ (min t T - 1)) := by
      rw [show min t T = (min t T - 1) + 1 by omega, pow_succ]; simp; ring
    omega

theorem D_le (t : ℕ) : 2 ^ (2 * (t - 1) + 1) ≤ 4 * 16 ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · norm_num
  · have : 2 ^ (2 * (t - 1) + 1) ≤ 2 ^ (4 * t + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (2 * (t - 1) + 1) ≤ 2 ^ (4 * t + 2) := this
      _ = 4 * 16 ^ t := by rw [pow_add, pow_mul]; norm_num; ring

theorem Dcmd_run (st : St) (L : ℕ) (hL : st.sc 810 = L) (h2 : 2 ≤ L) :
    let T := (Nat.log 2 L + 2) / 4
    let r := Cmd.run Dcmd st
    r.1.sc 832 = T ∧ r.1.sc 833 = 2 ^ (2 * (T - 1) + 1) ∧ r.1.sc 831 = 4 * 16 ^ T ∧ r.1.sc 833 ≤ L ∧ r.1.sc 810 = L ∧
    r.1.ar = st.ar ∧ (∀ y, ¬ ZBW y → r.1.sc y = st.sc y) ∧ r.2 ≤ 700 * L * L + 100 * L + 20 := by
  intro T r
  have hT : ∀ t, 4 * 16 ^ t ≤ L ↔ t < T := fun t => T_iff L t (by omega)
  have hTL : T ≤ L := by
    have := Nat.log_le_self 2 L
    show (Nat.log 2 L + 2) / 4 ≤ L
    omega
  set st1 := ((st.setSc 831 4).setSc 832 0).setSc 833 2 with hst1
  let P : ℕ → St → Prop := fun j t => t.sc 810 = L ∧ t.sc 832 = min j T ∧ t.sc 831 = 4 * 16 ^ (min j T) ∧
    t.sc 833 = 2 ^ (2 * (min j T - 1) + 1) ∧ t.ar = st.ar ∧ (∀ y, ¬ ZBW y → t.sc y = st.sc y)
  have h0 : P 0 st1 := by
    refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
    · simp [hst1, St.setSc, hL]
    · simp [hst1, St.setSc]
    · simp [hst1, St.setSc]
    · simp [hst1, St.setSc]
    · intro y hy
      simp only [hst1, St.setSc_sc, Function.update_apply]
      split_ifs with a b c
      · exfalso; apply hy; subst a; unfold ZBW; omega
      · exfalso; apply hy; subst b; unfold ZBW; omega
      · exfalso; apply hy; subst c; unfold ZBW; omega
      · rfl
  have hs0 : ∀ j t, P j t → (t.setSc 837 j).sc 810 = L ∧ (t.setSc 837 j).sc 831 = t.sc 831 ∧ (t.setSc 837 j).sc 832 = t.sc 832 ∧
      (t.setSc 837 j).sc 833 = t.sc 833 := by
    intro j t hP
    have p1 := hP.1
    simp [St.setSc, p1]
  have hstep : ∀ j t, j < st1.sc 810 → P j t → P (j + 1) (Cmd.run Dstep (t.setSc 837 j)).1 := by
    intro j t _ hP
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
    obtain ⟨e810, e831, e832, e833⟩ := hs0 j t ⟨p1, p2, p3, p4, p5, p6⟩
    obtain ⟨d1, d2, d3, d4, d5⟩ := Dstep_run (t.setSc 837 j) L T e810 hT (by rw [e831, e832, p3, p2])
    simp only [e832, e831, e833] at d1 d2 d5
    have fr : ∀ y, ¬ ZBW y → (t.setSc 837 j).sc y = t.sc y := fun y hy => by
      simp only [St.setSc_sc, Function.update_apply]
      split_ifs with h
      · exfalso; apply hy; subst h; unfold ZBW; omega
      · rfl
    by_cases hj : j < T
    · have hmin : min j T = j := min_eq_left hj.le
      have hmin' : min (j + 1) T = j + 1 := min_eq_left hj
      rw [hmin] at p2 p3 p4
      obtain ⟨q1, q2, q3⟩ := d1 (by rw [p2]; exact hj)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [d4 810 (by unfold ZBW; omega)]; rw [fr 810 (by unfold ZBW; omega), p1]
      · rw [q1, p2, hmin']
      · rw [q2, p3, hmin', pow_succ]; ring
      · rw [q3, p2, p4, hmin']
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp
        · rw [if_neg (by omega)]
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rw [show 2 * j' + 1 = (2 * j' + 1) from rfl, show 2 * (j' + 1) + 1 = (2 * j' + 1) + 2 by ring, pow_add]; ring
      · rw [d3]; exact p5
      · intro y hy; rw [d4 y hy, fr y hy, p6 y hy]
    · have hmin : min j T = T := min_eq_right (by omega)
      have hmin' : min (j + 1) T = T := min_eq_right (by omega)
      rw [hmin] at p2 p3 p4
      obtain ⟨q1, q2, q3⟩ := d2 (by rw [p2]; omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [d4 810 (by unfold ZBW; omega)]; rw [fr 810 (by unfold ZBW; omega), p1]
      · rw [q1, p2, hmin']
      · rw [q2, p3, hmin']
      · rw [q3, p4, hmin']
      · rw [d3]; exact p5
      · intro y hy; rw [d4 y hy, fr y hy, p6 y hy]
  have hI := Cmd.loop_inv (b := 810) (c := 837) (body := Dstep) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 810) (c := 837) (body := Dstep) P (640 * L + 60) h0 hstep (by
    intro j t _ hP
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
    obtain ⟨e810, e831, e832, e833⟩ := hs0 j t ⟨p1, p2, p3, p4, p5, p6⟩
    obtain ⟨d1, d2, d3, d4, d5⟩ := Dstep_run (t.setSc 837 j) L T e810 hT (by rw [e831, e832, p3, p2])
    simp only [e831, e833] at d5
    have h1 := pw_le L T j (by omega) hT
    have h2 := D_le (min j T)
    omega)
  have hst1_810 : st1.sc 810 = L := by simp [hst1, St.setSc, hL]
  rw [hst1_810] at hI hC
  have hr : r = ((Cmd.run (.loop 810 837 Dstep) st1).1, 1 + (1 + (1 + (Cmd.run (.loop 810 837 Dstep) st1).2 + 1) + 1) + 1) := by
    simp only [r, Dcmd, Cmd.run_seq, Cmd.run_setK]
    rfl
  rw [hr]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
  have hmin : min L T = T := min_eq_right hTL
  rw [hmin] at i2 i3 i4
  have hD : 2 ^ (2 * (T - 1) + 1) ≤ L := by
    rcases Nat.lt_or_ge 1 T with h | h
    · have := (hT (T - 1)).2 (by omega)
      have := D_le (T - 1)
      calc 2 ^ (2 * (T - 1) + 1) ≤ 4 * 16 ^ (T - 1) := by
            calc 2 ^ (2 * (T - 1) + 1) ≤ 2 ^ (4 * (T - 1) + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ = 4 * 16 ^ (T - 1) := by rw [pow_add, pow_mul]; norm_num; ring
        _ ≤ L := (hT (T - 1)).2 (by omega)
    · have : 2 * (T - 1) + 1 = 1 := by omega
      rw [this]; omega
  refine ⟨i2, i4, i3, by rw [i4]; exact hD, i1, i5, i6, ?_⟩
  simp only
  nlinarith [hC]

/-- `z := z - (scalar x)` (truncated) -/
def subS (z x c : ℕ) : Cmd := .loop x c (.decr z)

theorem subS_run (z x c : ℕ) (hzx : z ≠ x) (hxc : x ≠ c) (hzc : z ≠ c) (st : St) :
    let r := Cmd.run (subS z x c) st
    r.1.sc z = st.sc z - st.sc x ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → r.1.sc y = st.sc y) ∧ r.2 ≤ 2 * st.sc x + 1 := by
  intro r
  let P : ℕ → St → Prop := fun j t => t.sc z = st.sc z - j ∧ t.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → t.sc y = st.sc y)
  have h0 : P 0 st := ⟨by simp, rfl, fun _ _ _ => rfl⟩
  have hstep : ∀ j t, j < st.sc x → P j t → P (j + 1) (Cmd.run (.decr z) (t.setSc c j)).1 := by
    intro j t _ ⟨p1, p2, p3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [Cmd.run_decr, St.setSc, Function.update_apply, hzc, p1]; omega
    · simp [Cmd.run_decr, St.setSc, p2]
    · intro y hy1 hy2; simp [Cmd.run_decr, St.setSc, Function.update_apply, hy1, hy2, p3 y hy1 hy2]
  have hI := Cmd.loop_inv (b := x) (c := c) (body := .decr z) P h0 hstep
  have hC := Cmd.loop_cost_le (b := x) (c := c) (body := .decr z) P 1 h0 hstep (fun _ _ _ _ => by simp [Cmd.run_decr])
  obtain ⟨i1, i2, i3⟩ := hI
  exact ⟨i1, i2, i3, by simp only [r, subS]; omega⟩

def Qstep : Cmd := .ifLt 835 833 .skip (.seq (subS 835 833 838) (addS 836 833 838))

def Qcmd : Cmd := .seq (.setK 834 3) (.seq (addS 834 810 840) (.seq (addS 834 810 840) (.seq (.copy 835 834)
  (.seq (.copy 836 833) (.loop 834 837 Qstep)))))

theorem Qstep_run (s0 : St) (D rem bw Bits : ℕ) (hD : s0.sc 833 = D) (hr : s0.sc 835 = rem) (hb : s0.sc 836 = bw) :
    let r := Cmd.run Qstep s0
    (¬ rem < D → r.1.sc 835 = rem - D ∧ r.1.sc 836 = bw + D) ∧ (rem < D → r.1.sc 835 = rem ∧ r.1.sc 836 = bw) ∧
    r.1.sc 833 = D ∧ r.1.sc 834 = s0.sc 834 ∧ r.1.ar = s0.ar ∧ (∀ y, ¬ ZBW y → r.1.sc y = s0.sc y) ∧ r.2 ≤ 4 * D + 8 := by
  intro r
  by_cases h : rem < D
  · have hc : s0.sc 835 < s0.sc 833 := by rw [hr, hD]; exact h
    have e1 : r.1 = s0 := by simp only [r, Qstep, Cmd.run_ifLt, if_pos hc, Cmd.run_skip]
    have e2 : r.2 = 2 := by simp only [r, Qstep, Cmd.run_ifLt, if_pos hc, Cmd.run_skip]
    rw [e1, e2]
    exact ⟨fun h' => absurd h h', fun _ => ⟨hr, hb⟩, hD, rfl, rfl, fun _ _ => rfl, by omega⟩
  · have hc : ¬ s0.sc 835 < s0.sc 833 := by rw [hr, hD]; exact h
    obtain ⟨a1, a2, a3, a4⟩ := subS_run 835 833 838 (by norm_num) (by norm_num) (by norm_num) s0
    obtain ⟨b1, b2, b3, b4⟩ := addS_run 836 833 838 (by norm_num) (by norm_num) (by norm_num) (Cmd.run (subS 835 833 838) s0).1
    have e1 : r.1 = (Cmd.run (addS 836 833 838) (Cmd.run (subS 835 833 838) s0).1).1 := by
      simp only [r, Qstep, Cmd.run_ifLt, if_neg hc, Cmd.run_seq]
    have e2 : r.2 = (Cmd.run (subS 835 833 838) s0).2 + (Cmd.run (addS 836 833 838) (Cmd.run (subS 835 833 838) s0).1).2 + 1 + 1 := by
      simp only [r, Qstep, Cmd.run_ifLt, if_neg hc, Cmd.run_seq]
    rw [e1, e2]
    have f833 : (Cmd.run (subS 835 833 838) s0).1.sc 833 = D := by rw [a3 833 (by norm_num) (by norm_num), hD]
    have f836 : (Cmd.run (subS 835 833 838) s0).1.sc 836 = bw := by rw [a3 836 (by norm_num) (by norm_num), hb]
    have f835 : (Cmd.run (subS 835 833 838) s0).1.sc 835 = rem - D := by rw [a1, hr, hD]
    rw [f833] at b4 b1
    rw [f836] at b1
    refine ⟨fun _ => ⟨?_, b1⟩, fun h' => absurd h' h, ?_, ?_, ?_, ?_, ?_⟩
    · rw [b3 835 (by norm_num) (by norm_num), f835]
    · rw [b3 833 (by norm_num) (by norm_num), f833]
    · rw [b3 834 (by norm_num) (by norm_num), a3 834 (by norm_num) (by norm_num)]
    · rw [b2, a2]
    · intro y hy
      rw [b3 y (fun h => hy (by subst h; unfold ZBW; omega)) (fun h => hy (by subst h; unfold ZBW; omega)),
        a3 y (fun h => hy (by subst h; unfold ZBW; omega)) (fun h => hy (by subst h; unfold ZBW; omega))]
    · rw [hD] at a4; omega

theorem Qcmd_run (st : St) (L D : ℕ) (hL : st.sc 810 = L) (hD : st.sc 833 = D) (hD1 : 1 ≤ D) :
    let r := Cmd.run Qcmd st
    r.1.sc 836 = ((2 * L + 3) / D + 1) * D ∧ r.1.sc 833 = D ∧ r.1.sc 810 = L ∧ r.1.ar = st.ar ∧
    (∀ y, ¬ ZBW y → r.1.sc y = st.sc y) ∧ r.2 ≤ 4 * D * (2 * L + 3) + 30 * L + 100 := by
  intro r
  set Bits := 2 * L + 3 with hBits
  set Q := Bits / D with hQ
  have hQB : Q ≤ Bits := Nat.div_le_self _ _
  -- setup
  obtain ⟨a1, a2, a3, a4⟩ := addS_run 834 810 840 (by norm_num) (by norm_num) (by norm_num) (st.setSc 834 3)
  have a1' : (Cmd.run (addS 834 810 840) (st.setSc 834 3)).1.sc 834 = 3 + L := by
    rw [a1]; simp [St.setSc, hL]
  obtain ⟨b1, b2, b3, b4⟩ := addS_run 834 810 840 (by norm_num) (by norm_num) (by norm_num) (Cmd.run (addS 834 810 840) (st.setSc 834 3)).1
  have b810 : (Cmd.run (addS 834 810 840) (st.setSc 834 3)).1.sc 810 = L := by
    rw [a3 810 (by norm_num) (by norm_num)]; simp [St.setSc, hL]
  rw [a1', b810] at b1
  rw [b810] at b4
  have a4' : ((addS 834 810 840).run (st.setSc 834 3)).2 ≤ 2 * L + 1 := by
    have := a4; simp only [St.setSc_sc, Function.update_of_ne (show (810 : ℕ) ≠ 834 by norm_num), hL] at this; exact this
  set s1 := (Cmd.run (addS 834 810 840) (Cmd.run (addS 834 810 840) (st.setSc 834 3)).1).1 with hs1
  have s1_834 : s1.sc 834 = Bits := by rw [hs1, b1]; omega
  have s1_833 : s1.sc 833 = D := by
    rw [hs1, b3 833 (by norm_num) (by norm_num), a3 833 (by norm_num) (by norm_num)]; simp [St.setSc, hD]
  have s1_810 : s1.sc 810 = L := by
    rw [hs1, b3 810 (by norm_num) (by norm_num), a3 810 (by norm_num) (by norm_num)]; simp [St.setSc, hL]
  have s1_ar : s1.ar = st.ar := by rw [hs1, b2, a2]; rfl
  have s1_fr : ∀ y, ¬ ZBW y → y ≠ 834 → y ≠ 840 → s1.sc y = st.sc y := by
    intro y hy h1 h2
    rw [hs1, b3 y h1 h2, a3 y h1 h2]; simp [St.setSc, h1]
  set s3 := ((s1.setSc 835 (s1.sc 834)).setSc 836 ((s1.setSc 835 (s1.sc 834)).sc 833)) with hs3
  have s3_834 : s3.sc 834 = Bits := by simp [hs3, St.setSc, s1_834]
  have s3_835 : s3.sc 835 = Bits := by simp [hs3, St.setSc, s1_834]
  have s3_836 : s3.sc 836 = D := by simp [hs3, St.setSc, s1_833]
  have s3_833 : s3.sc 833 = D := by simp [hs3, St.setSc, s1_833]
  have s3_810 : s3.sc 810 = L := by simp [hs3, St.setSc, s1_810]
  have s3_ar : s3.ar = st.ar := by rw [hs3]; exact s1_ar
  have s3_fr : ∀ y, ¬ ZBW y → s3.sc y = st.sc y := by
    intro y hy
    have h1 : y ≠ 835 := fun h => hy (by subst h; unfold ZBW; omega)
    have h2 : y ≠ 836 := fun h => hy (by subst h; unfold ZBW; omega)
    have h3 : y ≠ 834 := fun h => hy (by subst h; unfold ZBW; omega)
    have h4 : y ≠ 840 := fun h => hy (by subst h; unfold ZBW; omega)
    simp only [hs3, St.setSc_sc, Function.update_of_ne h1, Function.update_of_ne h2]
    exact s1_fr y hy h3 h4
  let P : ℕ → St → Prop := fun j t => t.sc 833 = D ∧ t.sc 810 = L ∧ t.sc 834 = Bits ∧ t.sc 835 = Bits - D * min j Q ∧
    t.sc 836 = D * (min j Q + 1) ∧ t.ar = st.ar ∧ (∀ y, ¬ ZBW y → t.sc y = st.sc y)
  have h0 : P 0 s3 := ⟨s3_833, s3_810, s3_834, by simp [s3_835], by simp [s3_836], s3_ar, s3_fr⟩
  have hfr : ∀ (t : St) (j : ℕ) (y : ℕ), ¬ ZBW y → (t.setSc 837 j).sc y = t.sc y := by
    intro t j y hy
    simp only [St.setSc_sc, Function.update_apply]
    split_ifs with h
    · exfalso; apply hy; subst h; unfold ZBW; omega
    · rfl
  have hstep : ∀ j t, j < s3.sc 834 → P j t → P (j + 1) (Cmd.run Qstep (t.setSc 837 j)).1 := by
    intro j t _ ⟨p1, p2, p3, p4, p5, p6, p7⟩
    have e833 : (t.setSc 837 j).sc 833 = D := by simp [St.setSc, p1]
    have e835 : (t.setSc 837 j).sc 835 = Bits - D * min j Q := by simp [St.setSc, p4]
    have e836 : (t.setSc 837 j).sc 836 = D * (min j Q + 1) := by simp [St.setSc, p5]
    obtain ⟨q1, q2, q3, q34, q4, q5, q6⟩ := Qstep_run (t.setSc 837 j) D _ _ Bits e833 e835 e836
    refine ⟨q3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [q5 810 (by unfold ZBW; omega), hfr t j 810 (by unfold ZBW; omega), p2]
    · rw [q34]; simp [St.setSc, p3]
    · by_cases hj : j < Q
      · have hm : min j Q = j := min_eq_left hj.le
        have hm' : min (j + 1) Q = j + 1 := min_eq_left hj
        have hle : D * (j + 1) ≤ Bits := le_trans (Nat.mul_le_mul_left D hj) (by rw [hQ]; exact Nat.mul_div_le _ _)
        rw [hm] at e835
        have hn : ¬ Bits - D * j < D := by rw [Nat.mul_succ] at hle; omega
        rw [(q1 (by rw [hm]; exact hn)).1, hm']
        rw [hm]; rw [Nat.mul_succ]; omega
      · have hm : min j Q = Q := min_eq_right (by omega)
        have hm' : min (j + 1) Q = Q := min_eq_right (by omega)
        rw [hm] at e835
        have hlt : Bits - D * Q < D := by
          have := Nat.div_add_mod Bits D
          have := Nat.mod_lt Bits (show 0 < D by omega)
          rw [hQ]; omega
        rw [(q2 (by rw [hm]; exact hlt)).1, hm', hm]
    · by_cases hj : j < Q
      · have hm : min j Q = j := min_eq_left hj.le
        have hm' : min (j + 1) Q = j + 1 := min_eq_left hj
        have hle : D * (j + 1) ≤ Bits := le_trans (Nat.mul_le_mul_left D hj) (by rw [hQ]; exact Nat.mul_div_le _ _)
        rw [hm] at e835 e836
        have hn : ¬ Bits - D * j < D := by rw [Nat.mul_succ] at hle; omega
        rw [(q1 (by rw [hm]; exact hn)).2, hm', hm]
        ring
      · have hm : min j Q = Q := min_eq_right (by omega)
        have hm' : min (j + 1) Q = Q := min_eq_right (by omega)
        rw [hm] at e835 e836
        have hlt : Bits - D * Q < D := by
          have := Nat.div_add_mod Bits D
          have := Nat.mod_lt Bits (show 0 < D by omega)
          rw [hQ]; omega
        rw [(q2 (by rw [hm]; exact hlt)).2, hm, hm']
    · rw [q4]; exact p6
    · intro y hy; rw [q5 y hy, hfr t j y hy, p7 y hy]
  have hI := Cmd.loop_inv (b := 834) (c := 837) (body := Qstep) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 834) (c := 837) (body := Qstep) P (4 * D + 8) h0 hstep (by
    intro j t _ ⟨p1, p2, p3, p4, p5, p6, p7⟩
    have e833 : (t.setSc 837 j).sc 833 = D := by simp [St.setSc, p1]
    have e835 : (t.setSc 837 j).sc 835 = Bits - D * min j Q := by simp [St.setSc, p4]
    have e836 : (t.setSc 837 j).sc 836 = D * (min j Q + 1) := by simp [St.setSc, p5]
    exact (Qstep_run (t.setSc 837 j) D _ _ Bits e833 e835 e836).2.2.2.2.2.2)
  rw [s3_834] at hI hC
  have hr1 : r.1 = (Cmd.run (.loop 834 837 Qstep) s3).1 := by
    simp only [r, Qcmd, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy]
    rfl
  have hr2 : r.2 = 1 + ((Cmd.run (addS 834 810 840) (st.setSc 834 3)).2 + ((Cmd.run (addS 834 810 840) (Cmd.run (addS 834 810 840) (st.setSc 834 3)).1).2 + (1 + (1 + (Cmd.run (.loop 834 837 Qstep) s3).2 + 1) + 1) + 1) + 1) + 1 := by
    simp only [r, Qcmd, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy]
    rfl
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  rw [hr1]
  have hmin : min Bits Q = Q := min_eq_right hQB
  rw [hmin] at i4 i5
  have hmod := Nat.div_add_mod Bits D
  have hmod' := Nat.mod_lt Bits (show 0 < D by omega)
  refine ⟨?_, i1, i2, i6, i7, ?_⟩
  · rw [i5]; ring
  · have e : Bits * (4 * D + 8 + 1) = 4 * D * Bits + 9 * Bits := by ring
    rw [hr2]
    rw [e] at hC
    omega

def Bcmd : Cmd := .seq Dcmd Qcmd

theorem Bcmd_run (st : St) (L : ℕ) (hL : st.sc 810 = L) (h2 : 2 ≤ L) :
    let r := Cmd.run Bcmd st
    r.1.sc 836 = ECDLP.L72.bWof L ∧ r.1.sc 810 = L ∧ r.1.ar = st.ar ∧ (∀ y, ¬ ZBW y → r.1.sc y = st.sc y) ∧
    r.2 ≤ 1000 * L * L + 200 * L + 200 := by
  intro r
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Dcmd_run st L hL h2
  have hD1 : 1 ≤ (Cmd.run Dcmd st).1.sc 833 := by
    rw [d2]; exact Nat.one_le_two_pow
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := Qcmd_run (Cmd.run Dcmd st).1 L _ d5 rfl hD1
  have hr : r = ((Cmd.run Qcmd (Cmd.run Dcmd st).1).1, (Cmd.run Dcmd st).2 + (Cmd.run Qcmd (Cmd.run Dcmd st).1).2 + 1) := by
    simp only [r, Bcmd, Cmd.run_seq]
  rw [hr]
  refine ⟨?_, q3, by rw [q4, d6], ?_, ?_⟩
  · simp only
    rw [q1, d2]
    rfl
  · intro y hy; simp only; rw [q5 y hy, d7 y hy]
  · simp only
    have hDL : (Cmd.run Dcmd st).1.sc 833 ≤ L := d4
    have : 4 * (Cmd.run Dcmd st).1.sc 833 * (2 * L + 3) ≤ 4 * L * (2 * L + 3) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hDL)
    nlinarith [d8, q6, this]

end ECDLP.L80
