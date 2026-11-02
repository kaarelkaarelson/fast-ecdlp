import ECDLP.L76_Ops

/-!
# L113 / Scalar: wrap-around increments and modular scalar arithmetic by loops
`incW x j` : `x := (x+1) mod j` (for `x < j`).  `addW x t j c` : `x := (x + t) mod j`, `t` copies of `incW` (loop counter `c`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

def incW (x j : ℕ) : Cmd := .seq (.incr x) (.ifLt x j .skip (.setK x 0))

theorem incW_run (x j : ℕ) (hxj : x ≠ j) (s : St) (h : s.sc x < s.sc j) :
    (Cmd.run (incW x j) s).1.sc x = (s.sc x + 1) % s.sc j ∧
    (∀ y, y ≠ x → (Cmd.run (incW x j) s).1.sc y = s.sc y) ∧
    (Cmd.run (incW x j) s).1.ar = s.ar ∧ (Cmd.run (incW x j) s).2 ≤ 5 := by
  have hjx : j ≠ x := fun e => hxj e.symm
  have e1 : (s.setSc x (s.sc x + 1)).sc x = s.sc x + 1 := by simp [St.setSc]
  have e2 : (s.setSc x (s.sc x + 1)).sc j = s.sc j := by simp [St.setSc, Function.update_of_ne hjx]
  simp only [incW, Cmd.run_seq, Cmd.run_incr, Cmd.run_ifLt, e1, e2]
  by_cases h1 : s.sc x + 1 < s.sc j
  · rw [if_pos h1, Cmd.run_skip, Nat.mod_eq_of_lt h1]
    refine ⟨by simp [St.setSc], fun y hy => by simp [St.setSc, Function.update_of_ne hy], rfl, by omega⟩
  · rw [if_neg h1, Cmd.run_setK]
    have : s.sc x + 1 = s.sc j := by omega
    refine ⟨?_, fun y hy => ?_, rfl, by omega⟩
    · rw [this, Nat.mod_self]; simp [St.setSc]
    · simp [St.setSc, Function.update_of_ne hy]


/-- `x := (x + t) mod j` : `t` wrap-around increments, loop counter `c` -/
def addW (x t j c : ℕ) : Cmd := .loop t c (incW x j)

theorem addW_run (x t j c : ℕ) (hxj : x ≠ j) (hxc : x ≠ c) (hjc : j ≠ c) (s : St) (h : s.sc x < s.sc j) :
    (Cmd.run (addW x t j c) s).1.sc x = (s.sc x + s.sc t) % s.sc j ∧
    (∀ y, y ≠ x → y ≠ c → (Cmd.run (addW x t j c) s).1.sc y = s.sc y) ∧
    (Cmd.run (addW x t j c) s).1.ar = s.ar ∧ (Cmd.run (addW x t j c) s).2 ≤ s.sc t * 6 + 1 := by
  have hm : 0 < s.sc j := by omega
  let P : ℕ → St → Prop := fun i t' => t'.sc x = (s.sc x + i) % s.sc j ∧
    (∀ y, y ≠ x → y ≠ c → t'.sc y = s.sc y) ∧ t'.ar = s.ar
  have h0 : P 0 s := ⟨by simp [Nat.mod_eq_of_lt h], fun _ _ _ => rfl, rfl⟩
  have step : ∀ i t', P i t' → P (i + 1) (Cmd.run (incW x j) (t'.setSc c i)).1 ∧
      (Cmd.run (incW x j) (t'.setSc c i)).2 ≤ 5 := by
    intro i t' ⟨p1, p2, p3⟩
    have q1 : (t'.setSc c i).sc x = (s.sc x + i) % s.sc j := by simp [St.setSc, Function.update_of_ne hxc, p1]
    have q2 : (t'.setSc c i).sc j = s.sc j := by simp [St.setSc, Function.update_of_ne hjc, p2 j (Ne.symm hxj) hjc]
    obtain ⟨r1, r2, r3, r4⟩ := incW_run x j hxj (t'.setSc c i) (by rw [q1, q2]; exact Nat.mod_lt _ hm)
    refine ⟨⟨?_, fun y hy hyc => ?_, ?_⟩, r4⟩
    · rw [r1, q1, q2, Nat.mod_add_mod]; congr 1
    · rw [r2 y hy]; simp [St.setSc, Function.update_of_ne hyc, p2 y hy hyc]
    · rw [r3]; simpa [St.setSc] using p3
  have hI := Cmd.loop_inv (b := t) (c := c) (body := incW x j) (st := s) P h0 (fun i t' _ hp => (step i t' hp).1)
  have hC := Cmd.loop_cost_le (b := t) (c := c) (body := incW x j) (st := s) P 5 h0 (fun i t' _ hp => (step i t' hp).1)
    (fun i t' _ hp => (step i t' hp).2)
  obtain ⟨a1, a2, a3⟩ := hI
  refine ⟨a1, a2, a3, ?_⟩
  simp only [addW]; omega


/-! ### the residue of a bignum modulo a small scalar (LSB first Horner) -/

/-- one turn: `bit := A[ci+1]`; `acc += [bit≠0] * pw (mod j)`; `pw := 2 pw (mod j)`.  `j` is in scalar 802. -/
def modBigBody (A : ℕ) : Cmd :=
  .seq (.rd 813 A 814 1)
   (.seq (.ifZero 813 .skip (addW 811 812 802 816))
    (.seq (.copy 815 812) (addW 812 815 802 816)))

theorem modBigBody_step (A : ℕ) (s : St) (i j : ℕ) (hj : s.sc 802 = j) (ha : s.sc 811 < j) (hp : s.sc 812 < j) :
    (Cmd.run (modBigBody A) (s.setSc 814 i)).1.sc 811 = (s.sc 811 + bt (s.ar A) (i + 1) * s.sc 812) % j ∧
    (Cmd.run (modBigBody A) (s.setSc 814 i)).1.sc 812 = (2 * s.sc 812) % j ∧
    (∀ y, (y < 811 ∨ 816 < y) → (Cmd.run (modBigBody A) (s.setSc 814 i)).1.sc y = s.sc y) ∧
    (Cmd.run (modBigBody A) (s.setSc 814 i)).1.ar = s.ar ∧
    (Cmd.run (modBigBody A) (s.setSc 814 i)).2 ≤ 12 * j + 10 := by
  have hj0 : 0 < j := by omega
  set s0 := s.setSc 814 i with hs0
  have f0 : ∀ y, y ≠ 814 → s0.sc y = s.sc y := fun y hy => by simp [hs0, St.setSc, Function.update_of_ne hy]
  set s1 := (Cmd.run (.rd 813 A 814 1) s0).1 with hs1
  have c1 : s1.sc 813 = s.ar A (i + 1) := by simp [hs1, Cmd.run_rd, St.setSc, hs0]
  have f1 : ∀ y, y ≠ 813 → s1.sc y = s0.sc y := fun y hy => by simp [hs1, Cmd.run_rd, St.setSc, Function.update_of_ne hy]
  have a1 : s1.ar = s.ar := by simp [hs1, Cmd.run_rd, St.setSc, hs0]
  have j1 : s1.sc 802 = j := by rw [f1 _ (by norm_num), f0 _ (by norm_num), hj]
  have v11 : s1.sc 811 = s.sc 811 := by rw [f1 _ (by norm_num), f0 _ (by norm_num)]
  have v12 : s1.sc 812 = s.sc 812 := by rw [f1 _ (by norm_num), f0 _ (by norm_num)]
  -- second step
  set s2 := (Cmd.run (.ifZero 813 .skip (addW 811 812 802 816)) s1).1 with hs2
  have key2 : s2.sc 811 = (s.sc 811 + bt (s.ar A) (i + 1) * s.sc 812) % j ∧ s2.sc 812 = s.sc 812 ∧
      (∀ y, y ≠ 811 → y ≠ 816 → s2.sc y = s1.sc y) ∧ s2.ar = s.ar ∧
      (Cmd.run (.ifZero 813 .skip (addW 811 812 802 816)) s1).2 ≤ 6 * j + 3 := by
    by_cases hz : s.ar A (i + 1) = 0
    · have : s1.sc 813 = 0 := by rw [c1, hz]
      simp only [hs2, Cmd.run_ifZero, this, if_true, Cmd.run_skip]
      refine ⟨?_, v12, fun _ _ _ => trivial, a1, by omega⟩
      simp [bt, hz, v11, Nat.mod_eq_of_lt ha]
    · have : s1.sc 813 ≠ 0 := by rw [c1]; exact hz
      simp only [hs2, Cmd.run_ifZero, this, if_false]
      obtain ⟨r1, r2, r3, r4⟩ := addW_run 811 812 802 816 (by norm_num) (by norm_num) (by norm_num) s1 (by rw [j1, v11]; exact ha)
      refine ⟨?_, ?_, fun y h1 h2 => r2 y h1 h2, by rw [r3, a1], ?_⟩
      · rw [r1, j1, v11, v12]; simp [bt, hz]
      · rw [r2 812 (by norm_num) (by norm_num)]; exact v12
      · have : s1.sc 812 ≤ j := by rw [v12]; omega
        omega
  obtain ⟨k1, k2, k3, k4, k5⟩ := key2
  -- third / fourth step
  set s3 := (Cmd.run (.copy 815 812) s2).1 with hs3
  have c3 : s3.sc 815 = s.sc 812 := by simp [hs3, Cmd.run_copy, St.setSc, k2]
  have f3 : ∀ y, y ≠ 815 → s3.sc y = s2.sc y := fun y hy => by simp [hs3, Cmd.run_copy, St.setSc, Function.update_of_ne hy]
  have a3 : s3.ar = s.ar := by simp [hs3, Cmd.run_copy, St.setSc, k4]
  have j3 : s3.sc 802 = j := by rw [f3 _ (by norm_num), k3 _ (by norm_num) (by norm_num), j1]
  have v3 : s3.sc 812 = s.sc 812 := by rw [f3 _ (by norm_num), k2]
  obtain ⟨r1, r2, r3, r4⟩ := addW_run 812 815 802 816 (by norm_num) (by norm_num) (by norm_num) s3 (by rw [j3, v3]; exact hp)
  have hrun : (Cmd.run (modBigBody A) s0).1 = (Cmd.run (addW 812 815 802 816) s3).1 := by
    simp only [modBigBody, Cmd.run_seq]; rfl
  have hcost : (Cmd.run (modBigBody A) s0).2 = 1 + ((Cmd.run (.ifZero 813 .skip (addW 811 812 802 816)) s1).2 +
      (1 + (Cmd.run (addW 812 815 802 816) s3).2 + 1) + 1) + 1 := by
    simp only [modBigBody, Cmd.run_seq]; rfl
  have e3 : s3.sc 815 = s.sc 812 := c3
  rw [hrun, hcost]
  refine ⟨?_, ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [r2 811 (by norm_num) (by norm_num), f3 _ (by norm_num)]; exact k1
  · rw [r1, j3, e3, v3]; simp [Nat.two_mul]
  · have hy1 : y ≠ 812 := by omega
    have hy2 : y ≠ 816 := by omega
    rw [r2 y hy1 hy2, f3 y (by omega), k3 y (by omega) hy2, f1 y (by omega), f0 y (by omega)]
  · rw [r3, a3]
  · have : s3.sc 815 ≤ j := by rw [e3]; omega
    omega


/-- `scalar 811 := V(A, W) mod j` (`j ≥ 2` in scalar 802), W = scalar 710 -/
def modBig (A : ℕ) : Cmd := .seq (.setK 811 0) (.seq (.setK 812 1) (.loop 710 814 (modBigBody A)))

theorem modBig_run (A : ℕ) (st : St) (n j : ℕ) (hW : st.sc 710 = n) (hj : st.sc 802 = j) (h2 : 2 ≤ j) :
    (Cmd.run (modBig A) st).1.sc 811 = V (st.ar A) n % j ∧
    (∀ y, (y < 811 ∨ 816 < y) → (Cmd.run (modBig A) st).1.sc y = st.sc y) ∧
    (Cmd.run (modBig A) st).1.ar = st.ar ∧ (Cmd.run (modBig A) st).2 ≤ n * (12 * j + 11) + 5 := by
  set st1 := (st.setSc 811 0).setSc 812 1 with hst1
  have e710 : st1.sc 710 = n := by simp [hst1, St.setSc, hW]
  have e802 : st1.sc 802 = j := by simp [hst1, St.setSc, hj]
  let P : ℕ → St → Prop := fun i t => t.sc 811 = V (st.ar A) i % j ∧ t.sc 812 = 2 ^ i % j ∧
    (∀ y, (y < 811 ∨ 816 < y) → t.sc y = st.sc y) ∧ t.ar = st.ar
  have h0 : P 0 st1 := by
    refine ⟨by simp [hst1, St.setSc, V, numCells], by simp [hst1, St.setSc, Nat.mod_eq_of_lt (by omega : 1 < j)], fun y hy => ?_, rfl⟩
    have h1 : y ≠ 811 := by omega
    have h2 : y ≠ 812 := by omega
    simp [hst1, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2]
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (modBigBody A) (t.setSc 814 i)).1 ∧
      (Cmd.run (modBigBody A) (t.setSc 814 i)).2 ≤ 12 * j + 10 := by
    intro i t ⟨p1, p2, p3, p4⟩
    have tj : t.sc 802 = j := by rw [p3 802 (by omega), hj]
    obtain ⟨r1, r2, r3, r4, r5⟩ := modBigBody_step A t i j tj (by rw [p1]; exact Nat.mod_lt _ (by omega))
      (by rw [p2]; exact Nat.mod_lt _ (by omega))
    refine ⟨⟨?_, ?_, fun y hy => ?_, ?_⟩, r5⟩
    · rw [r1, p1, p4, V_snoc, p2]
      have hb := bt_le (st.ar A) (i + 1)
      rcases (by omega : bt (st.ar A) (i + 1) = 0 ∨ bt (st.ar A) (i + 1) = 1) with h | h <;> simp [h, Nat.add_mod]
    · rw [r2, p2, pow_succ]; rw [Nat.mul_mod, Nat.mod_mod]; simp [Nat.mul_comm, Nat.mul_mod]
    · rw [r3 y hy, p3 y hy]
    · rw [r4, p4]
  have hI := Cmd.loop_inv (b := 710) (c := 814) (body := modBigBody A) (st := st1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 710) (c := 814) (body := modBigBody A) (st := st1) P (12 * j + 10) h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  rw [e710] at hI hC
  have hr : Cmd.run (modBig A) st = ((Cmd.run (.loop 710 814 (modBigBody A)) st1).1,
      1 + (1 + (Cmd.run (.loop 710 814 (modBigBody A)) st1).2 + 1) + 1) := by
    simp [modBig, Cmd.run_seq, Cmd.run_setK, hst1]
  rw [hr]
  obtain ⟨a1, a2, a3, a4⟩ := hI
  refine ⟨a1, a3, a4, ?_⟩
  simp only
  nlinarith [hC]


/-! ### the least solution of `(x0 + k * pm) mod j = R` -/

/-- the scan body.  acc = scalar 817, counter = 818, found flag = 819, counter of `addW` = 820 -/
def findBody (pm rR out : ℕ) : Cmd :=
  .seq (.ifZero 819 (.ifLt 817 rR .skip (.ifLt rR 817 .skip (.seq (.copy out 818) (.setK 819 1)))) .skip)
    (addW 817 pm 802 820)

/-- `out := least k < j with (x0 + k * pm) mod j = R` (`0` if none); `j` in scalar 802. -/
def findC (x0 pm rR out : ℕ) : Cmd :=
  .seq (.copy 817 x0) (.seq (.setK 819 0) (.seq (.setK out 0) (.loop 802 818 (findBody pm rR out))))

def QQ (x0 pm j k : ℕ) : ℕ := (x0 + k * pm) % j

theorem QQ_succ (x0 pm j k : ℕ) : QQ x0 pm j (k + 1) = (QQ x0 pm j k + pm) % j := by
  unfold QQ; rw [Nat.mod_add_mod]; congr 1; ring

theorem findBody_step (pm rR out : ℕ) (hpm : pm ≠ 817 ∧ pm ≠ 818 ∧ pm ≠ 819 ∧ pm ≠ 820 ∧ pm ≠ 802 ∧ pm ≠ out)
    (hout : out ≠ 817 ∧ out ≠ 818 ∧ out ≠ 819 ∧ out ≠ 820 ∧ out ≠ 802)
    (hR : rR ≠ 817 ∧ rR ≠ 818 ∧ rR ≠ 819 ∧ rR ≠ 820 ∧ rR ≠ out)
    (t : St) (k j x0v : ℕ) (hj : t.sc 802 = j) (hpl : t.sc pm < j) (hRl : t.sc rR < j) (hacc : t.sc 817 < j) (hf : t.sc 819 ≤ 1) :
    let r := Cmd.run (findBody pm rR out) (t.setSc 818 k)
    r.1.sc 817 = (t.sc 817 + t.sc pm) % j ∧
    (t.sc 819 = 0 → t.sc 817 = t.sc rR → r.1.sc 819 = 1 ∧ r.1.sc out = k) ∧
    (t.sc 819 = 0 → t.sc 817 ≠ t.sc rR → r.1.sc 819 = 0 ∧ r.1.sc out = t.sc out) ∧
    (t.sc 819 ≠ 0 → r.1.sc 819 = t.sc 819 ∧ r.1.sc out = t.sc out) ∧
    (∀ y, y ≠ 817 → y ≠ 818 → y ≠ 819 → y ≠ 820 → y ≠ out → r.1.sc y = t.sc y) ∧
    r.1.ar = t.ar ∧ r.2 ≤ 6 * j + 8 := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpm
  obtain ⟨o1, o2, o3, o4, o5⟩ := hout
  obtain ⟨q1, q2, q3, q4, q5⟩ := hR
  set s0 := t.setSc 818 k with hs0
  have f0 : ∀ y, y ≠ 818 → s0.sc y = t.sc y := fun y hy => by simp [hs0, St.setSc, Function.update_of_ne hy]
  have c0 : s0.sc 818 = k := by simp [hs0, St.setSc]
  set s1 := (Cmd.run (.ifZero 819 (.ifLt 817 rR .skip (.ifLt rR 817 .skip (.seq (.copy out 818) (.setK 819 1)))) .skip) s0).1 with hs1
  have key : (t.sc 819 = 0 → t.sc 817 = t.sc rR → s1.sc 819 = 1 ∧ s1.sc out = k) ∧
      (t.sc 819 = 0 → t.sc 817 ≠ t.sc rR → s1.sc 819 = 0 ∧ s1.sc out = t.sc out) ∧
      (t.sc 819 ≠ 0 → s1.sc 819 = t.sc 819 ∧ s1.sc out = t.sc out) ∧
      (∀ y, y ≠ 819 → y ≠ out → s1.sc y = s0.sc y) ∧ s1.ar = t.ar ∧
      (Cmd.run (.ifZero 819 (.ifLt 817 rR .skip (.ifLt rR 817 .skip (.seq (.copy out 818) (.setK 819 1)))) .skip) s0).2 ≤ 6 := by
    have g817 : s0.sc 817 = t.sc 817 := f0 _ (by norm_num)
    have g819 : s0.sc 819 = t.sc 819 := f0 _ (by norm_num)
    have gR : s0.sc rR = t.sc rR := f0 _ q2
    have gout : s0.sc out = t.sc out := f0 _ o2
    by_cases hz : t.sc 819 = 0
    · have e1 : s0.sc 819 = 0 := by rw [g819, hz]
      simp only [hs1, Cmd.run_ifZero, e1, if_true, Cmd.run_ifLt, g817, gR]
      by_cases a1 : t.sc 817 < t.sc rR
      · simp only [a1, if_true, Cmd.run_skip]
        refine ⟨fun _ h => by omega, fun _ _ => ⟨?_, ?_⟩, fun h => absurd hz h, fun _ _ _ => trivial, rfl, by omega⟩
        · rw [g819, hz]
        · rw [gout]
      · by_cases a2 : t.sc rR < t.sc 817
        · simp only [a1, a2, if_false, if_true, Cmd.run_skip]
          refine ⟨fun _ h => by omega, fun _ _ => ⟨?_, ?_⟩, fun h => absurd hz h, fun _ _ _ => trivial, rfl, by omega⟩
          · rw [g819, hz]
          · rw [gout]
        · have heq : t.sc 817 = t.sc rR := by omega
          simp only [a1, a2, if_false, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK]
          refine ⟨fun _ _ => ⟨?_, ?_⟩, fun _ h => absurd heq h, fun h => absurd hz h, fun y h1 h2 => ?_, ?_, by omega⟩
          · simp [St.setSc]
          · simp [St.setSc, Function.update_of_ne o3, c0, Function.update_of_ne o2]
          · simp [St.setSc, Function.update_of_ne h1, Function.update_of_ne h2]
          · simp [St.setSc, hs0]
    · have e1 : s0.sc 819 ≠ 0 := by rw [g819]; exact hz
      simp only [hs1, Cmd.run_ifZero, e1, if_false, Cmd.run_skip]
      refine ⟨fun h => absurd h hz, fun h => absurd h hz, fun _ => ⟨g819, gout⟩, fun _ _ _ => trivial, rfl, by omega⟩
  obtain ⟨K1, K2, K3, K4, K5, K6⟩ := key
  have j1 : s1.sc 802 = j := by rw [K4 _ (by norm_num) (by omega), f0 _ (by norm_num), hj]
  have a1 : s1.sc 817 = t.sc 817 := by rw [K4 _ (by norm_num) (by omega), f0 _ (by norm_num)]
  have pm1 : s1.sc pm = t.sc pm := by rw [K4 _ p3 p6, f0 _ p2]
  obtain ⟨r1, r2, r3, r4⟩ := addW_run 817 pm 802 820 (by norm_num) (by norm_num) (by norm_num) s1 (by rw [j1, a1]; exact hacc)
  have hrun : Cmd.run (findBody pm rR out) s0 = ((Cmd.run (addW 817 pm 802 820) s1).1,
      (Cmd.run (.ifZero 819 (.ifLt 817 rR .skip (.ifLt rR 817 .skip (.seq (.copy out 818) (.setK 819 1)))) .skip) s0).2 +
        (Cmd.run (addW 817 pm 802 820) s1).2 + 1) := by
    simp only [findBody, Cmd.run_seq]; rfl
  have hsc : ∀ y, y ≠ 817 → y ≠ 820 → (Cmd.run (addW 817 pm 802 820) s1).1.sc y = s1.sc y := fun y h1 h2 => r2 y h1 h2
  show (Cmd.run (findBody pm rR out) s0).1.sc 817 = _ ∧ _
  rw [hrun]
  simp only
  have pmv : s1.sc pm ≤ j := by rw [pm1]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r1, j1, a1, pm1]
  · intro h0 h1
    rw [r2 819 (by norm_num) (by norm_num), r2 out o1 o4]
    exact K1 h0 h1
  · intro h0 h1
    rw [r2 819 (by norm_num) (by norm_num), r2 out o1 o4]
    exact K2 h0 h1
  · intro h0
    rw [r2 819 (by norm_num) (by norm_num), r2 out o1 o4]
    exact K3 h0
  · intro y h1 h2 h3 h4 h5
    rw [r2 y h1 h4, K4 y h3 h5, f0 y h2]
  · rw [r3, K5]
  · omega


theorem findC_run (x0 pm rR out : ℕ) (hpm : pm ≠ 817 ∧ pm ≠ 818 ∧ pm ≠ 819 ∧ pm ≠ 820 ∧ pm ≠ 802 ∧ pm ≠ out)
    (hout : out ≠ 817 ∧ out ≠ 818 ∧ out ≠ 819 ∧ out ≠ 820 ∧ out ≠ 802)
    (hR : rR ≠ 817 ∧ rR ≠ 818 ∧ rR ≠ 819 ∧ rR ≠ 820 ∧ rR ≠ out)
    (st : St) (j : ℕ) (hj : st.sc 802 = j) (hx : st.sc x0 < j) (hpl : st.sc pm < j) (hRl : st.sc rR < j) :
    ((∃ k, k < j ∧ QQ (st.sc x0) (st.sc pm) j k = st.sc rR) →
      (Cmd.run (findC x0 pm rR out) st).1.sc out < j ∧
      QQ (st.sc x0) (st.sc pm) j ((Cmd.run (findC x0 pm rR out) st).1.sc out) = st.sc rR ∧
      ∀ k, k < (Cmd.run (findC x0 pm rR out) st).1.sc out → QQ (st.sc x0) (st.sc pm) j k ≠ st.sc rR) ∧
    (∀ y, y ≠ 817 → y ≠ 818 → y ≠ 819 → y ≠ 820 → y ≠ out → (Cmd.run (findC x0 pm rR out) st).1.sc y = st.sc y) ∧
    (Cmd.run (findC x0 pm rR out) st).1.ar = st.ar ∧ (Cmd.run (findC x0 pm rR out) st).2 ≤ j * (6 * j + 9) + 7 := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpm
  obtain ⟨o1, o2, o3, o4, o5⟩ := hout
  obtain ⟨q1, q2, q3, q4, q5⟩ := hR
  have hj0 : 0 < j := by omega
  set Q := QQ (st.sc x0) (st.sc pm) j with hQ
  have hQ0 : Q 0 = st.sc x0 := by simp [hQ, QQ, Nat.mod_eq_of_lt hx]
  have hQs : ∀ k, Q (k + 1) = (Q k + st.sc pm) % j := fun k => QQ_succ _ _ _ _
  have hQl : ∀ k, Q k < j := fun k => Nat.mod_lt _ hj0
  set st1 := ((st.setSc 817 (st.sc x0)).setSc 819 0).setSc out 0 with hst1
  have g1 : ∀ y, y ≠ 817 → y ≠ 819 → y ≠ out → st1.sc y = st.sc y := fun y h1 h2 h3 => by
    simp [hst1, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  let P : ℕ → St → Prop := fun i t => t.sc 817 = Q i ∧ t.sc 819 ≤ 1 ∧ t.sc 802 = j ∧ t.sc pm = st.sc pm ∧
    t.sc rR = st.sc rR ∧
    (t.sc 819 = 0 → (∀ k, k < i → Q k ≠ st.sc rR) ∧ t.sc out = 0) ∧
    (t.sc 819 = 1 → t.sc out < i ∧ Q (t.sc out) = st.sc rR ∧ ∀ k, k < t.sc out → Q k ≠ st.sc rR) ∧
    (∀ y, y ≠ 817 → y ≠ 818 → y ≠ 819 → y ≠ 820 → y ≠ out → t.sc y = st.sc y) ∧ t.ar = st.ar
  have h0 : P 0 st1 := by
    refine ⟨by simp [hst1, St.setSc, Function.update_of_ne o1.symm, hQ0], by simp [hst1, St.setSc, Function.update_of_ne o3.symm],
      by rw [g1 _ (by norm_num) (by norm_num) (by omega), hj], by rw [g1 _ p1 p3 p6, ], by rw [g1 _ q1 q3 q5], ?_, ?_, ?_, rfl⟩
    · intro _; exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), by simp [hst1, St.setSc]⟩
    · intro h; simp [hst1, St.setSc, Function.update_of_ne o3.symm] at h
    · intro y h1 h2 h3 h4 h5; exact g1 y h1 h3 h5
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (findBody pm rR out) (t.setSc 818 i)).1 ∧
      (Cmd.run (findBody pm rR out) (t.setSc 818 i)).2 ≤ 6 * j + 8 := by
    intro i t ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := findBody_step pm rR out ⟨p1, p2, p3, p4, p5, p6⟩ ⟨o1, o2, o3, o4, o5⟩ ⟨q1, q2, q3, q4, q5⟩
      t i j 0 a3 (by rw [a4]; exact hpl) (by rw [a5]; exact hRl) (by rw [a1]; exact hQl i) a2
    set rr := (Cmd.run (findBody pm rR out) (t.setSc 818 i)).1 with hrr
    have scen : (t.sc 819 = 0 ∧ Q i = st.sc rR ∧ rr.sc 819 = 1 ∧ rr.sc out = i) ∨
        (t.sc 819 = 0 ∧ Q i ≠ st.sc rR ∧ rr.sc 819 = 0 ∧ rr.sc out = t.sc out) ∨
        (t.sc 819 = 1 ∧ rr.sc 819 = 1 ∧ rr.sc out = t.sc out) := by
      by_cases h0 : t.sc 819 = 0
      · by_cases he : Q i = st.sc rR
        · left; exact ⟨h0, he, r2 h0 (by rw [a1, a5]; exact he)⟩
        · right; left; exact ⟨h0, he, r3 h0 (by rw [a1, a5]; exact he)⟩
      · right; right
        have h1 : t.sc 819 = 1 := by omega
        have := r4 h0
        exact ⟨h1, by omega, this.2⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, r7⟩
    · rw [r1, a1, a4, hQs]
    · rcases scen with h | h | h <;> omega
    · rw [r5 802 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o5.symm, a3]
    · rw [r5 pm p1 p2 p3 p4 p6, a4]
    · rw [r5 rR q1 q2 q3 q4 q5, a5]
    · intro h0
      rcases scen with h | h | h
      · omega
      · refine ⟨fun k hk => ?_, by rw [h.2.2.2]; exact (a6 h.1).2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact ((a6 h.1).1 k hk)
        · rw [hk]; exact h.2.1
        
      · omega
    · intro h1
      rcases scen with h | h | h
      · refine ⟨by omega, by rw [h.2.2.2]; exact h.2.1, fun k hk => ?_⟩
        rw [h.2.2.2] at hk
        exact (a6 h.1).1 k hk
      · omega
      · have := a7 h.1
        refine ⟨by rw [h.2.2]; omega, by rw [h.2.2]; exact this.2.1, fun k hk => ?_⟩
        rw [h.2.2] at hk
        exact this.2.2 k hk
    · intro y h1 h2 h3 h4 h5
      rw [r5 y h1 h2 h3 h4 h5, a8 y h1 h2 h3 h4 h5]
    · rw [r6, a9]
  have hI := Cmd.loop_inv (b := 802) (c := 818) (body := findBody pm rR out) (st := st1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 802) (c := 818) (body := findBody pm rR out) (st := st1) P (6 * j + 8) h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  have e802 : st1.sc 802 = j := by rw [g1 _ (by norm_num) (by norm_num) (by omega), hj]
  rw [e802] at hI hC
  have hr : Cmd.run (findC x0 pm rR out) st = ((Cmd.run (.loop 802 818 (findBody pm rR out)) st1).1,
      1 + (1 + (1 + (Cmd.run (.loop 802 818 (findBody pm rR out)) st1).2 + 1) + 1) + 1) := by
    simp [findC, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy, hst1]
  rw [hr]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hI
  refine ⟨fun ⟨k, hk, hkq⟩ => ?_, b8, b9, ?_⟩
  · simp only
    by_cases hf : (Cmd.run (.loop 802 818 (findBody pm rR out)) st1).1.sc 819 = 0
    · exact absurd hkq ((b6 hf).1 k hk)
    · have := b7 (by omega)
      exact ⟨this.1, this.2.1, this.2.2⟩
  · simp only
    nlinarith [hC]

end ECDLP.L113
