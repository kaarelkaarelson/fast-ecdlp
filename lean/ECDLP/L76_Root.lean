import ECDLP.L76_Ops
import ECDLP.L76_RootMath

/-!
# L76 / Root: powers `c^k` (plain, via `mulMod` modulo `2^(W-1)`) and the integer `m`-th root
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `T1 := T1 * C` (exact, when it fits below `V Pn = 2^(W-1)`); `T2` is scratch -/
def powStep (C T1 T2 Pn tA tB : ℕ) : Cmd := .seq (mulMod T2 T1 C Pn tA tB) (copyA T1 T2)

def ZP (y : ℕ) : Prop := ZM y ∨ ZC y

theorem powStep_run (C T1 T2 Pn tA tB : ℕ) (hnd : List.Nodup [T2, T1, C, Pn, tA, tB]) (st : St) (n : ℕ)
    (hW : st.sc 710 = n) (hT : V (st.ar T1) n * V (st.ar C) n < V (st.ar Pn) n) (hT1 : V (st.ar T1) n < V (st.ar Pn) n)
    (hP : 2 * V (st.ar Pn) n ≤ 2 ^ n) :
    let r := Cmd.run (powStep C T1 T2 Pn tA tB) st
    Cells n (r.1.ar T1) (st.ar T1) ∧ V (r.1.ar T1) n = V (st.ar T1) n * V (st.ar C) n ∧
    ArK (fun a => a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st r.1 ∧ ScKeep ZP st r.1 ∧
    r.2 ≤ 300 * n * n + 320 * n + 40 := by
  intro r
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b2, b3, b4, b5⟩, ⟨c3, c4, c5⟩, ⟨d4, d5⟩, e5, -⟩ := hnd'
  obtain ⟨m1, m2, m3, m4, m5⟩ := mulMod_run T2 T1 C Pn tA tB hnd st n hW hT1 hP
  generalize hm : Cmd.run (mulMod T2 T1 C Pn tA tB) st = s1 at m1 m2 m3 m4 m5
  have w1 : s1.1.sc 710 = n := by rw [m4 710 (by simp [ZM, ZB, ZA, ZC])]; exact hW
  have kT1 : s1.1.ar T1 = st.ar T1 := m3 T1 (by intro h; rcases h with h | h | h; exact a1 h.symm; exact b4 h; exact b5 h)
  have vv : V (s1.1.ar T2) n = V (st.ar T1) n * V (st.ar C) n := by
    rw [m2, Nat.mod_eq_of_lt hT]
  obtain ⟨c1, c2, c3', c4', c5', c6'⟩ := copyA_run T1 T2 (fun h => a1 h.symm) s1.1 n w1
  simp only [r, powStep, Cmd.run_seq, hm]
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · rw [kT1] at c1; exact c1
  · rw [c3', vv]
  · have c4'' : ArK (fun a => a = T1) s1.1 (Cmd.run (copyA T1 T2) s1.1).1 := c4'
    exact (ArK.trans m3 c4'').mono (fun a ha => by rcases ha with (h | h | h) | h <;> simp [h])
  · exact (ScKeep.trans m4 c5').mono (fun y h => h)

def powSeq (C T1 T2 Pn tA tB : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (powSeq C T1 T2 Pn tA tB k) (powStep C T1 T2 Pn tA tB)

theorem powSeq_run (C T1 T2 Pn tA tB : ℕ) (hnd : List.Nodup [T2, T1, C, Pn, tA, tB]) (k : ℕ) (st : St) (n : ℕ)
    (hW : st.sc 710 = n) (hb : Cells n (st.ar T1) (st.ar T1)) (hT : V (st.ar T1) n = V (st.ar C) n)
    (hpow : ∀ i, 1 ≤ i → i ≤ k + 1 → (V (st.ar C) n) ^ i < V (st.ar Pn) n) (hP : 2 * V (st.ar Pn) n ≤ 2 ^ n) :
    let r := Cmd.run (powSeq C T1 T2 Pn tA tB k) st
    Cells n (r.1.ar T1) (st.ar T1) ∧ V (r.1.ar T1) n = (V (st.ar C) n) ^ (k + 1) ∧
    ArK (fun a => a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st r.1 ∧ ScKeep ZP st r.1 ∧
    r.2 ≤ k * (300 * n * n + 320 * n + 41) + 1 := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b2, b3, b4, b5⟩, ⟨c3, c4, c5⟩, ⟨d4, d5⟩, e5, -⟩ := hnd'
  induction k with
  | zero =>
    intro r
    simp only [r, powSeq, Cmd.run_skip]
    refine ⟨hb, by simpa using hT, fun a ha => rfl, fun y hy => rfl, by simp⟩
  | succ k ih =>
    intro r
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih (fun i h1 h2 => hpow i h1 (by omega))
    generalize hs : Cmd.run (powSeq C T1 T2 Pn tA tB k) st = s1 at i1 i2 i3 i4 i5
    have w1 : s1.1.sc 710 = n := by rw [i4 710 (by simp [ZP, ZM, ZB, ZA, ZC])]; exact hW
    have kC : s1.1.ar C = st.ar C := i3 C (by intro h; rcases h with h | h | h | h; exact b2 h.symm; exact a2 h.symm; exact c4 h; exact c5 h)
    have kP : s1.1.ar Pn = st.ar Pn := i3 Pn (by intro h; rcases h with h | h | h | h; exact b3 h.symm; exact a3 h.symm; exact d4 h; exact d5 h)
    have cc : V (s1.1.ar C) n = V (st.ar C) n := by rw [kC]
    have pp : V (s1.1.ar Pn) n = V (st.ar Pn) n := by rw [kP]
    obtain ⟨j1, j2, j3, j4, j5⟩ := powStep_run C T1 T2 Pn tA tB hnd s1.1 n w1
      (by rw [i2, cc, pp, ← pow_succ]; exact hpow (k + 2) (by omega) le_rfl)
      (by rw [i2, pp]; exact hpow (k + 1) (by omega) (by omega)) (by rw [pp]; exact hP)
    simp only [r, powSeq, Cmd.run_seq, hs]
    refine ⟨j1.trans i1, ?_, ?_, ?_, ?_⟩
    · rw [j2, i2, cc]; ring
    · exact (ArK.trans i3 j3).mono (fun a ha => by rcases ha with h | h <;> exact h)
    · exact (ScKeep.trans i4 j4).mono (fun y h => by rcases h with h | h <;> exact h)
    · nlinarith [i5, j5]

theorem V_update_one (f : ℕ → ℕ) (idx : ℕ) : ∀ n, 1 ≤ idx → idx ≤ n → f idx = 0 →
    V (Function.update f idx 1) n = V f n + 2 ^ (idx - 1) := by
  intro n
  induction n with
  | zero => intro h1 h2; omega
  | succ n ih =>
    intro h1 h2 h3
    rw [V_snoc, V_snoc f]
    by_cases hi : idx = n + 1
    · subst hi
      have e1 : V (Function.update f (n + 1) 1) n = V f n :=
        V_congr fun j _ hj => by simp [Function.update_apply, show j ≠ n + 1 by omega]
      have e2 : bt (Function.update f (n + 1) 1) (n + 1) = 1 := by simp [bt]
      have e3 : bt f (n + 1) = 0 := by simp [bt, h3]
      rw [e1, e2, e3]; simp
    · have e1 := ih h1 (by omega) h3
      have e2 : bt (Function.update f idx 1) (n + 1) = bt f (n + 1) := by
        simp [bt, Function.update_apply, Ne.symm hi]
      rw [e1, e2]; ring

def rootBody (m : ℕ) (C T1 T2 Pn p tA tB : ℕ) : Cmd :=
  .seq (.wr C 750 0 755) (.seq (copyA T1 C) (.seq (powSeq C T1 T2 Pn tA tB (m - 1))
    (.seq (geC tA T1 p) (.seq (.ifZero 722 .skip (.wr C 750 0 756)) (.decr 750)))))

/-- `C := ⌈p^(1/m)⌉ - 1`, scanning `nb` bits (`nb` in scalar 752) -/
def rootC (m : ℕ) (C T1 T2 Pn p tA tB : ℕ) : Cmd :=
  .seq (zeroA C) (.seq (.setK 755 1) (.seq (.setK 756 0) (.seq (.copy 750 752)
    (.loop 752 751 (rootBody m C T1 T2 Pn p tA tB)))))

/-- registers of the root -/
def ZR (y : ℕ) : Prop := ZP y ∨ (750 ≤ y ∧ y ≤ 756)

theorem Cells_update {n idx v : ℕ} {f g : ℕ → ℕ} (h : Cells n f g) (hi : 1 ≤ idx ∧ idx ≤ n) (hv : v ≤ 1) :
    Cells n (Function.update f idx v) g := by
  intro i
  obtain ⟨h1, h2⟩ := h i
  by_cases hii : i = idx
  · subst hii; simp [hv, hi]
  · simp only [Function.update_apply, if_neg hii]; exact ⟨h1, h2⟩

theorem Cells_self {n : ℕ} {f g : ℕ → ℕ} (h : Cells n f g) : Cells n f f := fun i => ⟨(h i).1, fun _ => rfl⟩

theorem even_div (c e : ℕ) (h : 2 ^ (e + 1) ∣ c) : (c / 2 ^ e) % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  omega

theorem bt_eq_zero {f : ℕ → ℕ} {i : ℕ} (h : bt f i = 0) : f i = 0 := by
  unfold bt at h; split_ifs at h with h1; exact h1

theorem trial_pow_lt (c d nb m i : ℕ) (hm : 1 ≤ m) (hi1 : 1 ≤ i) (him : i ≤ m) (hd : 1 ≤ d)
    (hc : c + 2 * d ≤ 2 ^ nb) : (c + d) ^ i < (2 ^ nb) ^ m := by
  have h1 : c + d < 2 ^ nb := by omega
  calc (c + d) ^ i ≤ (c + d) ^ m := Nat.pow_le_pow_right (by omega) him
    _ < (2 ^ nb) ^ m := Nat.pow_lt_pow_left h1 (by omega)

theorem arith_e (nb j n e : ℕ) (he : nb - j = e + 1) (hnb : nb ≤ n) : e < n := by omega
theorem arith_e2 (nb j e : ℕ) (hj : j < nb) (he : nb - j = e + 1) : nb - 1 - j = e := by omega
theorem arith_e3 (nb j : ℕ) (hj : j < nb) : ∃ e, nb - j = e + 1 := ⟨nb - j - 1, by omega⟩

theorem root_cost (m n a b c d : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (ha : a ≤ 7 * n + 1)
    (hb : b ≤ (m - 1) * (300 * n * n + 320 * n + 41) + 1) (hc : c ≤ 40 * n + 20) (hd : d ≤ 10) :
    1 + (a + (b + (c + d + 1) + 1) + 1) + 1 ≤ 400 * m * n * n + 400 * m * n + 100 * m + 100 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hb
  nlinarith [Nat.zero_le (k * n * n), Nat.zero_le (k * n), Nat.mul_le_mul hn hn]

set_option maxHeartbeats 800000 in
theorem rootBody_step (m C T1 T2 Pn p tA tB : ℕ) (hnd : List.Nodup [C, T1, T2, Pn, p, tA, tB]) (st t : St)
    (n nb j : ℕ) (hm : 1 ≤ m) (hpv : 0 < V (st.ar p) n) (hb : V (st.ar p) n ≤ (2 ^ nb) ^ m) (hnb : nb ≤ n)
    (hPn : (2 ^ nb) ^ m ≤ V (st.ar Pn) n) (hP : 2 * V (st.ar Pn) n ≤ 2 ^ n) (hW : st.sc 710 = n) (hj : j < nb)
    (c1 : Cells n (t.ar C) (st.ar C)) (c2 : V (t.ar C) n = cseq (V (st.ar p) n) m nb j) (c3 : t.sc 750 = nb - j)
    (c4 : t.sc 710 = n) (c5 : t.sc 755 = 1) (c6 : t.sc 756 = 0)
    (c7 : ArK (fun a => a = C ∨ a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st t) (c8 : ScKeep ZR st t) :
    let r := Cmd.run (rootBody m C T1 T2 Pn p tA tB) (t.setSc 751 j)
    Cells n (r.1.ar C) (st.ar C) ∧ V (r.1.ar C) n = cseq (V (st.ar p) n) m nb (j + 1) ∧ r.1.sc 750 = nb - (j + 1) ∧
    r.1.sc 710 = n ∧ r.1.sc 755 = 1 ∧ r.1.sc 756 = 0 ∧
    ArK (fun a => a = C ∨ a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st r.1 ∧ ScKeep ZR st r.1 ∧
    r.2 ≤ 400 * m * n * n + 400 * m * n + 100 * m + 100 := by
  intro r
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b2, b3, b4, b5, b6⟩, ⟨e3, e4, e5, e6⟩, ⟨f4, f5, f6⟩, ⟨g5, g6⟩, h56, -⟩ := hnd'
  -- a1: C≠T1 a2: C≠T2 a3: C≠Pn a4: C≠p a5: C≠tA a6: C≠tB ; b2: T1≠T2 b3: T1≠Pn b4: T1≠p b5: T1≠tA b6: T1≠tB
  -- e3: T2≠Pn e4: T2≠p e5: T2≠tA e6: T2≠tB ; f4: Pn≠p f5: Pn≠tA f6: Pn≠tB ; g5: p≠tA g6: p≠tB ; h56 : tA≠tB
  have kp : t.ar p = st.ar p := c7 p (by intro h; rcases h with h | h | h | h | h; exact a4 h.symm; exact b4 h.symm; exact e4 h.symm; exact g5 h; exact g6 h)
  have kPn : t.ar Pn = st.ar Pn := c7 Pn (by intro h; rcases h with h | h | h | h | h; exact a3 h.symm; exact b3 h.symm; exact e3 h.symm; exact f5 h; exact f6 h)
  obtain ⟨pv, hpvd⟩ : ∃ pv, V (st.ar p) n = pv := ⟨_, rfl⟩
  rw [hpvd] at hpv hb c2 ⊢
  obtain ⟨i1, i2, i3, i4⟩ := cseq_inv pv m nb hm hpv hb j (by omega)
  obtain ⟨cj, hcj⟩ : ∃ cj, cseq pv m nb j = cj := ⟨_, rfl⟩
  rw [hcj] at i1 i2 i3 i4 c2
  obtain ⟨e, he⟩ := arith_e3 nb j hj
  have he2 : nb - 1 - j = e := arith_e2 nb j e hj he
  have hd1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h2d : 2 ^ (nb - j) = 2 * 2 ^ e := by rw [he, pow_succ]; ring
  -- the cell to be set is zero
  have hcell0 : t.ar C (nb - j) = 0 := by
    have := V_div_mod2 (t.ar C) n e (arith_e nb j n e he hnb)
    rw [← he, c2] at this
    have hev := even_div cj e (by rw [← he]; exact i2)
    exact bt_eq_zero (this.symm.trans hev)
  have hidx : 1 ≤ nb - j ∧ nb - j ≤ n := ⟨by omega, by omega⟩
  have w710 : (t.setSc 751 j).sc 710 = n := by simp [St.setSc, Function.update_apply, c4]
  have t750 : (t.setSc 751 j).sc 750 = nb - j := by simp [St.setSc, Function.update_apply, c3]
  have t755 : (t.setSc 751 j).sc 755 = 1 := by simp [St.setSc, Function.update_apply, c5]
  -- stage 1: write the trial bit
  obtain ⟨S1, hS1, f1, f2, f3⟩ : ∃ S1 : St, Cmd.run (.wr C 750 0 755) (t.setSc 751 j) = (S1, 1) ∧
      S1.ar C = Function.update (t.ar C) (nb - j) 1 ∧ (∀ a, a ≠ C → S1.ar a = t.ar a) ∧
      (∀ y, S1.sc y = (t.setSc 751 j).sc y) := by
    refine ⟨(t.setSc 751 j).setAr C (nb - j) 1, ?_, ?_, ?_, ?_⟩
    · simp only [Cmd.run_wr, t750, t755, Nat.add_zero]
    · simp [St.setAr, St.putAr]
    · intro a ha; simp [St.setAr, St.putAr, Function.update_apply, ha]
    · intro y; rfl
  have vS1 : V (S1.ar C) n = cj + 2 ^ e := by
    rw [f1, V_update_one (t.ar C) (nb - j) n hidx.1 hidx.2 hcell0, c2, he]; simp
  have s1710 : S1.sc 710 = n := by rw [f3]; exact w710
  -- stage 2: copy
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := copyA_run T1 C (fun h => a1 h.symm) S1 n s1710
  generalize hs2 : Cmd.run (copyA T1 C) S1 = s2 at u1 u2 u3 u4 u5 u6
  have s2710 : s2.1.sc 710 = n := by rw [u5 710 (by simp [ZC])]; exact s1710
  have s2C : s2.1.ar C = S1.ar C := u4 C a1
  have s2Pn : s2.1.ar Pn = st.ar Pn := by rw [u4 Pn (fun h => b3 h.symm |> fun x => x), f2 Pn (fun h => a3 h.symm), kPn]
  have s2p : s2.1.ar p = st.ar p := by rw [u4 p (fun h => b4 h.symm), f2 p (fun h => a4 h.symm), kp]
  have hpow : ∀ i, 1 ≤ i → i ≤ m - 1 + 1 → (V (s2.1.ar C) n) ^ i < V (s2.1.ar Pn) n := by
    intro i h1 h2
    rw [s2C, vS1, s2Pn]
    have h2' : i ≤ m := Nat.le_trans h2 (Nat.le_of_eq (Nat.sub_add_cancel hm))
    have hc : cj + 2 * 2 ^ e ≤ 2 ^ nb := by rw [← h2d]; exact i4
    exact lt_of_lt_of_le (trial_pow_lt cj (2 ^ e) nb m i hm h1 h2' hd1 hc) hPn
  have hnd2 : List.Nodup [T2, T1, C, Pn, tA, tB] := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨fun h => b2 h.symm, fun h => a2 h.symm, e3, e5, e6⟩, ⟨fun h => a1 h.symm, b3, b5, b6⟩, ⟨a3, a5, a6⟩,
      ⟨f5, f6⟩, h56, id, List.nodup_nil⟩
  obtain ⟨p1, p2, p3, p4, p5⟩ := powSeq_run C T1 T2 Pn tA tB hnd2
    (m - 1) s2.1 n s2710 (Cells_self u1) (by rw [u3, s2C, vS1]) hpow (by rw [s2Pn]; exact hP)
  generalize hs3 : Cmd.run (powSeq C T1 T2 Pn tA tB (m - 1)) s2.1 = s3 at p1 p2 p3 p4 p5
  have p2' : V (s3.1.ar T1) n = (cj + 2 ^ e) ^ m := by rw [p2, s2C, vS1, Nat.sub_add_cancel hm]
  have nZP : ∀ y, y = 710 ∨ y = 750 ∨ y = 755 ∨ y = 756 → ¬ ZP y := by
    intro y hy; rcases hy with h | h | h | h <;> subst h <;> simp [ZP, ZM, ZB, ZA, ZC]
  have nZC : ∀ y, y = 710 ∨ y = 750 ∨ y = 755 ∨ y = 756 → ¬ ZC y := by
    intro y hy; rcases hy with h | h | h | h <;> subst h <;> simp [ZC]
  have nZB : ∀ y, y = 710 ∨ y = 750 ∨ y = 755 ∨ y = 756 → ¬ ZB y := by
    intro y hy; rcases hy with h | h | h | h <;> subst h <;> simp [ZB, ZA, ZC]
  have s3710 : s3.1.sc 710 = n := by rw [p4 710 (nZP 710 (Or.inl rfl))]; exact s2710
  have s3p : s3.1.ar p = st.ar p := by
    rw [p3 p (by intro h; rcases h with h | h | h | h; exact b4 h.symm; exact e4 h.symm; exact g5 h; exact g6 h)]; exact s2p
  obtain ⟨q1, q2, q3, q4⟩ := geC_run tA T1 p (fun h => b5 h.symm) (fun h => g5 h.symm) s3.1 n s3710
  generalize hs4 : Cmd.run (geC tA T1 p) s3.1 = s4 at q1 q2 q3 q4
  rw [s3p, p2', hpvd] at q1
  have y_chain : ∀ y, y = 710 ∨ y = 750 ∨ y = 755 ∨ y = 756 → s4.1.sc y = t.sc y := by
    intro y hy
    rw [q3 y (nZB y hy), p4 y (nZP y hy), u5 y (nZC y hy), f3 y]
    rcases hy with h | h | h | h <;> subst h <;> simp [St.setSc, Function.update_apply]
  have s4C : s4.1.ar C = S1.ar C := by
    rw [q2 C a5, p3 C (by intro h; rcases h with h | h | h | h; exact a1 h; exact a2 h; exact a5 h; exact a6 h), s2C]
  have s4ar : ∀ a, a ≠ C → a ≠ T1 → a ≠ T2 → a ≠ tA → a ≠ tB → s4.1.ar a = st.ar a := by
    intro a hC hT1 hT2 htA htB
    rw [q2 a htA, p3 a (by intro h; rcases h with h | h | h | h; exact hT1 h; exact hT2 h; exact htA h; exact htB h),
      u4 a hT1, f2 a hC]
    exact c7 a (by intro h; rcases h with h | h | h | h | h; exact hC h; exact hT1 h; exact hT2 h; exact htA h; exact htB h)
  have s4sc : ∀ y, ¬ ZR y → y ≠ 751 → s4.1.sc y = st.sc y := by
    intro y hy h751
    have n1 : ¬ ZB y := fun h => hy (Or.inl (Or.inl (Or.inl h)))
    have n2 : ¬ ZP y := fun h => hy (Or.inl h)
    have n3 : ¬ ZC y := fun h => hy (Or.inl (Or.inr h))
    rw [q3 y n1, p4 y n2, u5 y n3, f3 y]
    simp only [St.setSc_sc, Function.update_of_ne h751]
    exact c8 y hy
  have n750 : ¬ (750 : ℕ) = 751 := by norm_num
  have k0 : ∀ Rpre : St, (∀ y, Rpre.sc y = s4.1.sc y) → (∀ a, a ≠ C → Rpre.ar a = s4.1.ar a) →
      Cells n (Rpre.ar C) (st.ar C) → V (Rpre.ar C) n = cseq pv m nb (j + 1) →
      Cells n ((Rpre.setSc 750 (Rpre.sc 750 - 1)).ar C) (st.ar C) ∧
      V ((Rpre.setSc 750 (Rpre.sc 750 - 1)).ar C) n = cseq pv m nb (j + 1) ∧
      (Rpre.setSc 750 (Rpre.sc 750 - 1)).sc 750 = nb - (j + 1) ∧ (Rpre.setSc 750 (Rpre.sc 750 - 1)).sc 710 = n ∧
      (Rpre.setSc 750 (Rpre.sc 750 - 1)).sc 755 = 1 ∧ (Rpre.setSc 750 (Rpre.sc 750 - 1)).sc 756 = 0 ∧
      ArK (fun a => a = C ∨ a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st (Rpre.setSc 750 (Rpre.sc 750 - 1)) ∧
      ScKeep ZR st (Rpre.setSc 750 (Rpre.sc 750 - 1)) := by
    intro Rpre hs ha hc hv
    refine ⟨hc, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Function.update Rpre.sc 750 (Rpre.sc 750 - 1) 750 = _
      rw [Function.update_self, hs, y_chain 750 (Or.inr (Or.inl rfl)), c3, Nat.sub_sub]
    · show Function.update Rpre.sc 750 (Rpre.sc 750 - 1) 710 = _
      rw [Function.update_of_ne (by norm_num), hs, y_chain 710 (Or.inl rfl), c4]
    · show Function.update Rpre.sc 750 (Rpre.sc 750 - 1) 755 = _
      rw [Function.update_of_ne (by norm_num), hs, y_chain 755 (Or.inr (Or.inr (Or.inl rfl))), c5]
    · show Function.update Rpre.sc 750 (Rpre.sc 750 - 1) 756 = _
      rw [Function.update_of_ne (by norm_num), hs, y_chain 756 (Or.inr (Or.inr (Or.inr rfl))), c6]
    · intro a haa
      have hC : a ≠ C := fun h => haa (Or.inl h)
      have hT1 : a ≠ T1 := fun h => haa (Or.inr (Or.inl h))
      have hT2 : a ≠ T2 := fun h => haa (Or.inr (Or.inr (Or.inl h)))
      have htA : a ≠ tA := fun h => haa (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have htB : a ≠ tB := fun h => haa (Or.inr (Or.inr (Or.inr (Or.inr h))))
      show Rpre.ar a = st.ar a
      rw [ha a hC]; exact s4ar a hC hT1 hT2 htA htB
    · intro y hy
      have h750 : y ≠ 750 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have h751 : y ≠ 751 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      show Function.update Rpre.sc 750 _ y = st.sc y
      rw [Function.update_of_ne h750, hs]
      exact s4sc y hy h751
  have hn0 : 1 ≤ n := Nat.le_trans (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)) hnb
  simp only [r, rootBody, Cmd.run_seq, hS1, hs2, hs3, hs4]
  by_cases hlt : (cj + 2 ^ e) ^ m < pv
  · have hflag : s4.1.sc 722 = 0 := by rw [q1, if_neg (not_le.mpr hlt)]
    simp only [Cmd.run_ifZero, hflag, ↓reduceIte, Cmd.run_skip, Cmd.run_decr]
    have := k0 s4.1 (fun y => rfl) (fun a _ => rfl) (by rw [s4C, f1]; exact Cells_update c1 hidx (le_refl 1))
      (by rw [s4C, vS1]; show _ = (if (cseq pv m nb j + 2 ^ (nb - 1 - j)) ^ m < pv then _ else _); rw [hcj, he2, if_pos hlt])
    obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := this
    refine ⟨z1, z2, z3, z4, z5, z6, z7, z8, ?_⟩
    exact root_cost m n s2.2 s3.2 s4.2 4 hm hn0 u6 p5 q4 (by norm_num)
  · have hflag : s4.1.sc 722 = 1 := by rw [q1, if_pos (not_lt.mp hlt)]
    simp only [Cmd.run_ifZero, hflag, one_ne_zero, ↓reduceIte, Cmd.run_wr, Cmd.run_decr]
    have hRC : (s4.1.setAr C (s4.1.sc 750 + 0) (s4.1.sc 756)).ar C = t.ar C := by
      rw [St.setAr_ar, Function.update_self, s4C, f1, y_chain 750 (Or.inr (Or.inl rfl)), y_chain 756 (Or.inr (Or.inr (Or.inr rfl))), c3, c6, Nat.add_zero,
        Function.update_idem]
      exact Function.update_eq_self_iff.mpr hcell0.symm
    have := k0 (s4.1.setAr C (s4.1.sc 750 + 0) (s4.1.sc 756)) (fun y => rfl)
      (fun a ha => by rw [St.setAr_ar, Function.update_of_ne ha])
      (by rw [hRC]; exact c1)
      (by rw [hRC, c2]; show _ = (if (cseq pv m nb j + 2 ^ (nb - 1 - j)) ^ m < pv then _ else _); rw [hcj, he2, if_neg hlt])
    obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := this
    refine ⟨z1, z2, z3, z4, z5, z6, z7, z8, ?_⟩
    exact root_cost m n s2.2 s3.2 s4.2 4 hm hn0 u6 p5 q4 (by norm_num)

theorem rootC_run (m C T1 T2 Pn p tA tB : ℕ) (hnd : List.Nodup [C, T1, T2, Pn, p, tA, tB]) (st : St) (n nb : ℕ)
    (hm : 1 ≤ m) (hpv : 0 < V (st.ar p) n) (hb : V (st.ar p) n ≤ (2 ^ nb) ^ m) (hnb : nb ≤ n)
    (hPn : (2 ^ nb) ^ m ≤ V (st.ar Pn) n) (hP : 2 * V (st.ar Pn) n ≤ 2 ^ n) (hW : st.sc 710 = n)
    (h752 : st.sc 752 = nb) :
    let r := Cmd.run (rootC m C T1 T2 Pn p tA tB) st
    Cells n (r.1.ar C) (st.ar C) ∧ V (r.1.ar C) n + 1 = sInf {B | V (st.ar p) n ≤ B ^ m} ∧
    ArK (fun a => a = C ∨ a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st r.1 ∧ ScKeep ZR st r.1 ∧
    r.2 ≤ n * (400 * m * n * n + 400 * m * n + 100 * m + 101) + 5 * n + 20 := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run C st n hW
  generalize hz : Cmd.run (zeroA C) st = s0 at z1 z2 z3 z4 z5
  have nz : ∀ y, y = 710 ∨ y = 750 ∨ y = 752 ∨ y = 755 ∨ y = 756 → ¬ ZC y := by
    intro y hy; rcases hy with h | h | h | h | h <;> subst h <;> simp [ZC]
  let st2 : St := (((s0.1.setSc 755 1).setSc 756 0).setSc 750 (((s0.1.setSc 755 1).setSc 756 0).sc 752))
  have hnb0 : 0 < nb ∨ nb = 0 := by omega
  let Pj : ℕ → St → Prop := fun j t =>
    Cells n (t.ar C) (st.ar C) ∧ V (t.ar C) n = cseq (V (st.ar p) n) m nb j ∧ t.sc 750 = nb - j ∧
    t.sc 710 = n ∧ t.sc 755 = 1 ∧ t.sc 756 = 0 ∧
    ArK (fun a => a = C ∨ a = T1 ∨ a = T2 ∨ a = tA ∨ a = tB) st t ∧ ScKeep ZR st t
  have s752 : s0.1.sc 752 = nb := by rw [z4 752 (nz 752 (by simp))]; exact h752
  have s752' : ((s0.1.setSc 755 1).setSc 756 0).sc 752 = nb := by
    simp only [St.setSc_sc]
    rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num)]; exact s752
  have h0 : Pj 0 st2 := by
    refine ⟨z1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show V (s0.1.ar C) n = 0
      exact z2
    · simp only [st2, St.setSc_sc, Function.update_self, s752', Nat.sub_zero]
    · simp only [st2, St.setSc_sc]
      rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
        z4 710 (nz 710 (by simp))]; exact hW
    · simp only [st2, St.setSc_sc]
      rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), Function.update_self]
    · simp only [st2, St.setSc_sc]
      rw [Function.update_of_ne (by norm_num), Function.update_self]
    · intro a ha; exact z3 a (fun h => ha (Or.inl h))
    · intro y hy
      have h1 : y ≠ 750 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have h2 : y ≠ 755 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have h3 : y ≠ 756 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      show Function.update (Function.update (Function.update s0.1.sc 755 1) 756 0) 750 _ y = st.sc y
      rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2]
      exact z4 y (fun h => hy (Or.inl (Or.inr h)))
  have e752 : st2.sc 752 = nb := by
    simp only [st2, St.setSc_sc]
    rw [Function.update_of_ne (by norm_num)]
    exact s752'
  have hstep : ∀ j t, j < st2.sc 752 → Pj j t →
      Pj (j + 1) (Cmd.run (rootBody m C T1 T2 Pn p tA tB) (t.setSc 751 j)).1 := by
    intro j t hj ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩
    rw [e752] at hj
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := rootBody_step m C T1 T2 Pn p tA tB hnd st t n nb j hm hpv hb hnb hPn hP hW
      hj c1 c2 c3 c4 c5 c6 c7 c8
    exact ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  have hI := Cmd.loop_inv (b := 752) (c := 751) (body := rootBody m C T1 T2 Pn p tA tB) Pj h0 hstep
  have hC := Cmd.loop_cost_le (b := 752) (c := 751) (body := rootBody m C T1 T2 Pn p tA tB) Pj
    (400 * m * n * n + 400 * m * n + 100 * m + 100) h0 hstep
    (fun j t hj hp => by
      rw [e752] at hj
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hp
      exact (rootBody_step m C T1 T2 Pn p tA tB hnd st t n nb j hm hpv hb hnb hPn hP hW hj c1 c2 c3 c4 c5 c6 c7 c8).2.2.2.2.2.2.2.2)
  rw [e752] at hI hC
  have hr : Cmd.run (rootC m C T1 T2 Pn p tA tB) st =
      ((Cmd.run (.loop 752 751 (rootBody m C T1 T2 Pn p tA tB)) st2).1,
        s0.2 + (1 + (1 + (1 + (Cmd.run (.loop 752 751 (rootBody m C T1 T2 Pn p tA tB)) st2).2 + 1) + 1) + 1) + 1) := by
    simp only [rootC, Cmd.run_seq, Cmd.run_setK, Cmd.run_copy, hz, st2]
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI
  simp only [r, hr]
  refine ⟨i1, ?_, i7, i8, ?_⟩
  · have := cseq_final (V (st.ar p) n) m nb hm hpv hb
    rw [← this, i2]
  · have := Nat.mul_le_mul_right (400 * m * n * n + 400 * m * n + 100 * m + 101) hnb
    have h2 : nb * (400 * m * n * n + 400 * m * n + 100 * m + 100 + 1) + 1 ≤
        n * (400 * m * n * n + 400 * m * n + 100 * m + 101) + 1 := by
      have e : 400 * m * n * n + 400 * m * n + 100 * m + 100 + 1 = 400 * m * n * n + 400 * m * n + 100 * m + 101 := by ring
      rw [e]; omega
    omega

end ECDLP.L76
