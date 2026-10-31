import ECDLP.L76_Mod

/-!
# L76 / Mul: modular multiplication by the Horner scheme on bit arrays

`mulMod acc A B P tmp tmp2`: `acc := (A * B) mod P`, scanning the bits of `B` from the top; each turn is `dblMod` then (if the bit is set) `addMod`.
With `A = 1` this is the reduction `B mod P`; with `P = 2^(W-1)` it is the exact product (when `A*B < 2^(W-1)`).
Scratch scalars `740 .. 742` (pointer, bit) and the loop counter `741`.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem V_div_mod2 (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) : (V f n / 2 ^ i) % 2 = bt f (i + 1) := by
  have h := testBit_numCells f n 1 i hi
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  unfold bt
  rw [Nat.add_comm i 1]
  have h2 := Nat.mod_lt (V f n / 2 ^ i) (by norm_num : 0 < 2)
  by_cases hz : f (1 + i) = 0
  · simp only [hz, ne_eq, not_true_eq_false, decide_false] at h
    simp only [hz, if_true]
    have : ¬ (V f n / 2 ^ i % 2 = 1) := by simpa using h
    omega
  · simp only [hz, ne_eq, not_false_eq_true, decide_true] at h
    simp only [hz, if_false]
    have : V f n / 2 ^ i % 2 = 1 := by simpa using h
    omega

theorem div_step (B e : ℕ) : B / 2 ^ e = 2 * (B / 2 ^ (e + 1)) + (B / 2 ^ e) % 2 := by
  have h1 : B / 2 ^ (e + 1) = B / 2 ^ e / 2 := by rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rw [h1]; omega

theorem mod_step (a T b P : ℕ) : (2 * ((a * T) % P) + b * a) % P = (a * (2 * T + b)) % P := by
  have h : (a * T) % P ≡ a * T [MOD P] := Nat.mod_modEq _ _
  have h2 : 2 * ((a * T) % P) + b * a ≡ 2 * (a * T) + b * a [MOD P] := (h.mul_left 2).add_right _
  have h3 : 2 * (a * T) + b * a = a * (2 * T + b) := by ring
  rw [h3] at h2
  exact h2

def mulBody (acc A B P tmp tmp2 : ℕ) : Cmd :=
  .seq (dblMod acc P tmp tmp2) (.seq (.rd 742 B 740 0) (.seq (.ifZero 742 .skip (addMod acc A P tmp)) (.decr 740)))

/-- `acc := A * B mod P` over cells `1..W` -/
def mulMod (acc A B P tmp tmp2 : ℕ) : Cmd :=
  .seq (zeroA acc) (.seq (.copy 740 710) (.loop 710 741 (mulBody acc A B P tmp tmp2)))

/-- registers of `mulMod` -/
def ZM (y : ℕ) : Prop := ZB y ∨ (740 ≤ y ∧ y ≤ 742)

theorem T_step (f : ℕ → ℕ) (n j : ℕ) (hj : j < n) :
    V f n / 2 ^ (n - (j + 1)) = 2 * (V f n / 2 ^ (n - j)) + bt f (n - j) := by
  have e1 : n - (j + 1) + 1 = n - j := by omega
  have h1 := V_div_mod2 f n (n - (j + 1)) (by omega)
  have h2 := div_step (V f n) (n - (j + 1))
  rw [e1] at h1 h2
  rw [← h1]; exact h2

/-- one turn of `mulMod` -/
theorem mulBody_step (acc A B P tmp tmp2 : ℕ) (hnd : List.Nodup [acc, A, B, P, tmp, tmp2]) (st t : St) (n j : ℕ)
    (hj : j < n) (hW : st.sc 710 = n) (hA : V (st.ar A) n < V (st.ar P) n) (hP : 2 * V (st.ar P) n ≤ 2 ^ n)
    (c1 : Cells n (t.ar acc) (st.ar acc))
    (c2 : V (t.ar acc) n = (V (st.ar A) n * (V (st.ar B) n / 2 ^ (n - j))) % V (st.ar P) n)
    (c3 : t.sc 740 = n - j) (c4 : t.sc 710 = n) (c5 : ArK (fun a => a = acc ∨ a = tmp ∨ a = tmp2) st t)
    (c6 : ScKeep ZM st t) :
    let r := (Cmd.run (mulBody acc A B P tmp tmp2) (t.setSc 741 j))
    Cells n (r.1.ar acc) (st.ar acc) ∧
    V (r.1.ar acc) n = (V (st.ar A) n * (V (st.ar B) n / 2 ^ (n - (j + 1)))) % V (st.ar P) n ∧
    r.1.sc 740 = n - (j + 1) ∧ r.1.sc 710 = n ∧ ArK (fun a => a = acc ∨ a = tmp ∨ a = tmp2) st r.1 ∧
    ScKeep ZM st r.1 ∧ r.2 ≤ 200 * n + 100 := by
  intro r
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hac1, hac2, hac3, hac4, hac5⟩, ⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45, -⟩ := hnd
  have kA : t.ar A = st.ar A := c5 A (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])
  have kB : t.ar B = st.ar B := c5 B (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])
  have kP : t.ar P = st.ar P := c5 P (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])
  have hPpos : 0 < V (st.ar P) n := by omega
  have hT : n - j - 1 = n - (j + 1) := by omega
  have e710 : (t.setSc 741 j).sc 710 = n := by simp [St.setSc, Function.update_apply, c4]
  have hacc : V (t.ar acc) n < V (st.ar P) n := by rw [c2]; exact Nat.mod_lt _ hPpos
  obtain ⟨d1, d2, d3, d4, d5⟩ := dblMod_run acc P tmp tmp2 hac3 hac4 hac5 h34 h35 h45 (t.setSc 741 j) n e710
    (by show V (t.ar acc) n < V (t.ar P) n; rw [kP]; exact hacc) (by show 2 * V (t.ar P) n ≤ 2 ^ n; rw [kP]; exact hP)
  change V _ n = (2 * V (t.ar acc) n) % V (t.ar P) n at d2
  rw [kP, c2] at d2
  change Cells n _ (t.ar acc) at d1
  generalize hD : Cmd.run (dblMod acc P tmp tmp2) (t.setSc 741 j) = s1 at d1 d2 d3 d4 d5
  have n740 : ¬ ZB 740 := by simp [ZB, ZA, ZC]
  have n710 : ¬ ZB 710 := by simp [ZB, ZA, ZC]
  have s740 : s1.1.sc 740 = n - j := by rw [d4 740 n740]; simpa [St.setSc] using c3
  have s710 : s1.1.sc 710 = n := by rw [d4 710 n710]; exact e710
  have sB : s1.1.ar B = st.ar B := by
    rw [d3 B (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])]; exact kB
  have sA : s1.1.ar A = st.ar A := by
    rw [d3 A (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])]; exact kA
  have sP : s1.1.ar P = st.ar P := by
    rw [d3 P (by intro h; rcases h with h | h | h <;> simp_all [Ne.symm])]; exact kP
  have dstep := T_step (st.ar B) n j hj
  have cZM : ∀ y, ¬ ZM y → y ≠ 740 → y ≠ 742 → y ≠ 741 → s1.1.sc y = st.sc y := by
    intro y hy _ _ h741
    rw [d4 y (fun h => hy (Or.inl h))]
    simp [St.setSc, Function.update_apply, h741]
    exact c6 y hy
  have fin740 : ∀ (u : St) (v : ℕ), u.sc 740 = n - j → (u.setSc 740 (u.sc 740 - 1)).sc 740 = n - (j + 1) := by
    intro u v h; simp only [St.setSc_sc, Function.update_self]; rw [h, Nat.sub_sub]
  by_cases hx : st.ar B (n - j) = 0
  · have hb : bt (st.ar B) (n - j) = 0 := by simp [bt, hx]
    simp only [r, mulBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_decr, hD, s740, sB, hx,
      Nat.add_zero, St.setSc_sc, Function.update_self, ↓reduceIte, ite_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact d1.trans c1
    · rw [dstep, hb, add_zero]
      have := mod_step (V (st.ar A) n) (V (st.ar B) n / 2 ^ (n - j)) 0 (V (st.ar P) n)
      simp only [zero_mul, add_zero] at this
      exact (d2.trans this)
    · rw [Function.update_of_ne (by norm_num : (740:ℕ) ≠ 742), s740, Nat.sub_sub]
    · rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740), Function.update_of_ne (by norm_num : (710:ℕ) ≠ 742)]
      exact s710
    · have c5' := ArK.trans (D := fun a => a = acc ∨ a = tmp ∨ a = tmp2) (D' := fun a => a = acc ∨ a = tmp ∨ a = tmp2) c5 d3
      exact c5'.mono (fun a ha => by rcases ha with h | h <;> exact h)
    · intro y hy
      have n740' : y ≠ 740 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have n742' : y ≠ 742 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have n741' : y ≠ 741 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      show Function.update (Function.update s1.1.sc 742 0) 740 _ y = st.sc y
      rw [Function.update_of_ne n740', Function.update_of_ne n742']
      exact cZM y hy n740' n742' n741'
    · omega
  · have hb : bt (st.ar B) (n - j) = 1 := by simp [bt, hx]
    have h710' : (s1.1.setSc 742 (st.ar B (n - j))).sc 710 = n := by
      simp only [St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 742)]; exact s710
    obtain ⟨e1, e2, e3, e4, e5⟩ := addMod_run acc A P tmp hac1 hac3 hac4 h13 h34 h14
      (s1.1.setSc 742 (st.ar B (n - j))) n h710'
      (by show V (s1.1.ar acc) n < V (s1.1.ar P) n; rw [d2, sP]; exact Nat.mod_lt _ hPpos)
      (by show V (s1.1.ar A) n < V (s1.1.ar P) n; rw [sA, sP]; exact hA)
      (by show 2 * V (s1.1.ar P) n ≤ 2 ^ n; rw [sP]; exact hP)
    change Cells n _ (s1.1.ar acc) at e1
    change V _ n = (V (s1.1.ar acc) n + V (s1.1.ar A) n) % V (s1.1.ar P) n at e2
    rw [d2, sA, sP] at e2
    generalize hM : Cmd.run (addMod acc A P tmp) (s1.1.setSc 742 (st.ar B (n - j))) = s3 at e1 e2 e3 e4 e5
    have s3740 : s3.1.sc 740 = n - j := by
      rw [e4 740 n740]; simp only [St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (740:ℕ) ≠ 742)]; exact s740
    simp only [r, mulBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_decr, hD, s740, sB, hx,
      Nat.add_zero, St.setSc_sc, Function.update_self, ↓reduceIte, ite_true, hM, if_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact e1.trans (d1.trans c1)
    · rw [dstep, hb]
      have := mod_step (V (st.ar A) n) (V (st.ar B) n / 2 ^ (n - j)) 1 (V (st.ar P) n)
      rw [Nat.mod_add_mod] at e2
      exact e2.trans (by rw [← mod_step (V (st.ar A) n) (V (st.ar B) n / 2 ^ (n - j)) 1 (V (st.ar P) n)]; simp)
    · rw [s3740, Nat.sub_sub]
    · rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740)]
      rw [e4 710 n710]; simp only [St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 742)]; exact s710
    · have c5' := ArK.trans (ArK.trans (D := fun a => a = acc ∨ a = tmp ∨ a = tmp2) (D' := fun a => a = acc ∨ a = tmp ∨ a = tmp2) c5 d3)
        (D' := fun a => a = acc ∨ a = tmp) e3
      exact c5'.mono (fun a ha => by
        rcases ha with ((h | h | h) | (h | h | h)) | (h | h) <;> simp [h])
    · intro y hy
      have n740' : y ≠ 740 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have n742' : y ≠ 742 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      have n741' : y ≠ 741 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      show Function.update s3.1.sc 740 _ y = st.sc y
      rw [Function.update_of_ne n740', e4 y (fun h => hy (Or.inl h))]
      show Function.update s1.1.sc 742 _ y = st.sc y
      rw [Function.update_of_ne n742']
      exact cZM y hy n740' n742' n741'
    · omega

theorem mulMod_run (acc A B P tmp tmp2 : ℕ) (hnd : List.Nodup [acc, A, B, P, tmp, tmp2]) (st : St) (n : ℕ)
    (hW : st.sc 710 = n) (hA : V (st.ar A) n < V (st.ar P) n) (hP : 2 * V (st.ar P) n ≤ 2 ^ n) :
    let r := Cmd.run (mulMod acc A B P tmp tmp2) st
    Cells n (r.1.ar acc) (st.ar acc) ∧
    V (r.1.ar acc) n = (V (st.ar A) n * V (st.ar B) n) % V (st.ar P) n ∧
    ArK (fun a => a = acc ∨ a = tmp ∨ a = tmp2) st r.1 ∧ ScKeep ZM st r.1 ∧ r.2 ≤ 300 * n * n + 300 * n + 20 := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run acc st n hW
  generalize hz : Cmd.run (zeroA acc) st = s0 at z1 z2 z3 z4 z5
  have w0 : s0.1.sc 710 = n := by rw [z4 710 (by simp [ZC])]; exact hW
  have kA : s0.1.ar A = st.ar A := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    exact z3 A (fun h => hnd.1.1 h.symm)
  have kB : s0.1.ar B = st.ar B := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    exact z3 B (fun h => hnd.1.2.1 h.symm)
  have kP : s0.1.ar P = st.ar P := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    exact z3 P (fun h => hnd.1.2.2.1 h.symm)
  let st2 : St := s0.1.setSc 740 (s0.1.sc 710)
  let Pj : ℕ → St → Prop := fun j t =>
    Cells n (t.ar acc) (st.ar acc) ∧
    V (t.ar acc) n = (V (st.ar A) n * (V (st.ar B) n / 2 ^ (n - j))) % V (st.ar P) n ∧
    t.sc 740 = n - j ∧ t.sc 710 = n ∧ ArK (fun a => a = acc ∨ a = tmp ∨ a = tmp2) st t ∧ ScKeep ZM st t
  have h0 : Pj 0 st2 := by
    refine ⟨z1, ?_, ?_, ?_, ?_, ?_⟩
    · show V (s0.1.ar acc) n = _
      rw [z2, Nat.sub_zero, Nat.div_eq_of_lt (V_lt _ _)]; simp
    · simp [st2, St.setSc, w0]
    · simp only [st2, St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740)]; exact w0
    · intro a ha; exact z3 a (fun h => ha (Or.inl h))
    · intro y hy
      have h740 : y ≠ 740 := fun h => hy (Or.inr ⟨by omega, by omega⟩)
      show Function.update s0.1.sc 740 _ y = st.sc y
      rw [Function.update_of_ne h740]
      exact z4 y (fun h => hy (Or.inl (Or.inr h)))
  have hstep : ∀ j t, j < st2.sc 710 → Pj j t →
      Pj (j + 1) (Cmd.run (mulBody acc A B P tmp tmp2) (t.setSc 741 j)).1 := by
    intro j t hj ⟨c1, c2, c3, c4, c5, c6⟩
    have h710 : st2.sc 710 = n := by
      simp only [st2, St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740)]; exact w0
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mulBody_step acc A B P tmp tmp2 hnd st t n j (by omega) hW hA hP c1 c2 c3 c4 c5 c6
    exact ⟨b1, b2, b3, b4, b5, b6⟩
  have hI := Cmd.loop_inv (b := 710) (c := 741) (body := mulBody acc A B P tmp tmp2) Pj h0 hstep
  have hC := Cmd.loop_cost_le (b := 710) (c := 741) (body := mulBody acc A B P tmp tmp2) Pj (200 * n + 100) h0 hstep
    (fun j t hj hp => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hp
      exact (mulBody_step acc A B P tmp tmp2 hnd st t n j (by
        have h710 : st2.sc 710 = n := by
          simp only [st2, St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740)]; exact w0
        omega) hW hA hP c1 c2 c3 c4 c5 c6).2.2.2.2.2.2)
  have h710 : st2.sc 710 = n := by
    simp only [st2, St.setSc_sc]; rw [Function.update_of_ne (by norm_num : (710:ℕ) ≠ 740)]; exact w0
  rw [h710] at hI hC
  have hr : Cmd.run (mulMod acc A B P tmp tmp2) st =
      ((Cmd.run (.loop 710 741 (mulBody acc A B P tmp tmp2)) st2).1,
        (s0.2 + (1 + (Cmd.run (.loop 710 741 (mulBody acc A B P tmp tmp2)) st2).2 + 1) + 1)) := by
    simp only [mulMod, Cmd.run_seq, Cmd.run_copy, hz, st2]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
  simp only [r, hr]
  refine ⟨i1, ?_, i5, i6, ?_⟩
  · rw [i2, Nat.sub_self, pow_zero, Nat.div_one]
  · nlinarith [hC, z5]

end ECDLP.L76
