import ECDLP.L102_Str

/-!
# L102 / Loops: the small commands of the m = 1 oracle and their run lemmas
Scalars: `C=11` loop counter, `W=10` (size p), `BT=12`, `PW=13`, `NN=14`, `TMP=15`, `SCR=16`, `BND=17`, `RES=18`,
`AB=19`, `BB=20`, `F=21`, `D=22`, `T1=23`, `T2=24`, `W1=26`.
-/
namespace ECDLP.L102
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L71

/-! ### Stage 1: `W := size (numCells (ar 0) 1 ℓ)` -/

def body1 : Cmd := .seq (.rd 12 0 11 1) (.ifZero 12 .skip (.seq (.copy 10 11) (.incr 10)))

def stage1 : Cmd := .seq (.setK 10 0) (.loop 0 11 body1)

theorem body1_sc (t : St) (j : ℕ) :
    (Cmd.run body1 (t.setSc 11 j)).1.sc 10 = (if t.ar 0 (j + 1) = 0 then t.sc 10 else j + 1) ∧
    (Cmd.run body1 (t.setSc 11 j)).2 ≤ 6 := by
  by_cases h : t.ar 0 (j + 1) = 0
  · simp [body1, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Function.update_apply, h]
  · simp [body1, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_copy, Cmd.run_incr, Function.update_apply, h]

theorem body1_ar (t : St) (j : ℕ) : (Cmd.run body1 (t.setSc 11 j)).1.ar = t.ar := by
  funext a; exact Cmd.run_ar_frame _ _ a (by simp [body1, Cmd.war])

theorem stage1_run (s : St) :
    (Cmd.run stage1 s).1.sc 10 = Nat.size (numCells (s.ar 0) 1 (s.sc 0)) ∧ (Cmd.run stage1 s).1.ar = s.ar ∧
    (∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → (Cmd.run stage1 s).1.sc z = s.sc z) ∧ (Cmd.run stage1 s).2 ≤ 7 * s.sc 0 + 3 := by
  have hrun : Cmd.run stage1 s = ((Cmd.run (.loop 0 11 body1) (s.setSc 10 0)).1,
      1 + (Cmd.run (.loop 0 11 body1) (s.setSc 10 0)).2 + 1) := by
    simp only [stage1, Cmd.run_seq, Cmd.run_setK]
  have h0 : (s.setSc 10 0).sc 0 = s.sc 0 := by simp [St.setSc]
  let P : ℕ → St → Prop := fun j t => t.sc 10 = Nat.size (numCells (s.ar 0) 1 j) ∧ t.ar = s.ar
  have hP0 : P 0 (s.setSc 10 0) := by simp [P, numCells, St.setSc]
  have hstep : ∀ j t, j < (s.setSc 10 0).sc 0 → P j t → P (j + 1) (Cmd.run body1 (t.setSc 11 j)).1 := by
    intro j t _ ⟨h1, h2⟩
    refine ⟨?_, by rw [body1_ar, h2]⟩
    rw [(body1_sc t j).1, size_numCells_succ, Nat.add_comm 1 j, h1, h2]
  have hI := Cmd.loop_inv (b := 0) (c := 11) (body := body1) P hP0 hstep
  have hC := Cmd.loop_cost_le (b := 0) (c := 11) (body := body1) P 6 hP0 hstep
    (fun j t _ _ => (body1_sc t j).2)
  rw [h0] at hI hC
  rw [hrun]
  refine ⟨hI.1, hI.2, fun z h1 h2 h3 => ?_, by show 1 + _ + 1 ≤ _; omega⟩
  show (Cmd.run (.loop 0 11 body1) (s.setSc 10 0)).1.sc z = s.sc z
  rw [Cmd.run_sc_frame (.loop 0 11 body1) (s.setSc 10 0) z (by simp [body1, Cmd.wsc]; omega)]
  simp [St.setSc, h1]

/-! ### Stage 2: `NN := numCells (ar 9) 1 (size ℓ)`, `PW := 2^(size ℓ)` -/

def body2 : Cmd := .ifLt 0 13 .skip (.seq (.rd 12 9 11 1) (.seq (.ifZero 12 .skip (addTo 14 13 16))
  (.seq (.copy 15 13) (addTo 13 15 16))))

def stage2 : Cmd := .seq (.setK 13 1) (.seq (.setK 14 0) (.loop 0 11 body2))

theorem addTo_1 (x y t : ℕ) (h : [x, y, t].Nodup) (st : St) :
    (Cmd.run (addTo x y t) st).1 = (st.setSc x (st.sc x + st.sc y)).setSc t 0 := (run_addTo h st).1
theorem addTo_2 (x y t : ℕ) (h : [x, y, t].Nodup) (st : St) :
    (Cmd.run (addTo x y t) st).2 = 2 * st.sc y + 5 := (run_addTo h st).2

theorem body2_sc (t : St) (j : ℕ) :
    (Cmd.run body2 (t.setSc 11 j)).1.sc 13 = (if t.sc 0 < t.sc 13 then t.sc 13 else t.sc 13 + t.sc 13) ∧
    (Cmd.run body2 (t.setSc 11 j)).1.sc 14 = (if t.sc 0 < t.sc 13 then t.sc 14 else
      (if t.ar 9 (j + 1) = 0 then t.sc 14 else t.sc 14 + t.sc 13)) ∧
    (Cmd.run body2 (t.setSc 11 j)).2 ≤ 4 * t.sc 13 + 25 := by
  have a1 := addTo_1 14 13 16 (by decide)
  have a2 := addTo_2 14 13 16 (by decide)
  have b1 := addTo_1 13 15 16 (by decide)
  have b2 := addTo_2 13 15 16 (by decide)
  by_cases c1 : t.sc 0 < t.sc 13
  · simp [body2, Cmd.run_ifLt, Cmd.run_skip, c1]
  · by_cases c2 : t.ar 9 (j + 1) = 0
    · simp [body2, Cmd.run_seq, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_copy, Cmd.run_skip, a1, a2, b1, b2,
        Function.update_apply, c1, c2]
      omega
    · simp [body2, Cmd.run_seq, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_copy, Cmd.run_skip, a1, a2, b1, b2,
        Function.update_apply, c1, c2]
      omega

theorem body2_ar (t : St) (j : ℕ) : (Cmd.run body2 (t.setSc 11 j)).1.ar = t.ar := by
  funext a; exact Cmd.run_ar_frame _ _ a (by simp [body2, addTo, Cmd.seqs, Cmd.war])

theorem body2_sc0 (t : St) (j : ℕ) : (Cmd.run body2 (t.setSc 11 j)).1.sc 0 = t.sc 0 := by
  rw [Cmd.run_sc_frame _ _ 0 (by simp [body2, addTo, Cmd.seqs, Cmd.wsc])]; simp [St.setSc]

theorem pow_size_le (ℓ : ℕ) : 2 ^ Nat.size ℓ ≤ 2 * ℓ + 1 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | h
  · simp
  · have h1 : Nat.size ℓ - 1 < Nat.size ℓ := by have := Nat.size_pos.mpr h; omega
    have := Nat.lt_size.mp h1
    have e : 2 ^ Nat.size ℓ = 2 * 2 ^ (Nat.size ℓ - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.size_pos.mpr h; omega
    omega

theorem stage2_run (s : St) :
    (Cmd.run stage2 s).1.sc 13 = 2 ^ Nat.size (s.sc 0) ∧
    (Cmd.run stage2 s).1.sc 14 = numCells (s.ar 9) 1 (Nat.size (s.sc 0)) ∧ (Cmd.run stage2 s).1.ar = s.ar ∧
    (∀ z, z ≠ 13 → z ≠ 14 → z ≠ 11 → z ≠ 12 → z ≠ 15 → z ≠ 16 → (Cmd.run stage2 s).1.sc z = s.sc z) ∧
    (Cmd.run stage2 s).2 ≤ s.sc 0 * (8 * s.sc 0 + 30) + 6 := by
  set ℓ := s.sc 0 with hℓ
  set J := Nat.size ℓ with hJ
  have hJl : J ≤ ℓ := by rw [hJ, Nat.size_le]; exact Nat.lt_two_pow_self
  have hJ2 : ℓ < 2 ^ J := Nat.lt_size_self ℓ
  have hJ3 : 2 ^ J ≤ 2 * ℓ + 1 := pow_size_le ℓ
  set s2 := (s.setSc 13 1).setSc 14 0 with hs2
  have hrun : Cmd.run stage2 s = ((Cmd.run (.loop 0 11 body2) s2).1, 1 + (1 + (Cmd.run (.loop 0 11 body2) s2).2 + 1) + 1) := by
    simp only [stage2, Cmd.run_seq, Cmd.run_setK, hs2]
  have hs20 : s2.sc 0 = ℓ := by simp [hs2, St.setSc]; exact hℓ.symm
  let P : ℕ → St → Prop := fun j t => t.sc 13 = 2 ^ min j J ∧ t.sc 14 = numCells (s.ar 9) 1 (min j J) ∧
    t.ar = s.ar ∧ t.sc 0 = ℓ
  have hP0 : P 0 s2 := by simp [P, hs2, St.setSc, numCells]; exact hℓ.symm
  have hstep : ∀ j t, j < s2.sc 0 → P j t → P (j + 1) (Cmd.run body2 (t.setSc 11 j)).1 := by
    intro j t _ ⟨h1, h2, h3, h4⟩
    obtain ⟨b1, b2, -⟩ := body2_sc t j
    refine ⟨?_, ?_, by rw [body2_ar, h3], by rw [body2_sc0, h4]⟩
    · rw [b1, h1, h4]
      by_cases hj : j < J
      · have : 2 ^ j ≤ ℓ := Nat.lt_size.mp hj
        rw [if_neg (by rw [min_eq_left hj.le]; omega), min_eq_left hj.le, min_eq_left (by omega : j + 1 ≤ J), pow_succ]; ring
      · have hm : min j J = J := min_eq_right (by omega)
        rw [hm, if_pos (by omega), min_eq_right (by omega)]
    · rw [b2, h1, h2, h3, h4]
      by_cases hj : j < J
      · have : 2 ^ j ≤ ℓ := Nat.lt_size.mp hj
        rw [if_neg (by rw [min_eq_left hj.le]; omega), min_eq_left hj.le, min_eq_left (by omega : j + 1 ≤ J),
          numCells_snoc, Nat.add_comm 1 j]
        by_cases hb : s.ar 9 (j + 1) = 0 <;> simp [hb]
      · have hm : min j J = J := min_eq_right (by omega)
        rw [hm, if_pos (by omega), min_eq_right (by omega)]
  have hI := Cmd.loop_inv (b := 0) (c := 11) (body := body2) P hP0 hstep
  have hC := Cmd.loop_cost_le (b := 0) (c := 11) (body := body2) P (8 * ℓ + 29) hP0 hstep
    (fun j t _ ⟨h1, h2, h3, h4⟩ => by
      have := (body2_sc t j).2.2
      have h5 : 2 ^ min j J ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      omega)
  rw [hs20] at hI hC
  obtain ⟨i1, i2, i3, -⟩ := hI
  rw [min_eq_right hJl] at i1 i2
  rw [hrun]
  refine ⟨i1, i2, i3, fun z h1 h2 h3 h4 h5 h6 => ?_, by show 1 + (1 + _ + 1) + 1 ≤ _; nlinarith⟩
  show (Cmd.run (.loop 0 11 body2) s2).1.sc z = s.sc z
  rw [Cmd.run_sc_frame (.loop 0 11 body2) s2 z (by simp [body2, addTo, Cmd.seqs, Cmd.wsc]; omega)]
  simp [hs2, St.setSc, h1, h2]

/-! ### Stage 3: `RES := [p ≤ 2 y]` by a low-to-high comparison -/

def body3 : Cmd := .seq (.rd 19 0 11 1) (.seq (normB 19) (.seq (.ifZero 11 (.setK 20 0) (.seq (.rd 20 5 11 0) (normB 20)))
  (.ifLt 19 20 (.setK 18 1) (.ifLt 20 19 (.setK 18 0) .skip))))

def stage3 : Cmd := .seq (.setK 18 1) (.loop 0 11 body3)

theorem body3_sc (t : St) (j : ℕ) :
    (Cmd.run body3 (t.setSc 11 j)).1.sc 18 =
      cmpStep (t.sc 18) (if t.ar 0 (j + 1) = 0 then 0 else 1) (if j = 0 ∨ t.ar 5 j = 0 then 0 else 1) ∧
    (Cmd.run body3 (t.setSc 11 j)).2 ≤ 14 := by
  rcases j with _ | j
  · by_cases h1 : t.ar 0 1 = 0 <;>
    simp [body3, normB_run, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_ifLt, Cmd.run_setK, Cmd.run_skip,
      Function.update_apply, cmpStep, h1]
  · by_cases h1 : t.ar 0 (j + 1 + 1) = 0 <;> by_cases h3 : t.ar 5 (j + 1) = 0 <;>
    simp [body3, normB_run, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_ifLt, Cmd.run_setK, Cmd.run_skip,
      Function.update_apply, cmpStep, h1, h3]

theorem body3_ar (t : St) (j : ℕ) : (Cmd.run body3 (t.setSc 11 j)).1.ar = t.ar := by
  funext a; exact Cmd.run_ar_frame _ _ a (by simp [body3, normB, Cmd.war])

theorem stage3_run (s : St) :
    (Cmd.run stage3 s).1.sc 18 = (if numCells (s.ar 0) 1 (s.sc 0) ≤ Bs (s.ar 5) (s.sc 0) then 1 else 0) ∧
    (Cmd.run stage3 s).1.ar = s.ar ∧
    (∀ z, z ≠ 18 → z ≠ 11 → z ≠ 19 → z ≠ 20 → (Cmd.run stage3 s).1.sc z = s.sc z) ∧
    (Cmd.run stage3 s).2 ≤ 15 * s.sc 0 + 3 := by
  set s1 := s.setSc 18 1 with hs1
  have hrun : Cmd.run stage3 s = ((Cmd.run (.loop 0 11 body3) s1).1, 1 + (Cmd.run (.loop 0 11 body3) s1).2 + 1) := by
    simp only [stage3, Cmd.run_seq, Cmd.run_setK, hs1]
  have hs10 : s1.sc 0 = s.sc 0 := by simp [hs1, St.setSc]
  let P : ℕ → St → Prop := fun j t => t.sc 18 = (if numCells (s.ar 0) 1 j ≤ Bs (s.ar 5) j then 1 else 0) ∧ t.ar = s.ar
  have hP0 : P 0 s1 := by simp [P, hs1, St.setSc, numCells, Bs]
  have hstep : ∀ j t, j < s1.sc 0 → P j t → P (j + 1) (Cmd.run body3 (t.setSc 11 j)).1 := by
    intro j t _ ⟨h1, h2⟩
    refine ⟨?_, by rw [body3_ar, h2]⟩
    rw [(body3_sc t j).1, h1, h2, numCells_snoc, Bs_succ]
    have := cmp_step (numCells (s.ar 0) 1 j) (Bs (s.ar 5) j) j _ (numCells_lt _ _ _) (Bs_lt _ _)
      (if s.ar 0 (j + 1) = 0 then 0 else 1) (if j = 0 ∨ s.ar 5 j = 0 then 0 else 1) (by split_ifs <;> simp)
      (by split_ifs <;> simp) rfl
    rw [Nat.add_comm 1 j]
    exact this
  have hI := Cmd.loop_inv (b := 0) (c := 11) (body := body3) P hP0 hstep
  have hC := Cmd.loop_cost_le (b := 0) (c := 11) (body := body3) P 14 hP0 hstep (fun j t _ _ => (body3_sc t j).2)
  rw [hs10] at hI hC
  rw [hrun]
  refine ⟨hI.1, hI.2, fun z h1 h2 h3 h4 => ?_, by show 1 + _ + 1 ≤ _; omega⟩
  show (Cmd.run (.loop 0 11 body3) s1).1.sc z = s.sc z
  rw [Cmd.run_sc_frame (.loop 0 11 body3) s1 z (by simp [body3, normB, Cmd.wsc]; omega)]
  simp [hs1, St.setSc, h1]

/-! ### Stage 4-5: the comparison loop -/

def prep : Cmd := .seq (.copy 26 10) (.seq (.incr 26) (.seq (.setK 21 1) (.seq (.copy 22 10)
  (.ifLt 26 14 (.seq (.setK 21 0) (.setK 17 0)) (.copy 17 14)))))

theorem prep_run (s : St) :
    (Cmd.run prep s).1.sc 21 = (if s.sc 10 + 1 < s.sc 14 then 0 else 1) ∧
    (Cmd.run prep s).1.sc 22 = s.sc 10 ∧
    (Cmd.run prep s).1.sc 17 = (if s.sc 10 + 1 < s.sc 14 then 0 else s.sc 14) ∧
    (Cmd.run prep s).1.sc 10 = s.sc 10 ∧ (Cmd.run prep s).1.sc 18 = s.sc 18 ∧ (Cmd.run prep s).1.sc 0 = s.sc 0 ∧
    (Cmd.run prep s).1.ar = s.ar ∧ (Cmd.run prep s).2 ≤ 12 := by
  by_cases h : s.sc 10 + 1 < s.sc 14
  · simp [prep, Cmd.run_seq, Cmd.run_copy, Cmd.run_incr, Cmd.run_setK, Cmd.run_ifLt, Function.update_apply, h]
  · simp [prep, Cmd.run_seq, Cmd.run_copy, Cmd.run_incr, Cmd.run_setK, Cmd.run_ifLt, Function.update_apply, h]

def body5 : Cmd := .seq (.rd 23 6 11 1) (.seq (normB 23) (.ifLt 11 10
  (.seq (.rd 24 4 22 0) (.seq (normB 24) (.seq (neqSet 23 24 21) (.decr 22)))) (neqSet 23 18 21)))

def stage5 : Cmd := .loop 17 11 body5

theorem body5_sc (t : St) (j : ℕ) :
    (Cmd.run body5 (t.setSc 11 j)).1.sc 21 =
      (if j < t.sc 10 then (if (if t.ar 6 (j + 1) = 0 then 0 else 1) = (if t.ar 4 (t.sc 22) = 0 then 0 else 1)
          then t.sc 21 else 0)
       else (if (if t.ar 6 (j + 1) = 0 then 0 else 1) = t.sc 18 then t.sc 21 else 0)) ∧
    (Cmd.run body5 (t.setSc 11 j)).1.sc 22 = (if j < t.sc 10 then t.sc 22 - 1 else t.sc 22) ∧
    (Cmd.run body5 (t.setSc 11 j)).2 ≤ 20 := by
  by_cases c1 : j < t.sc 10 <;> by_cases c2 : t.ar 6 (j + 1) = 0 <;> by_cases c3 : t.ar 4 (t.sc 22) = 0 <;>
  simp [body5, normB_run, neqSet_run, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifLt, Cmd.run_decr, Function.update_apply,
    c1, c2, c3] <;> (try split_ifs) <;> simp [St.setSc, Function.update_apply] <;> omega

theorem testBit_numCells (f : ℕ → ℕ) : ∀ n o k, k < n → (numCells f o n).testBit k = decide (f (o + k) ≠ 0)
  | 0, o, k, h => by omega
  | n + 1, o, 0, _ => by
      rw [numCells_succ, Nat.testBit_zero]
      by_cases h : f o = 0 <;> simp [h] <;> omega
  | n + 1, o, k + 1, h => by
      rw [numCells_succ, Nat.testBit_succ]
      have e : ((if f o = 0 then 0 else 1) + 2 * numCells f (o + 1) n) / 2 = numCells f (o + 1) n := by
        split_ifs <;> omega
      rw [e, testBit_numCells f n (o + 1) k (by omega), show o + 1 + k = o + (k + 1) by ring]

theorem body5_frame (t : St) (j : ℕ) :
    (Cmd.run body5 (t.setSc 11 j)).1.sc 10 = t.sc 10 ∧ (Cmd.run body5 (t.setSc 11 j)).1.sc 18 = t.sc 18 ∧
    (Cmd.run body5 (t.setSc 11 j)).1.ar = t.ar := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Cmd.run_sc_frame _ _ 10 (by simp [body5, normB, neqSet, Cmd.wsc])]; simp [St.setSc]
  · rw [Cmd.run_sc_frame _ _ 18 (by simp [body5, normB, neqSet, Cmd.wsc])]; simp [St.setSc]
  · funext a; exact Cmd.run_ar_frame _ _ a (by simp [body5, normB, neqSet, Cmd.war])

theorem stage5_cost (s : St) : (Cmd.run stage5 s).2 ≤ s.sc 17 * 21 + 1 :=
  Cmd.loop_cost_le (b := 17) (c := 11) (body := body5) (st := s) (fun _ _ => True) 20 trivial
    (fun _ _ _ _ => trivial) (fun j t _ _ => (body5_sc t j).2.2)

theorem stage5_val (s : St) (e : ℕ → Bool) (W RES : ℕ) (h10 : s.sc 10 = W) (h18 : s.sc 18 = RES) (h22 : s.sc 22 = W)
    (h21 : s.sc 21 = 1) (hRES : RES = 0 ∨ RES = 1)
    (hlow : ∀ q, q < W → e q = decide (s.ar 4 (W - q) ≠ 0)) (hhigh : ∀ q, W ≤ q → (e q = true ↔ RES = 1)) :
    (Cmd.run stage5 s).1.sc 21 = if (∀ q, q < s.sc 17 → ((s.ar 6 (q + 1) ≠ 0) ↔ e q = true)) then 1 else 0 := by
  let φ : ℕ → Prop := fun q => (s.ar 6 (q + 1) ≠ 0) ↔ e q = true
  let P : ℕ → St → Prop := fun j t => t.sc 21 = (if ∀ q, q < j → φ q then 1 else 0) ∧ t.sc 22 = W - j ∧
    t.sc 10 = W ∧ t.sc 18 = RES ∧ t.ar = s.ar
  have hP0 : P 0 s := ⟨by simp [h21], by simp [h22], h10, h18, rfl⟩
  have hstep : ∀ j t, j < s.sc 17 → P j t → P (j + 1) (Cmd.run body5 (t.setSc 11 j)).1 := by
    intro j t _ ⟨p1, p2, p3, p4, p5⟩
    obtain ⟨f1, f2, f3⟩ := body5_frame t j
    obtain ⟨b1, b2, -⟩ := body5_sc t j
    have key : (∀ q, q < j + 1 → φ q) ↔ ((∀ q, q < j → φ q) ∧ φ j) := by
      constructor
      · intro H; exact ⟨fun q hq => H q (by omega), H j (by omega)⟩
      · rintro ⟨H, hj⟩ q hq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
        · exact H q hq
        · subst hq; exact hj
    refine ⟨?_, ?_, by rw [f1, p3], by rw [f2, p4], by rw [f3, p5]⟩
    · rw [b1, p1, p3, p4, p5]
      simp only [key]
      by_cases hj : j < W
      · have hl := hlow j hj
        have e22 : t.sc 22 = W - j := p2
        rw [if_pos hj, e22]
        have hT : ((if s.ar 6 (j + 1) = 0 then 0 else 1) = (if s.ar 4 (W - j) = 0 then 0 else 1)) ↔ φ j := by
          simp only [φ, hl]
          by_cases a1 : s.ar 6 (j + 1) = 0 <;> by_cases a2 : s.ar 4 (W - j) = 0 <;> simp [a1, a2]
        by_cases a4 : φ j
        · rw [if_pos (hT.mpr a4)]
          by_cases a3 : ∀ q, q < j → φ q <;> simp [a3, a4]
        · rw [if_neg (fun h => a4 (hT.mp h))]
          simp [a4]
      · have hl := hhigh j (by omega)
        rw [if_neg hj]
        have hT : ((if s.ar 6 (j + 1) = 0 then 0 else 1) = RES) ↔ φ j := by
          simp only [φ, hl]
          rcases hRES with hR | hR <;> subst hR <;> by_cases a1 : s.ar 6 (j + 1) = 0 <;> simp [a1]
        by_cases a4 : φ j
        · rw [if_pos (hT.mpr a4)]
          by_cases a3 : ∀ q, q < j → φ q <;> simp [a3, a4]
        · rw [if_neg (fun h => a4 (hT.mp h))]
          simp [a4]
    · rw [b2, p2, p3]
      by_cases hj : j < W
      · rw [if_pos hj]; omega
      · rw [if_neg hj]; omega
  have hI := Cmd.loop_inv (b := 17) (c := 11) (body := body5) P hP0 hstep
  exact hI.1

end ECDLP.L102
