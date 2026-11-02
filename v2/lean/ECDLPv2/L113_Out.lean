import ECDLPv2.L113_Recover

/-!
# L113 / Out: the output writer
`encodeNat c` is the little-endian binary of `c` without leading (high) zeros, i.e. exactly the list `outOf` reads from an array whose
cell `0` is the bit length and cells `1..ℓ` are the bits.  `lenC Q` computes the bit length of the number in `Q` (scalar 840) and stores it in `Q[0]`:
`outOf (Q after) = encodeNat (V Q n)` (`lenC_run`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76 Computability

theorem encodeNat_bit (b : Bool) (m : ℕ) (hm : 0 < m) : encodeNat (Nat.bit b m) = b :: encodeNat m := by
  unfold encodeNat
  rw [← Num.ofNat'_eq, ← Num.ofNat'_eq, Num.ofNat'_bit]
  obtain ⟨p, hp⟩ : ∃ p : PosNum, Num.ofNat' m = Num.pos p := by
    cases h : Num.ofNat' m with
    | zero =>
      exfalso
      have : (Num.ofNat' m : ℕ) = m := by rw [Num.ofNat'_eq]; simp
      rw [h] at this; simp at this; omega
    | pos p => exact ⟨p, rfl⟩
  rw [hp]
  cases b <;> simp [encodeNum, encodePosNum, Num.bit0, Num.bit1]

theorem encodeNat_eq_ofFn : ∀ c : ℕ, encodeNat c = List.ofFn (fun i : Fin (Nat.size c) => c.testBit i)
  | c => by
    by_cases h0 : c = 0
    · subst h0; simp [encodeNat, encodeNum]
    by_cases h1 : c = 1
    · subst h1; rfl
    have hc : 0 < c / 2 := by omega
    have ih := encodeNat_eq_ofFn (c / 2)
    have hbit : Nat.bit (decide (c % 2 = 1)) (c / 2) = c := by
      rw [Nat.bit_val]; by_cases h : c % 2 = 1 <;> simp [h] <;> omega
    have hsz : Nat.size c = Nat.size (c / 2) + 1 := by
      conv_lhs => rw [← hbit]
      rw [Nat.size_bit (by omega)]
    have e : encodeNat c = decide (c % 2 = 1) :: encodeNat (c / 2) := by
      conv_lhs => rw [← hbit]
      exact encodeNat_bit _ _ hc
    rw [e, ih]
    -- cast the length
    have : ∀ (k : ℕ) (hk : Nat.size c = k + 1), List.ofFn (fun i : Fin (Nat.size c) => c.testBit i) =
        c.testBit 0 :: List.ofFn (fun i : Fin k => c.testBit (i + 1)) := by
      intro k hk
      rw [List.ofFn_congr hk, List.ofFn_succ]; rfl
    rw [this _ hsz]
    congr 1
    · simp [Nat.testBit_zero]
    · congr 1; funext i; rw [Nat.testBit_succ]
termination_by c => c

def lenBody (Q : ℕ) : Cmd := .seq (.rd 842 Q 841 1) (.ifZero 842 .skip (.seq (.copy 840 841) (.incr 840)))

/-- scalar 840 := bit length of the number in `Q`; then `Q[0] := that length` -/
def lenC (Q : ℕ) : Cmd :=
  .seq (.setK 840 0) (.seq (.loop 710 841 (lenBody Q)) (.seq (.setK 843 0) (.wr Q 843 0 840)))

theorem lenBody_step (Q : ℕ) (t : St) (i : ℕ) :
    let r := Cmd.run (lenBody Q) (t.setSc 841 i)
    r.1.sc 840 = (if t.ar Q (i + 1) = 0 then t.sc 840 else i + 1) ∧
    (∀ y, y ≠ 840 → y ≠ 841 → y ≠ 842 → r.1.sc y = t.sc y) ∧ r.1.ar = t.ar ∧ r.2 ≤ 6 := by
  by_cases h : t.ar Q (i + 1) = 0
  · simp [lenBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, St.setSc, h, Function.update_apply]
    intro y h1 h2 h3; simp [h1, h2, h3]
  · simp [lenBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_copy, Cmd.run_incr, St.setSc, h, Function.update_apply]
    intro y h1 h2 h3; simp [h1, h2, h3]

theorem size_step (f : ℕ → ℕ) (i : ℕ) :
    Nat.size (V f (i + 1)) = (if f (i + 1) = 0 then Nat.size (V f i) else i + 1) := by
  rw [V_snoc]
  by_cases h : f (i + 1) = 0
  · simp [bt, h]
  · have hb : bt f (i + 1) = 1 := by simp [bt, h]
    rw [hb, if_neg h, one_mul]
    have hlt := V_lt f i
    apply le_antisymm
    · exact Nat.size_le.mpr (by rw [pow_succ]; omega)
    · exact Nat.lt_size.mpr (by omega)

theorem lenC_run (Q : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    (Cmd.run (lenC Q) st).1.ar Q 0 = Nat.size (V (st.ar Q) n) ∧
    (∀ i, 1 ≤ i → (Cmd.run (lenC Q) st).1.ar Q i = st.ar Q i) ∧
    (∀ a, a ≠ Q → (Cmd.run (lenC Q) st).1.ar a = st.ar a) ∧
    (∀ y, ¬ (840 ≤ y ∧ y ≤ 843) → (Cmd.run (lenC Q) st).1.sc y = st.sc y) ∧
    (Cmd.run (lenC Q) st).2 ≤ 7 * n + 8 := by
  set s1 := st.setSc 840 0 with hs1
  have w1 : s1.sc 710 = n := by simp [hs1, St.setSc, hW]
  let P : ℕ → St → Prop := fun i t => t.sc 840 = Nat.size (V (st.ar Q) i) ∧
    (∀ y, y ≠ 840 → y ≠ 841 → y ≠ 842 → t.sc y = st.sc y) ∧ t.ar = st.ar
  have h0 : P 0 s1 := ⟨by simp [hs1, St.setSc, V, numCells], fun y h1 h2 h3 => by simp [hs1, St.setSc, Function.update_of_ne h1], rfl⟩
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (lenBody Q) (t.setSc 841 i)).1 ∧ (Cmd.run (lenBody Q) (t.setSc 841 i)).2 ≤ 6 := by
    intro i t ⟨p1, p2, p3⟩
    obtain ⟨r1, r2, r3, r4⟩ := lenBody_step Q t i
    refine ⟨⟨?_, fun y h1 h2 h3 => by rw [r2 y h1 h2 h3, p2 y h1 h2 h3], by rw [r3, p3]⟩, r4⟩
    rw [r1, p1, p3, size_step]
  have hI := Cmd.loop_inv (b := 710) (c := 841) (body := lenBody Q) (st := s1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 710) (c := 841) (body := lenBody Q) (st := s1) P 6 h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  rw [w1] at hI hC
  obtain ⟨a1, a2, a3⟩ := hI
  set s2 := (Cmd.run (.loop 710 841 (lenBody Q)) s1).1 with hs2
  have hr : Cmd.run (lenC Q) st = (((s2.setSc 843 0).setAr Q ((s2.setSc 843 0).sc 843 + 0) ((s2.setSc 843 0).sc 840)),
      1 + ((Cmd.run (.loop 710 841 (lenBody Q)) s1).2 + (1 + 1 + 1) + 1) + 1) := by
    simp only [lenC, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]; rfl
  rw [hr]
  have e840 : (s2.setSc 843 0).sc 840 = Nat.size (V (st.ar Q) n) := by simp [St.setSc, a1]
  have e843 : (s2.setSc 843 0).sc 843 = 0 := by simp [St.setSc]
  refine ⟨?_, fun i hi => ?_, fun a ha => ?_, fun y hy => ?_, ?_⟩
  · simp [St.setAr, St.putAr, e843, e840, a3, a1]
  · simp [St.setAr, St.putAr, e843, Function.update_apply, a3, show i ≠ 0 by omega]
  · simp [St.setAr, St.putAr, Function.update_of_ne ha, a3]
  · have h1 : y ≠ 840 := fun h => hy ⟨by omega, by omega⟩
    have h2 : y ≠ 841 := fun h => hy ⟨by omega, by omega⟩
    have h3 : y ≠ 842 := fun h => hy ⟨by omega, by omega⟩
    have h4 : y ≠ 843 := fun h => hy ⟨by omega, by omega⟩
    simp [St.setAr, St.putAr, St.setSc, Function.update_of_ne h4, a2 y h1 h2 h3]
  · simp only; omega

theorem lenC_out (Q : ℕ) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    outOf ((Cmd.run (lenC Q) st).1.ar Q) = encodeNat (V (st.ar Q) n) := by
  obtain ⟨a1, a2, -, -, -⟩ := lenC_run Q st n hW
  set c := V (st.ar Q) n with hc
  have hsz : Nat.size c ≤ n := Nat.size_le.mpr (V_lt _ _)
  rw [encodeNat_eq_ofFn]
  unfold outOf
  rw [List.ofFn_congr a1]
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  show decide (((Cmd.run (lenC Q) st).1.ar Q ((i : ℕ) + 1)) ≠ 0) = c.testBit i
  rw [a2 (i + 1) (by omega)]
  have hv := V_div_mod2 (st.ar Q) n i (by have := i.2; omega)
  rw [← hc] at hv
  rw [Nat.testBit_eq_decide_div_mod_eq, hv]
  unfold bt
  by_cases h : st.ar Q (i + 1) = 0 <;> simp [h]

/-- the whole tail: residue arrays -> `outOf` of the output array is `encodeNat c` -/
def finishC (X1 X2 P T Q R TM ONE RN RD : ℕ) : Cmd := .seq (recoverC X1 X2 P T Q R TM ONE RN RD) (lenC Q)

theorem finish_run (X1 X2 P T Q R TM ONE RN RD : ℕ) (hnd : List.Nodup [X1, X2, P, T, Q, R, TM, ONE, RN, RD])
    (st : St) (n K c D : ℕ) (hW : st.sc 710 = n) (hK : st.sc 801 = K) (hn : 1 ≤ n) (hfac : (K + 1).factorial < 2 ^ n)
    (hRN : ∀ m, 2 ≤ m → m ≤ K + 1 → st.ar RN m = (D * c) % m) (hRD : ∀ m, 2 ≤ m → m ≤ K + 1 → st.ar RD m = D % m)
    (hbN : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ K + 1 → i ∣ Y) → D * c < Y)
    (hbD : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ K + 1 → i ∣ Y) → D < Y)
    (hD0 : 0 < D) (hDn : 2 * D ≤ 2 ^ n) :
    outOf ((Cmd.run (finishC X1 X2 P T Q R TM ONE RN RD) st).1.ar Q) = encodeNat c ∧
    (Cmd.run (finishC X1 X2 P T Q R TM ONE RN RD) st).2 ≤
      2 * (K * (200 * ((n + 1) * (K + 3) ^ 2) + 7) + 10 * n + 20) + (n * (200 * (n + 1) + 7) + 16 * n + 40) + 2 + (7 * n + 8) + 1 := by
  obtain ⟨r1, r2, r3⟩ := recover_run X1 X2 P T Q R TM ONE RN RD hnd st n K c D hW hK hn hfac hRN hRD hbN hbD hD0 hDn
  have hrun : Cmd.run (finishC X1 X2 P T Q R TM ONE RN RD) st =
      ((Cmd.run (lenC Q) (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).1).1,
       (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).2 +
         (Cmd.run (lenC Q) (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).1).2 + 1) := by
    simp only [finishC, Cmd.run_seq]
  rw [hrun]
  obtain ⟨-, -, -, -, l5⟩ := lenC_run Q (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).1 n r2
  refine ⟨?_, ?_⟩
  · simp only
    rw [lenC_out Q _ n r2, r1]
  · simp only; omega

end ECDLP.L113
