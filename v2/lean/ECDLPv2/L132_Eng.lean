import ECDLPv2.L115_Long
import ECDLPv2.L115_Bits
import ECDLPv2.L115_Poly
import ECDLPv2.L109_Real
import ECDLP.L104_Final

/-!
# L115 / Eng: the counting engine branch for the real network
`cntBr r S` runs on a state whose view shifted by `S` is a `FrameIn'` state (built by `checkC; frameW' S`):
short inputs (`len < T1 r`): the count from the table `lookCnt`, written in binary (`toBitsC`) and length-tagged (`lenC`) in array `2`;
long inputs: `longC` (residue sweep of the real engine, bignum CRT, exact division, `lenC`) with the same output array `2`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000
noncomputable section
namespace ECDLP.L132
open ECDLP.L115 Finset Factoring.Aux Ex ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L96 ECDLP.L92 ECDLP.L104 ECDLP.L104R ECDLP.L61 ECDLP
  ECDLP.L85A ECDLP.L85B ECDLP.L88 ECDLP.L60 Factoring.Aux.Copied Factoring.Aux.Copied.PLib Uni ECDLP.L71 ECDLP.L109 ECDLP.L113 Computability

def cntShortG (r S T w : ℕ) : Cmd :=
  .seq ((lookCnt (r + 1) T).shift S) (.seq (.copy 860 (S + 3)) (.seq (toBitsC 2 w) (lenC 2)))

def shortBG (T w : ℕ) : ℕ := (38 * T + 1) + 1 + (w * (14 * 2 ^ w + 51) + 3) + (7 * w + 8) + 4

theorem cntShortG_run (r S T w : ℕ) (x : Inst) (τ : List Bool) (Sf1 : St)
    (hF : FrameIn r (redInp x τ) (unshift S Sf1)) (hlt : (redInp x τ).len < T) (hτ : τ.length ≤ (redInp x τ).len)
    (hw : Zc (r + 1) x τ < 2 ^ w) :
    outOf ((Cmd.run (cntShortG r S T w) Sf1).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧
      (Cmd.run (cntShortG r S T w) Sf1).2 ≤ shortBG T w := by
  obtain ⟨u1, c1, lo1⟩ := run_shift S (lookCnt (r + 1) T) Sf1
  obtain ⟨l1, l2⟩ := lookCnt_spec r T x τ (unshift S Sf1) hF hlt hτ
  rw [← u1] at l1
  generalize hA : Cmd.run ((lookCnt (r + 1) T).shift S) Sf1 = A at u1 c1 lo1 l1
  have hA3 : A.1.sc (S + 3) = Zc (r + 1) x τ := l1
  set B := A.1.setSc 860 (A.1.sc (S + 3)) with hB
  have hB860 : B.sc 860 = Zc (r + 1) x τ := by simp [hB, hA3]
  obtain ⟨t1, t2, t3, t4, t5⟩ := toBitsC_run 2 w B (Zc (r + 1) x τ) hB860 hw
  set C := (Cmd.run (toBitsC 2 w) B).1 with hC
  have o1 := lenC_out 2 C w t2
  obtain ⟨-, -, -, -, o2⟩ := lenC_run 2 C w t2
  have hrun : Cmd.run (cntShortG r S T w) Sf1 = ((Cmd.run (lenC 2) C).1,
      A.2 + (1 + ((Cmd.run (toBitsC 2 w) B).2 + (Cmd.run (lenC 2) C).2 + 1) + 1) + 1) := by
    simp only [cntShortG, Cmd.run_seq, Cmd.run_copy, hA]
    rfl
  rw [hrun]
  have hc1 : A.2 = (Cmd.run (lookCnt (r + 1) T) (unshift S Sf1)).2 := c1
  have hmul : w * (14 * Zc (r + 1) x τ + 51) ≤ w * (14 * 2 ^ w + 51) :=
    Nat.mul_le_mul_left _ (by omega)
  refine ⟨?_, ?_⟩
  · simp only
    rw [o1, t1]
  · simp only [shortBG]
    omega

def cntShort (r S : ℕ) : Cmd := cntShortG r S (T1 r) (r * T1 r + 1)

def cntLong (r S : ℕ) : Cmd := longC S 110 111 (realU r) 100 101 102 103 2 104 105 106

def cntBr (r S : ℕ) : Cmd := .seq (.setK (S + 22) (T1 r)) (.ifLt (S + 0) (S + 22) (cntShort r S) (cntLong r S))

def shortB (r : ℕ) : ℕ := shortBG (T1 r) (r * T1 r + 1)

theorem short_arith (r T len : ℕ) (h : len < T) : r * (len + 1) + 1 ≤ r * T + 1 := by
  have : r * (len + 1) ≤ r * T := Nat.mul_le_mul_left _ h
  omega

theorem pow_step (r len T Zv : ℕ) (h : len < T) (hz : Zv < 2 ^ (r * (len + 1) + 1)) : Zv < 2 ^ (r * T + 1) :=
  lt_of_lt_of_le hz (Nat.pow_le_pow_right Nat.zero_lt_two (short_arith r T len h))

theorem cntShort_run (r S : ℕ) (hS : 1400 ≤ S) (x : Inst) (τ : List Bool) (hG : Good (r + 1) x τ) (Sf1 : St)
    (hF : FrameIn r (redInp x τ) (unshift S Sf1)) (hlt : (redInp x τ).len < T1 r) :
    outOf ((Cmd.run (cntShort r S) Sf1).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧ (Cmd.run (cntShort r S) Sf1).2 ≤ shortB r := by
  have hτ : τ.length ≤ (redInp x τ).len := by simp [EdgeInp.len, redInp]; omega
  have hzc := zc_short r x τ hG
  have hw := pow_step r _ (T1 r) _ hlt hzc
  exact cntShortG_run r S (T1 r) (r * T1 r + 1) x τ Sf1 hF hlt hτ hw

end ECDLP.L132
end
