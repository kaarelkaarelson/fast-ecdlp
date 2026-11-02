import ECDLPv2.L115_Sweep
import ECDLPv2.L115_Prep
import ECDLPv2.L113_Out
import ECDLPv2.L113_Num

/-!
# L115 / Long: the long-input counting branch
`longC` = residue sweep, `prepC`, `finishC` (L113): for the engine's value `cnt < 2^n` (with `cnt` the network value mod every `j > 1`), the output array `Q` ends with
`outOf Q = encodeNat cnt`.  Cost: `200 YB^4 + poly(K)`, `K + 2 = M = 2(n+ML+4)+1`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
namespace ECDLP.L115
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A ECDLP.L104B ECDLP.L109 ECDLP.L71 ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A Computability

def longC (S RN RD : ℕ) (U : UParts) (X1 X2 Pa T Q R TM ONE : ℕ) : Cmd :=
  .seq (swpC S RN RD U) (.seq prepC (finishC X1 X2 Pa T Q R TM ONE RN RD))

/-- the cost of `finishC` as in `finish_run` -/
def finB (K n : ℕ) : ℕ :=
  2 * (K * (200 * ((n + 1) * (K + 3) ^ 2) + 7) + 10 * n + 20) + (n * (200 * (n + 1) + 7) + 16 * n + 40) + 2 + (7 * n + 8) + 1

set_option maxRecDepth 20000 in
theorem long_run {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX) (hS : F.Spec)
    (SD : ShapeDataF DB P F T SX TX) (S RN RD X1 X2 Pa Tm Q R TM ONE : ℕ) (hS1 : 1400 ≤ S) (hRN : RN < S) (hRD : RD < S) (hne : RN ≠ RD)
    (hnd : List.Nodup [X1, X2, Pa, Tm, Q, R, TM, ONE, RN, RD])
    (V : ℕ) (Sf : St) {cnt : ℕ}
    (hP : P ((unshift S Sf).sc 0) (unshift S Sf).ar) (hkn : (unshift S Sf).sc 2 < (unshift S Sf).sc 0)
    (R' : F.UniReq V ((unshift S Sf).sc 0))
    (hcnt : ∀ m, 1 < m → ((SD.D m ((unshift S Sf).sc 0) ((unshift S Sf).sc 2) (unshift S Sf).ar).inner.value : ZMod m) = (cnt : ZMod m))
    (hlt : cnt < 2 ^ ((unshift S Sf).sc 0)) :
    let n := (unshift S Sf).sc 0
    let ℓ := ellOf n
    let L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n
    let K := 2 * (n + mlogN K0u ℓ L + 4) - 1
    outOf ((Cmd.run (longC S RN RD (UP' L0X SX TX) X1 X2 Pa Tm Q R TM ONE) Sf).1.ar Q) = encodeNat cnt ∧
    (Cmd.run (longC S RN RD (UP' L0X SX TX) X1 X2 Pa Tm Q R TM ONE) Sf).2 ≤
      200 * YB DB V ^ 4 + ((K + 1) * (2 * (K + 1) + 2) + 14) + finB K ((K + 1) * (K + 1)) + 2 := by
  intro n ℓ L K
  obtain ⟨m1, m2, m3, m4, m5⟩ := swp_run hI hS SD S RN RD hS1 hRN hRD hne V Sf hP hkn R' hcnt
  set r1 := (Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf).1 with hr1
  set ML := mlogN K0u ℓ L with hML
  have hn1 : 1 ≤ n := by omega
  have hK : r1.sc 852 = K + 2 := by rw [m1]; omega
  obtain ⟨p1, p2, p3, p4, p5⟩ := prepC_run r1 K hK
  set r2 := (Cmd.run prepC r1).1 with hr2
  have hDl : deepMult K0u ℓ L ≤ 2 ^ ML := deepMult_le K0u ℓ L
  have hD0 : 0 < deepMult K0u ℓ L := deepMult_pos K0u ℓ L
  have hKK : K + 1 = 2 * (n + ML + 4) := by omega
  have hDn : 2 * deepMult K0u ℓ L ≤ 2 ^ ((K + 1) * (K + 1)) := by
    calc 2 * deepMult K0u ℓ L ≤ 2 * 2 ^ ML := by omega
      _ = 2 ^ (ML + 1) := by ring
      _ ≤ 2 ^ ((K + 1) * (K + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  obtain ⟨f1, f2⟩ := finish_run X1 X2 Pa Tm Q R TM ONE RN RD hnd r2 ((K + 1) * (K + 1)) K cnt (deepMult K0u ℓ L) p1 p2
    (by nlinarith) (fact_lt_pow K)
    (fun m h1 h2 => by rw [p4]; exact (m2 m h1 (by omega)).1)
    (fun m h1 h2 => by rw [p4]; exact (m2 m h1 (by omega)).2)
    (by rw [hKK]; exact hbig_count hDl hlt) (by rw [hKK]; exact hbig_mult hn1 hDl) hD0 hDn
  have hrun : Cmd.run (longC S RN RD (UP' L0X SX TX) X1 X2 Pa Tm Q R TM ONE) Sf =
      ((Cmd.run (finishC X1 X2 Pa Tm Q R TM ONE RN RD) r2).1,
        (Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf).2 + ((Cmd.run prepC r1).2 + (Cmd.run (finishC X1 X2 Pa Tm Q R TM ONE RN RD) r2).2 + 1) + 1) := by
    simp only [longC, Cmd.run_seq]
    rfl
  rw [hrun]
  refine ⟨f1, ?_⟩
  simp only [finB]
  have := f2
  omega

end ECDLP.L115
