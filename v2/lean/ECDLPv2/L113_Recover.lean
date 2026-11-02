import ECDLPv2.L113_Div
import ECDLPv2.L113_Num

/-!
# L113 / Recover: from the two residue arrays to the bits of `c`
`recoverC` = `crtC` on the residues of `N = D * c`, `crtC` on the residues of `D`, then exact division.
`recover_run` : if `RN[m] = (D c) mod m`, `RD[m] = D mod m` for `2 ≤ m ≤ K+1` and the central-binomial hypotheses hold,
the array `Q` holds the bits of `c` (cells `1..n`), at a cost polynomial in `n, K`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

def recoverC (X1 X2 P T Q R TM ONE RN RD : ℕ) : Cmd :=
  .seq (crtC X1 P T RN) (.seq (crtC X2 P T RD) (divC X1 X2 Q R TM ONE))

theorem recover_run (X1 X2 P T Q R TM ONE RN RD : ℕ) (hnd : List.Nodup [X1, X2, P, T, Q, R, TM, ONE, RN, RD])
    (st : St) (n K c D : ℕ) (hW : st.sc 710 = n) (hK : st.sc 801 = K) (hn : 1 ≤ n) (hfac : (K + 1).factorial < 2 ^ n)
    (hRN : ∀ m, 2 ≤ m → m ≤ K + 1 → st.ar RN m = (D * c) % m) (hRD : ∀ m, 2 ≤ m → m ≤ K + 1 → st.ar RD m = D % m)
    (hbN : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ K + 1 → i ∣ Y) → D * c < Y)
    (hbD : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ K + 1 → i ∣ Y) → D < Y)
    (hD0 : 0 < D) (hDn : 2 * D ≤ 2 ^ n) :
    V ((Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).1.ar Q) n = c ∧
    (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).1.sc 710 = n ∧
    (Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st).2 ≤
      2 * (K * (200 * ((n + 1) * (K + 3) ^ 2) + 7) + 10 * n + 20) + (n * (200 * (n + 1) + 7) + 16 * n + 40) + 2 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨a12, a13, a14, a15, a16, a17, a18, a19, a110⟩, ⟨a23, a24, a25, a26, a27, a28, a29, a210⟩,
    ⟨a34, a35, a36, a37, a38, a39, a310⟩, ⟨a45, a46, a47, a48, a49, a410⟩, ⟨a56, a57, a58, a59, a510⟩,
    ⟨a67, a68, a69, a610⟩, ⟨a78, a79, a710⟩, ⟨a89, a810⟩, a910, -⟩ := hnd
  -- first CRT
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := crtC_run X1 P T RN a13 a14 a34 (Ne.symm a19) (Ne.symm a39) (Ne.symm a49) st n K (D * c) hW hK hn hfac hRN hbN
  generalize hr1 : Cmd.run (crtC X1 P T RN) st = r1 at c1 c2 c3 c4 c5 c6
  have w1 : r1.1.sc 710 = n := by rw [c5 710 (by unfold Z1 Z0; omega)]; exact hW
  have k1 : r1.1.sc 801 = K := by rw [c5 801 (by unfold Z1 Z0; omega)]; exact hK
  -- second CRT
  have rd1 : ∀ m, 2 ≤ m → m ≤ K + 1 → r1.1.ar RD m = D % m := fun m h1 h2 => by
    rw [c4 RD (Ne.symm a110) (Ne.symm a310) (Ne.symm a410), hRD m h1 h2]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := crtC_run X2 P T RD a23 a24 a34 (Ne.symm a210) (Ne.symm a310) (Ne.symm a410) r1.1 n K D w1 k1 hn hfac rd1 hbD
  generalize hr2 : Cmd.run (crtC X2 P T RD) r1.1 = r2 at d1 d2 d3 d4 d5 d6
  have w2 : r2.1.sc 710 = n := by rw [d5 710 (by unfold Z1 Z0; omega)]; exact w1
  -- the division
  have n1 : V (r2.1.ar X1) n = D * c := by
    rw [d4 X1 a12 a13 a14]; exact c1
  have n2 : V (r2.1.ar X2) n = D := d1
  obtain ⟨e1, e2, e3, e4, e5⟩ := divC_run X1 X2 Q R TM ONE a67 (Ne.symm a26) a68 (Ne.symm a27) a56 a57 a16 a17 (Ne.symm a78) a58 a15 a25 a18 a28 r2.1 n w2 hn
    (by rw [n2]; exact hD0) (by rw [n2]; exact hDn)
  have hq : V ((Cmd.run (divC X1 X2 Q R TM ONE) r2.1).1.ar Q) n = c := by
    rw [e1, n1, n2]; exact Nat.mul_div_cancel_left c hD0
  have hrun : Cmd.run (recoverC X1 X2 P T Q R TM ONE RN RD) st = ((Cmd.run (divC X1 X2 Q R TM ONE) r2.1).1,
      r1.2 + (r2.2 + (Cmd.run (divC X1 X2 Q R TM ONE) r2.1).2 + 1) + 1) := by
    simp only [recoverC, Cmd.run_seq, hr1, hr2]
  rw [hrun]
  refine ⟨hq, ?_, ?_⟩
  · simp only
    rw [e4 710 (by unfold Zd ZK ZC; omega)]; exact w2
  simp only
  have := c6; have := d6; have := e5; omega

end ECDLP.L113
