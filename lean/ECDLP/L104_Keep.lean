import ECDLP.L104_Setup

/-!
# L104 / Keep: frames of the count modulo `m` and of one modulus for a general top (Rudich `UniCostKeep`)
-/
namespace ECDLP.L104A
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60

section Keep

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

attribute [local irreducible] cset fillC UP lvlSet topSet

variable {F : NetFamily} {L0X SX TX : Ex}

set_option maxRecDepth 20000 in
theorem countMF_keeps' (hI : TopIfaceF DB P F L0X SX TX) :
    Keeps (countM (UP' L0X SX TX)) (fun y => WC y ∨ 990 ≤ y) := by
  unfold countM pathBody lvlBody UP'
  repeat' (first | apply Keeps.seq | apply Keeps.loop | apply Keeps.ifLt | apply Keeps.skip | apply Keeps.copy | apply Keeps.setK | apply keeps_fill | apply keeps_lset | apply Keeps.cset)
  all_goals first
    | exact UP_ok.vlnE | exact UP_ok.vsrE _ | exact UP_ok.vnxE | exact hI.vl0 | exact hI.vts
    | exact hI.vtt | exact vb_dE | exact vb_kbE _ (by norm_num) | exact vb_NcE | exact vb_bruteU | exact vb_c1E
    | (simp only [WC, WP, WL]; omega)
    | (simp [WC, WP, WL]; done)
    | (intro y hy; simp only [WC, WP, WL]; omega)
    | (norm_num; done)
    | (simp [VB, pow2]; done)

set_option maxRecDepth 20000 in
theorem modBodyF_keeps' (hI : TopIfaceF DB P F L0X SX TX) :
    Keeps (modBody (UP' L0X SX TX)) (fun y => WM y ∨ 990 ≤ y) := by
  unfold modBody countM pathBody lvlBody dmLoop dmBody UP'
  repeat' (first | apply Keeps.seq | apply Keeps.loop | apply Keeps.ifLt | apply Keeps.skip | apply Keeps.copy | apply Keeps.setK | apply keeps_fill | apply keeps_lset | apply Keeps.cset)
  all_goals first
    | exact UP_ok.vlnE | exact UP_ok.vsrE _ | exact UP_ok.vnxE | exact hI.vl0 | exact hI.vts
    | exact hI.vtt | exact vb_dE | exact vb_kbE _ (by norm_num) | exact vb_NcE | exact vb_bruteU | exact vb_c1E
    | (simp only [WM, WC, WP, WL]; omega)
    | (simp [WM, WC, WP, WL]; done)
    | (intro y hy; simp only [WM, WC, WP, WL]; omega)
    | (norm_num; done)
    | (simp [VB, pow2, flagE, ifEq, c1E, nsum, xBit, bitRd, multVm, gE, powE, tBE]; done)

end Keep

theorem countMF_frame' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX) (st : St) {y : ℕ}
    (hy : y < 990) (hW : ¬ WC y) : (Cmd.run (countM (UP' L0X SX TX)) st).1.sc y = st.sc y :=
  ((countMF_keeps' hI) st).1 y hy (fun h => h.elim hW (by omega))

theorem modBodyF_frame' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX) (st : St) {y : ℕ}
    (hy : y < 990) (hW : ¬ WM y) : (Cmd.run (modBody (UP' L0X SX TX)) st).1.sc y = st.sc y :=
  ((modBodyF_keeps' hI) st).1 y hy (fun h => h.elim hW (by omega))

end ECDLP.L104A
