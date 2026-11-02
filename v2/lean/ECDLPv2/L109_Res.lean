import ECDLP.L104_VUni
import ECDLPv2.L109_Residue

/-!
# L109 / Res: the engine's per-modulus RESIDUE register (not only the zero flag)

`modBodyR U` is Rudich's `modBody U` without its last step `cset flagE 301` (the divisibility flag).
`modBodyR_spec'` : for a modulus `j ≥ 2`, `modBodyR` leaves in scalar 308 the residue `(D · cnt : ZMod j).val`
(`D = deepMult`, `cnt` any natural with network value `cnt` in `ZMod j`; for the real engine `cnt = Zc`, by `engine_value_mod_real`),
keeps scalar 10 `= j` and keeps all arrays `≠ 3`.  (Copy of the first half of L104B `modBodyF_spec'`.)
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L109
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A ECDLP.L104B
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

/-- one modulus, residue version: `modBody` minus the flag step -/
def modBodyR (U : UParts) : Cmd :=
  .seq (.copy 10 300) <| .seq (.setK 315 2) (.ifLt 10 315 .skip (.seq (countM U) (dmLoop U)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem modBodyR_spec' {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (SD : ShapeDataF DB P F T SX TX)
    (s : St) (j : ℕ) {n k ℓ cnt : ℕ} (hP : P n s.ar) (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (h303 : s.sc 303 = NPof K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k')
    (hj : 2 ≤ j)
    (hcnt : ((SD.D j n k s.ar).inner.value : ZMod j) = (cnt : ZMod j)) :
    (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.sc 308 =
        (((deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) : ℕ) : ZMod j) * (cnt : ZMod j)).val ∧
      (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.sc 10 = j ∧
      (∀ a, a ≠ 3 → (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.ar a = s.ar a) := by
  set D := deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
  set s' := s.setSc 300 j
  set t1 := (Cmd.run (.copy 10 300) s').1
  set t2 := (Cmd.run (.setK 315 2) t1).1
  have g2 : ∀ y, y ≠ 315 → y ≠ 10 → y ≠ 300 → t2.sc y = s.sc y := fun y a b c => by
    simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have j10 : t2.sc 10 = j := by simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy]
  have c315 : t2.sc 315 = 2 := by simp [t2, Cmd.run_setK]
  have hrun : (Cmd.run (modBodyR (UP' L0X SX TX)) s').1 =
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX)) (dmLoop UP))) t2).1 := by
    simp only [modBodyR, Cmd.run_seq]; rfl
  rw [hrun, Cmd.run_ifLt, j10, c315]
  have hj' : ¬ j < 2 := by omega
  rw [if_neg hj', Cmd.run_seq]
  dsimp only
  have hm : 1 < j := by omega
  obtain ⟨c308, cfr, car⟩ := countMF_spec' (L0X := L0X) SD (m := j) (n := n) (k := k) (ℓ := ℓ) (cnt := cnt) t2 (by simpa [t2, t1, s', Cmd.run_setK, Cmd.run_copy] using hP) hm j10
    (by rw [g2 11 (by norm_num) (by norm_num) (by norm_num), h11]) (by rw [g2 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [g2 2 (by norm_num) (by norm_num) (by norm_num), h2]) hkn
    (by rw [g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [g2 316 (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [g2 303 (by norm_num) (by norm_num) (by norm_num), h303])
    (fun v k' h => by have := topOk_lt h; have := h.1; rw [g2 v (by omega) (by omega) (by omega), htok v k' h])
    hcnt
  set t3 := (Cmd.run (countM (UP' L0X SX TX)) t2).1
  obtain ⟨dm309, dfr, dar⟩ := dmLoop_spec t3 (ℓ := ℓ) (L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (m := j)
    (by omega) (by rw [cfr 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [cfr 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10])
  set t4 := (Cmd.run (dmLoop UP) t3).1
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · rw [dfr 308 (by norm_num) (by simp [WD]) (by norm_num), c308]
  · rw [dfr 10 (by norm_num) (by simp [WD]) (by norm_num), cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10]
  · rw [dar, car a ha]
    simp only [t2, t1, s', Cmd.run_setK, Cmd.run_copy, St.setSc_ar]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one modulus.** -/
theorem modBodyR_cost' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX) (hS : F.Spec) {V n k ℓ : ℕ} (s : St) (hP : P n s.ar) (j : ℕ) (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (h303 : s.sc 303 ≤ V)
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k') (hR : 2 ≤ j → F.FamOK V j K0u ℓ n) (hjV : j ≤ V)
    (hnV : n ≤ V) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).2 ≤ 100 * YB DB V ^ 3 := by
  have hY := YB_ge DB V
  have hPB := PB_le_YB DB V
  have hY3 : YB DB V ≤ YB DB V ^ 3 := Nat.le_self_pow (by norm_num) _
  have hY23 : YB DB V ^ 2 ≤ YB DB V ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  set s' := s.setSc 300 j
  set t1 := (Cmd.run (.copy 10 300) s').1
  set t2 := (Cmd.run (.setK 315 2) t1).1
  have g2 : ∀ y, y ≠ 315 → y ≠ 10 → y ≠ 300 → t2.sc y = s.sc y := fun y a b c => by
    simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have j10 : t2.sc 10 = j := by simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy]
  have c315 : t2.sc 315 = 2 := by simp [t2, Cmd.run_setK]
  have e : (Cmd.run (modBodyR (UP' L0X SX TX)) s').2 = (Cmd.run (.copy 10 300) s').2 + ((Cmd.run (.setK 315 2) t1).2 +
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX)) (dmLoop UP))) t2).2 + 1) + 1 := by
    rw [show modBodyR (UP' L0X SX TX) = .seq (.copy 10 300) (.seq (.setK 315 2) (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX))
      (dmLoop UP)))) from rfl, seq_cost, seq_cost]
  rw [e, Cmd.run_copy, Cmd.run_setK, Cmd.run_ifLt, j10, c315]
  by_cases hj : j < 2
  · rw [if_pos hj, Cmd.run_skip]; omega
  rw [if_neg hj]
  have R := hR (by omega)
  have hm : 1 < j := by omega
  have kc := countMF_cost' hI hS (n := n) (k := k) (ℓ := ℓ) t2 (by simpa [t2, t1, s', Cmd.run_setK, Cmd.run_copy] using hP) hm j10
    (by rw [g2 11 (by norm_num) (by norm_num) (by norm_num), h11])
    (by rw [g2 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [g2 2 (by norm_num) (by norm_num) (by norm_num), h2]) hkn
    (by rw [g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [g2 316 (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [g2 303 (by norm_num) (by norm_num) (by norm_num)]; exact h303)
    (fun v k' h => by have := topOk_lt h; have := h.1; rw [g2 v (by omega) (by omega) (by omega), htok v k' h])
    R hℓ hlv
  dsimp only
  set t3 := (Cmd.run (countM (UP' L0X SX TX)) t2).1 with ht3
  have f3 : ∀ y < 990, ¬ WC y → t3.sc y = t2.sc y := fun y hy hW => by rw [ht3]; exact countMF_frame' hI t2 hy hW
  have m3 : t3.sc 10 = j := by rw [f3 10 (by norm_num) (by simp [WC, WP, WL]), j10]
  have z3 : t3.sc 0 = n := by
    rw [f3 0 (by norm_num) (by simp [WC, WP, WL]), g2 0 (by norm_num) (by norm_num) (by norm_num), h0]
  have w3 : t3.sc 2 = k := by
    rw [f3 2 (by norm_num) (by simp [WC, WP, WL]), g2 2 (by norm_num) (by norm_num) (by norm_num), h2]
  have l3 : t3.sc 307 = ℓ := by
    rw [f3 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307]
  have c3 : t3.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n := by
    rw [f3 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12]
  obtain ⟨kd, d4⟩ := dmLoop_cost (D := DB) t3 hm l3 c3 m3 (hI.ok_deep R) hℓ hlv
  obtain ⟨-, f4, -⟩ := dmLoop_spec t3 (by omega) l3 c3 m3
  set t4 := (Cmd.run (dmLoop UP) t3).1 with ht4
  have m4 : t4.sc 10 = j := by rw [ht4, f4 10 (by norm_num) (by simp [WD]) (by norm_num), m3]
  have z4 : t4.sc 0 = n := by rw [ht4, f4 0 (by norm_num) (by simp [WD]) (by norm_num), z3]
  have w4 : t4.sc 2 = k := by rw [ht4, f4 2 (by norm_num) (by simp [WD]) (by norm_num), w3]
  have e5 := seq_cost (countM (UP' L0X SX TX)) (dmLoop UP) t2
  rw [← ht3] at e5
  omega



end ECDLP.L109
#print axioms ECDLP.L109.modBodyR_spec'
#print axioms ECDLP.L109.modBodyR_cost'
