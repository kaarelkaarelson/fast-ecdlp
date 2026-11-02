import ECDLPv2.L115_Dm
import ECDLP.L104_VUni

/-!
# L115 / ModR: one modulus of the residue sweep, with frames
`modBodyR_spec2` (for `j ≥ 2`): scalar `308 = (D * cnt : ZMod j).val`, scalar `309 = D % j`, all scalars `< 990` outside `WM` unchanged, arrays `≠ 3` unchanged.
`modBodyR_small` (for `j < 2`): the same frames.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A ECDLP.L104B ECDLP.L109
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

attribute [local irreducible] cset

theorem modBodyR_small (U : UParts) (s : St) (j : ℕ) (hj : j < 2) :
    (∀ y < 990, ¬ WM y → (Cmd.run (modBodyR U) (s.setSc 300 j)).1.sc y = s.sc y) ∧
    (∀ a, (Cmd.run (modBodyR U) (s.setSc 300 j)).1.ar a = s.ar a) := by
  have hr : (Cmd.run (modBodyR U) (s.setSc 300 j)).1 =
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM U) (dmLoop U))) ((Cmd.run (.setK 315 2) (Cmd.run (.copy 10 300) (s.setSc 300 j)).1).1)).1 := by
    simp only [modBodyR, Cmd.run_seq]
  rw [hr, Cmd.run_ifLt]
  simp only [Cmd.run_setK, Cmd.run_copy, St.setSc_sc, Function.update_self]
  have h10 : (10 : ℕ) ≠ 315 := by norm_num
  simp only [Function.update_of_ne h10, Function.update_self]
  rw [if_pos (by simpa using hj)]
  refine ⟨fun y hy hW => ?_, fun a => ?_⟩
  · simp only [WM] at hW
    simp [Cmd.run_skip, St.setSc, Function.update_of_ne (show y ≠ 315 by omega), Function.update_of_ne (show y ≠ 10 by omega),
      Function.update_of_ne (show y ≠ 300 by omega)]
  · simp [Cmd.run_skip, St.setSc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem modBodyR_spec2 {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (SD : ShapeDataF DB P F T SX TX)
    (s : St) (j : ℕ) {n k ℓ cnt : ℕ} (hP : P n s.ar) (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (h303 : s.sc 303 = NPof K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k')
    (hj : 2 ≤ j)
    (hcnt : ((SD.D j n k s.ar).inner.value : ZMod j) = (cnt : ZMod j)) :
    (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.sc 308 =
        (((deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) : ℕ) : ZMod j) * (cnt : ZMod j)).val ∧
      (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.sc 309 = deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) % j ∧
      (∀ y < 990, ¬ WM y → (Cmd.run (modBodyR (UP' L0X SX TX)) (s.setSc 300 j)).1.sc y = s.sc y) ∧
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
  obtain ⟨dm309, dfr, dar⟩ := dmLoop_spec' t3 (ℓ := ℓ) (L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (m := j)
    hm (by rw [cfr 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [cfr 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10])
  set t4 := (Cmd.run (dmLoop UP) t3).1
  refine ⟨?_, dm309, fun y hy hW => ?_, fun a ha => ?_⟩
  · rw [dfr 308 (by norm_num) (by simp [WD]) (by norm_num), c308]
  · have hW' : ¬ (WC y ∨ y = 10 ∨ y = 300 ∨ y = 301 ∨ y = 315 ∨ y = 309) := hW
    have y10 : y ≠ 10 := fun h => hW' (Or.inr (Or.inl h))
    have y300 : y ≠ 300 := fun h => hW' (Or.inr (Or.inr (Or.inl h)))
    have y315 : y ≠ 315 := fun h => hW' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have y309 : y ≠ 309 := fun h => hW' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    have hWC : ¬ WC y := fun h => hW' (Or.inl h)
    have hWD : ¬ WD y := by
      intro hd
      simp only [WD] at hd
      apply hWC
      simp only [WC, WP, WL]
      omega
    rw [dfr y (by omega) hWD (by simp only [WC, WP, WL] at hWC; omega), cfr y hy hWC, g2 y y315 y10 y300]
  · rw [dar, car a ha]
    simp only [t2, t1, s', Cmd.run_setK, Cmd.run_copy, St.setSc_ar]

end ECDLP.L115
