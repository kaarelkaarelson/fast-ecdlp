import ECDLPv2.L113_Out
import ECDLPv2.L113_Num

/-!
# L115 / Prep: the scalars `K = M - 2` (scalar 801) and the width `(K+1)^2` (scalar 710) from the modulus count `M` (scalar 852)
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `710 := (sc 801 + 1)^2`, by `a` rounds of `a` increments (`a` in scalar 863) -/
def sqC : Cmd :=
  .seq (.copy 863 801) (.seq (.incr 863) (.seq (.setK 710 0) (.loop 863 864 (.loop 863 865 (.incr 710)))))

def prepC : Cmd := .seq (.seq (.copy 801 852) (.seq (.decr 801) (.decr 801))) sqC

theorem inner_run (st : St) (a : ℕ) (h863 : st.sc 863 = a) :
    (Cmd.run (.loop 863 865 (.incr 710)) st).1.sc 710 = st.sc 710 + a ∧
    (∀ y, y ≠ 710 → y ≠ 865 → (Cmd.run (.loop 863 865 (.incr 710)) st).1.sc y = st.sc y) ∧
    (Cmd.run (.loop 863 865 (.incr 710)) st).1.ar = st.ar ∧
    (Cmd.run (.loop 863 865 (.incr 710)) st).2 ≤ 2 * a + 1 := by
  let P : ℕ → St → Prop := fun i t => t.sc 710 = st.sc 710 + i ∧ (∀ y, y ≠ 710 → y ≠ 865 → t.sc y = st.sc y) ∧ t.ar = st.ar
  have h0 : P 0 st := ⟨rfl, fun _ _ _ => rfl, rfl⟩
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (.incr 710) (t.setSc 865 i)).1 := by
    intro i t ⟨p1, p2, p3⟩
    refine ⟨?_, fun y h1 h2 => ?_, ?_⟩
    · simp [Cmd.run_incr, St.setSc, p1]; omega
    · simp [Cmd.run_incr, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2, p2 y h1 h2]
    · simp [Cmd.run_incr, St.setSc, p3]
  have hI := Cmd.loop_inv (b := 863) (c := 865) (body := .incr 710) (st := st) P h0 (fun i t _ hp => step i t hp)
  have hC := Cmd.loop_cost_le (b := 863) (c := 865) (body := .incr 710) (st := st) P 1 h0 (fun i t _ hp => step i t hp)
    (fun i t _ hp => by simp [Cmd.run_incr])
  rw [h863] at hI hC
  obtain ⟨i1, i2, i3⟩ := hI
  refine ⟨i1, i2, i3, ?_⟩
  omega

theorem sqC_run (st : St) (K : ℕ) (h801 : st.sc 801 = K) :
    (Cmd.run sqC st).1.sc 710 = (K + 1) * (K + 1) ∧ (Cmd.run sqC st).1.sc 801 = K ∧
    (∀ y, y ≠ 710 → y ≠ 863 → y ≠ 864 → y ≠ 865 → (Cmd.run sqC st).1.sc y = st.sc y) ∧
    (Cmd.run sqC st).1.ar = st.ar ∧ (Cmd.run sqC st).2 ≤ (K + 1) * (2 * (K + 1) + 2) + 8 := by
  set s1 := ((st.setSc 863 (st.sc 801)).setSc 863 ((st.setSc 863 (st.sc 801)).sc 863 + 1)).setSc 710 0 with hs1
  have e863 : s1.sc 863 = K + 1 := by simp [hs1, St.setSc, h801]
  have e710 : s1.sc 710 = 0 := by simp [hs1, St.setSc]
  let P : ℕ → St → Prop := fun i t => t.sc 710 = i * (K + 1) ∧ (∀ y, y ≠ 710 → y ≠ 864 → y ≠ 865 → t.sc y = s1.sc y) ∧ t.ar = s1.ar
  have h0 : P 0 s1 := ⟨by simp [e710], fun _ _ _ _ => rfl, rfl⟩
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (.loop 863 865 (.incr 710)) (t.setSc 864 i)).1 ∧
      (Cmd.run (.loop 863 865 (.incr 710)) (t.setSc 864 i)).2 ≤ 2 * (K + 1) + 1 := by
    intro i t ⟨p1, p2, p3⟩
    have h863 : (t.setSc 864 i).sc 863 = K + 1 := by
      simp [St.setSc, Function.update_of_ne (show (863 : ℕ) ≠ 864 by norm_num), p2 863 (by norm_num) (by norm_num) (by norm_num), e863]
    obtain ⟨q1, q2, q3, q4⟩ := inner_run (t.setSc 864 i) (K + 1) h863
    refine ⟨⟨?_, fun y h1 h2 h3 => ?_, ?_⟩, q4⟩
    · rw [q1]; simp [St.setSc, p1]; ring
    · rw [q2 y h1 h3, St.setSc_sc, Function.update_of_ne h2, p2 y h1 h2 h3]
    · rw [q3]; simpa using p3
  have hI := Cmd.loop_inv (b := 863) (c := 864) (body := .loop 863 865 (.incr 710)) (st := s1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 863) (c := 864) (body := .loop 863 865 (.incr 710)) (st := s1) P (2 * (K + 1) + 1) h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  rw [e863] at hI hC
  obtain ⟨i1, i2, i3⟩ := hI
  have hrun : Cmd.run sqC st = ((Cmd.run (.loop 863 864 (.loop 863 865 (.incr 710))) s1).1,
      1 + (1 + (1 + (Cmd.run (.loop 863 864 (.loop 863 865 (.incr 710))) s1).2 + 1) + 1) + 1) := by
    simp only [sqC, Cmd.run_seq, Cmd.run_copy, Cmd.run_incr, Cmd.run_setK]
    rfl
  rw [hrun]
  refine ⟨i1, ?_, fun y h1 h2 h3 h4 => ?_, ?_, ?_⟩
  · rw [i2 801 (by norm_num) (by norm_num) (by norm_num)]
    simp [hs1, St.setSc, h801]
  · simp only
    rw [i2 y h1 h3 h4]
    simp [hs1, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2]
  · simp only
    rw [i3]; simp [hs1, St.setSc]
  · simp only
    nlinarith

theorem prepC_run (st : St) (K : ℕ) (h852 : st.sc 852 = K + 2) :
    (Cmd.run prepC st).1.sc 710 = (K + 1) * (K + 1) ∧ (Cmd.run prepC st).1.sc 801 = K ∧
    (∀ y, y ≠ 710 → y ≠ 801 → y ≠ 863 → y ≠ 864 → y ≠ 865 → (Cmd.run prepC st).1.sc y = st.sc y) ∧
    (Cmd.run prepC st).1.ar = st.ar ∧ (Cmd.run prepC st).2 ≤ (K + 1) * (2 * (K + 1) + 2) + 14 := by
  have e : Cmd.run (.seq (.copy 801 852) (.seq (.decr 801) (.decr 801))) st = (st.setSc 801 K, 5) := by
    simp only [Cmd.run_seq, Cmd.run_copy, Cmd.run_decr, h852]
    refine Prod.ext ?_ rfl
    apply St.ext
    · funext y; by_cases h : y = 801 <;> simp [h, St.setSc]
    · rfl
  have e801 : (st.setSc 801 K).sc 801 = K := by simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := sqC_run (st.setSc 801 K) K e801
  have hrun : Cmd.run prepC st = ((Cmd.run sqC (st.setSc 801 K)).1, 5 + (Cmd.run sqC (st.setSc 801 K)).2 + 1) := by
    simp only [prepC, Cmd.run_seq, e]
  rw [hrun]
  refine ⟨a1, a2, fun y h1 h2 h3 h4 h5 => ?_, ?_, ?_⟩
  · simp only
    rw [a3 y h1 h3 h4 h5]; simp [St.setSc, Function.update_of_ne h2]
  · simp only; rw [a4]; rfl
  · simp only; omega

end ECDLP.L115
