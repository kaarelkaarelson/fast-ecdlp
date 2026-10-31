import ECDLP.L80_Poly
import ECDLP.L76_Layer
import ECDLP.L77_Cap

/-!
# L80 / Hook: L77's input-layer hook discharged from L76's `checkC_run`

`hookCmd m` = save `sc 2` in scalar 800, set `sc 2 := 0` (the gate runs on the initial state; the length clause of `checkC` is
`|τ| ≤ nlen`, trivial for the empty prefix), run `checkC m`, restore `sc 2`.
`HookSpec'` is L77's `HookSpec` with the `keep_*` fields required only on states that hold the input (this is all `gate_hook` uses);
`gate_hook'` is `gate_hook`'s statement for it; `hook_spec` : `HookSpec' Prime Gx2 (hookCmd m) 775 (Th m)`.
-/
namespace ECDLP.L80
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

structure HookSpec' (F1 F2 : Inst → Prop) (H : Cmd) (fl2 : ℕ) (Th : ℕ → ℕ) : Prop where
  keep_sc : ∀ (x : Inst) (st : St), F1 x → st.sc 0 = (encB x).length → st.ar 0 = startingMemory (encB x) →
    ∀ y, (y = 0 ∨ y = 2 ∨ y = 5 ∨ y = 7 ∨ y = 8) → (Cmd.run H st).1.sc y = st.sc y
  keep_ar : ∀ (x : Inst) (st : St), F1 x → st.sc 0 = (encB x).length → st.ar 0 = startingMemory (encB x) →
    (Cmd.run H st).1.ar 0 = st.ar 0
  spec : ∀ (x : Inst) (st : St), F1 x → st.sc 0 = (encB x).length → st.ar 0 = startingMemory (encB x) →
    ((Cmd.run H st).1.sc fl2 = 0 ↔ ¬ F2 x) ∧ (Cmd.run H st).2 ≤ Th (encB x).length

theorem gate_hook' (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (F2 : Inst → Prop) (H : Cmd) (fl fl2 : ℕ)
    (hfl : 10 ≤ fl) (Th : ℕ → ℕ) (hH : HookSpec' (fun x => x.1.Prime) F2 H fl2 Th) :
    ∃ Tg : ℕ → ℕ, GateSpec (fun x => x.1.Prime ∧ F2 x) (gateCmd S q H fl fl2) fl Tg ∧
      ((∀ k, 1 ≤ k → ∃ C : ℕ, ∀ L, Th L ≤ C * 2 ^ (L / k)) →
        ∀ k, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) := by
  classical
  obtain ⟨Tp, hP, hPs⟩ := gate_prime S q hS hq1 hqS
  refine ⟨fun L => Tp L + Th L + 5, ⟨fun x => ?_⟩, fun hT k hk => ?_⟩
  · obtain ⟨g0, gA, g2, g5, g7, g8, gf, gc⟩ := hP.spec x
    simp only [gateCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize Cmd.run (guardPrime S q) (St.init (encB x)) = r at g0 gA g2 g5 g7 g8 gf gc ⊢
    by_cases hp : x.1.Prime
    · have hz : r.1.sc 1204 ≠ 0 := fun h => (gf.1 h) hp
      simp only [hz, if_false, Cmd.run_seq, Cmd.run_copy]
      obtain ⟨hf, hc⟩ := hH.spec x r.1 hp g0 gA
      have k := fun y hy => hH.keep_sc x r.1 hp g0 gA y hy
      simp only [St.setSc_sc, Function.update_apply, St.setSc_ar]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [if_neg (by omega), k 0 (by simp), g0]
      · rw [hH.keep_ar x r.1 hp g0 gA, gA]
      · rw [if_neg (by omega), k 2 (by simp), g2]
      · rw [if_neg (by omega), k 5 (by simp), g5]
      · rw [if_neg (by omega), k 7 (by simp), g7]
      · rw [if_neg (by omega), k 8 (by simp), g8]
      · simp only [if_true]; rw [hf]; simp [hp]
      · omega
    · have hz : r.1.sc 1204 = 0 := gf.2 hp
      simp only [hz, if_true, Cmd.run_setK]
      simp only [St.setSc_sc, Function.update_apply, St.setSc_ar]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [if_neg (by omega), g0]
      · exact gA
      · rw [if_neg (by omega), g2]
      · rw [if_neg (by omega), g5]
      · rw [if_neg (by omega), g7]
      · rw [if_neg (by omega), g8]
      · simp [hp]
      · omega
  · obtain ⟨C1, h1⟩ := hPs k hk
    obtain ⟨C2, h2⟩ := hT k hk
    refine ⟨C1 + C2 + 5, fun L => ?_⟩
    have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    have := h1 L
    have := h2 L
    nlinarith

/-! ### the hook -/

def hookCmd (m : ℕ) : Cmd :=
  .seq (.copy 800 2) (.seq (.setK 2 0) (.seq (checkC m)
    (.seq (.setK 801 1) (.seq (.ifLt 801 775 (.setK 775 0) .skip) (.copy 2 800)))))

def Th (m L : ℕ) : ℕ :=
  400 * m * (8 + (m + 2) * L) ^ 3 + 13000 * m * (8 + (m + 2) * L) ^ 2 + 4000 * m * (8 + (m + 2) * L) + 3000 + 20

theorem Th_subexp (m k : ℕ) (hk : 1 ≤ k) : ∃ C : ℕ, ∀ L, Th m L ≤ C * 2 ^ (L / k) := by
  obtain ⟨C, hC⟩ := poly_subexp 3 k hk
  have hle : ∀ L, 8 + (m + 2) * L ≤ (m + 10) * (L + 1) := fun L => by nlinarith
  refine ⟨(400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3020) * C, fun L => ?_⟩
  have h1 := hC L
  have p1 : 1 ≤ (L + 1) := by omega
  have e1 : (8 + (m + 2) * L) ^ 3 ≤ (m + 10) ^ 3 * (L + 1) ^ 3 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (hle L) 3
  have e2 : (8 + (m + 2) * L) ^ 2 ≤ (m + 10) ^ 2 * (L + 1) ^ 3 := by
    calc (8 + (m + 2) * L) ^ 2 ≤ ((m + 10) * (L + 1)) ^ 2 := Nat.pow_le_pow_left (hle L) 2
      _ = (m + 10) ^ 2 * (L + 1) ^ 2 := by rw [mul_pow]
      _ ≤ (m + 10) ^ 2 * (L + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right p1 (by norm_num))
  have e3 : 8 + (m + 2) * L ≤ (m + 10) * (L + 1) ^ 3 := by
    calc 8 + (m + 2) * L ≤ (m + 10) * (L + 1) := hle L
      _ ≤ (m + 10) * (L + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have e4 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ p1
  unfold Th
  have f1 := Nat.mul_le_mul_left (400 * m) e1
  have f2 := Nat.mul_le_mul_left (13000 * m) e2
  have f3 := Nat.mul_le_mul_left (4000 * m) e3
  have g : (400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3020) * (L + 1) ^ 3 ≤
      (400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3020) * (C * 2 ^ (L / k)) :=
    Nat.mul_le_mul_left _ h1
  nlinarith [f1, f2, f3, g, e4]

theorem hook_spec (m : ℕ) (hm : 1 ≤ m) : HookSpec' (fun x => x.1.Prime) Gx2 (hookCmd m) 775 (Th m) := by
  classical
  have key : ∀ (x : Inst) (st : St), x.1.Prime → st.sc 0 = (encB x).length → st.ar 0 = startingMemory (encB x) →
      (Cmd.run (hookCmd m) st).1.sc 775 = (if Gx2 x then 1 else 0) ∧ (Cmd.run (hookCmd m) st).1.sc 2 = st.sc 2 ∧
      (Cmd.run (hookCmd m) st).1.sc 0 = st.sc 0 ∧ (Cmd.run (hookCmd m) st).1.sc 5 = st.sc 5 ∧
      (Cmd.run (hookCmd m) st).1.sc 7 = st.sc 7 ∧ (Cmd.run (hookCmd m) st).1.sc 8 = st.sc 8 ∧
      (Cmd.run (hookCmd m) st).1.ar 0 = st.ar 0 ∧ (Cmd.run (hookCmd m) st).2 ≤ Th m (encB x).length := by
    intro x st hp h0 hA
    obtain ⟨p, a, b, xR, yR, π⟩ := x
    set s2 := (st.setSc 800 (st.sc 2)).setSc 2 0 with hs2
    have s20 : s2.sc 0 = st.sc 0 := by simp [hs2, St.setSc, Function.update_apply]
    have s2A : s2.ar 0 = st.ar 0 := by simp [hs2, St.setSc]
    have s22 : s2.sc 2 = 0 := by simp [hs2, St.setSc]
    obtain ⟨f1, -, -, -, -, -, -, -, -, f10, f11, f12, f13⟩ :=
      checkC_run m hm π p a b xR yR hp s2 (by rw [s2A]; exact hA) (by rw [s20]; exact h0) _ rfl
    have e : Cmd.run (checkC m) ((st.setSc 800 (st.sc 2)).setSc 2 0) = Cmd.run (checkC m) s2 := rfl
    generalize hr : Cmd.run (checkC m) s2 = r at f1 f10 f11 f12 f13
    have g800 : r.1.sc 800 = st.sc 2 := by rw [f12 800 (by simp [ZChk])]; simp [hs2, St.setSc]
    have hG : r.1.sc 775 = 1 ↔ Gx2 (p, a, b, xR, yR, π) := by
      rw [f1, s22]
      simp only [Gx2]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Nat.zero_le _⟩
    have hF : ∀ y, (Cmd.run (hookCmd m) st).1.sc y = if y = 2 then st.sc 2 else if y = 775 then
        (if r.1.sc 775 = 1 then 1 else 0) else if y = 801 then 1 else r.1.sc y := by
      intro y
      simp only [hookCmd, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, Cmd.run_ifLt, e, hr, Cmd.run_skip]
      by_cases hc : 1 < r.1.sc 775
      · simp only [hc, if_true, St.setSc_sc, Function.update_apply, g800]
        have : r.1.sc 775 ≠ 1 := by omega
        split_ifs <;> first | rfl | omega | (simp_all; done)
      · simp only [hc, if_false, St.setSc_sc, Function.update_apply, g800]
        have : r.1.sc 775 = 0 ∨ r.1.sc 775 = 1 := by omega
        split_ifs <;> first | rfl | omega | (simp_all; done)
    have hAr : (Cmd.run (hookCmd m) st).1.ar = r.1.ar := by
      simp only [hookCmd, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, Cmd.run_ifLt, e, hr, Cmd.run_skip]
      by_cases hc : 1 < r.1.sc 775 <;> simp [hc, St.setSc]
    have hCo : (Cmd.run (hookCmd m) st).2 ≤ r.2 + 12 := by
      simp only [hookCmd, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, Cmd.run_ifLt, e, hr, Cmd.run_skip]
      by_cases hc : 1 < r.1.sc 775 <;> simp [hc, Cmd.run_setK, Cmd.run_skip] <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hF]; simp only [show (775 : ℕ) ≠ 2 by norm_num, if_false, if_true]
      by_cases hg : Gx2 (p, a, b, xR, yR, π)
      · have := hG.2 hg; simp [this, hg]
      · have hne : r.1.sc 775 ≠ 1 := fun h => hg (hG.1 h)
        simp [hne, hg]
    · rw [hF]; simp
    · rw [hF]; simp [f12 0 (by simp [ZChk]), hs2, St.setSc]
    · rw [hF]; simp [f12 5 (by simp [ZChk]), hs2, St.setSc]
    · rw [hF]; simp [f12 7 (by simp [ZChk]), hs2, St.setSc]
    · rw [hF]; simp [f12 8 (by simp [ZChk]), hs2, St.setSc]
    · rw [hAr, f11 0 (by simp [AR])]; simp [hs2, St.setSc]
    · unfold Th
      rw [s20, h0] at f13
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro x st hp h0 hA y hy
    obtain ⟨-, k2, k0, k5, k7, k8, -, -⟩ := key x st hp h0 hA
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro x st hp h0 hA
    exact (key x st hp h0 hA).2.2.2.2.2.2.1
  · intro x st hp h0 hA
    obtain ⟨k775, -, -, -, -, -, -, kc⟩ := key x st hp h0 hA
    refine ⟨?_, kc⟩
    rw [k775]
    by_cases hg : Gx2 x <;> simp [hg]

end ECDLP.L80
