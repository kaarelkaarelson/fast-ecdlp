import ECDLPv2.L132_Cc
import ECDLP.L102_Final

/-!
# L115 / Final: `countingRate_all : ∀ m, ECDLP109.countingRate m` (no hypotheses)
* `countingRate_of_bound` : a source command with output `encodeNat (count m a)` in array `2` and a sub-exponential cost bound gives `countingRate m`.
* `m = 0` : `count = 0` (the empty sum is `0`); `m = 1` : the L102 Boolean oracle (`Zc 1 ≤ 1`); `m = r+2` : the real engine (`ccCmd`), gate `gate_hook'`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace ECDLP.L132
open ECDLP.L115 ECDLP ECDLP.L61 ECDLP.L65 ECDLP.L70 ECDLP.L77 ECDLP.L78 ECDLP.L80 ECDLP.L92 Turing Computability Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem countingRate_of_bound (m : ℕ) (cs : Cmd) (Bnd : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut cs (encB a)).ar 2) = encodeNat (ECDLP109.count m a))
    (hcost : ∀ a, srcCost cs (encB a) ≤ Bnd (encB a).length)
    (hB : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Bnd L ≤ C * 2 ^ (L / k)) :
    type_of% (ECDLP109.countingRate m) := by
  classical
  choose! C hC using hB
  obtain ⟨Eb, hmono, hE1, hE2⟩ := envelope_mono C
  refine ECDLP.L109.countingRate_of_source m cs 2 (fun L => Eb (2 * L + 1)) hout (fun a => ?_) (fun k hk => ?_)
  · refine le_trans (hcost a) ?_
    refine le_trans (hE1 _ _ (fun k hk => hC k hk _)) ?_
    exact hmono (len_encB_le a)
  · refine ⟨2 * C (2 * k), fun L => ?_⟩
    refine le_trans (hE2 (2 * k) (by omega) (2 * L + 1)) ?_
    have h1 : (2 * L + 1) / (2 * k) ≤ L / k + 1 := by
      calc (2 * L + 1) / (2 * k) ≤ (2 * (L + k)) / (2 * k) := Nat.div_le_div_right (by omega)
        _ = (L + k) / k := Nat.mul_div_mul_left _ _ (by omega)
        _ = L / k + 1 := by rw [Nat.add_div_right _ (by omega)]
    have h2 : 2 ^ ((2 * L + 1) / (2 * k)) ≤ 2 * 2 ^ (L / k) :=
      calc 2 ^ ((2 * L + 1) / (2 * k)) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 * 2 ^ (L / k) := by ring
    calc C (2 * k) * 2 ^ ((2 * L + 1) / (2 * k)) ≤ C (2 * k) * (2 * 2 ^ (L / k)) := Nat.mul_le_mul_left _ h2
      _ = 2 * C (2 * k) * 2 ^ (L / k) := by ring

theorem top_bound_subexp (T Tg : ℕ → ℕ)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L + 21 * L + T L + 8 ≤ C * 2 ^ (L / k) := by
  intro k hk
  obtain ⟨C1, h1⟩ := hT k hk
  obtain ⟨C2, h2⟩ := hTg k hk
  obtain ⟨C3, h3⟩ := poly_subexp 1 k hk
  refine ⟨C1 + C2 + 21 * C3 + 8, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have a := h1 L
  have b := h2 L
  have c := h3 L
  simp only [pow_one] at c
  nlinarith

/-! ### `m = 0` -/

theorem count_zero (a : ECDLP109.Inst) : ECDLP109.count 0 a = 0 := by
  rw [ECDLP109.count_eq_zero_iff]
  refine Set.eq_empty_iff_forall_notMem.2 fun s hs => ?_
  obtain ⟨p, a, b, x, y, π⟩ := a
  simp only [ECDLP109.strings] at hs
  split_ifs at hs with hp
  · obtain ⟨-, P, -, -, -, -, hsum, -⟩ := hs
    exact hsum (by simp)
  · exact hs

theorem countingRate_zero : type_of% (ECDLP109.countingRate 0) := by
  refine countingRate_of_bound 0 zeroOut (fun _ => 3) (fun a => ?_) (fun a => ?_) (fun k hk => ⟨3, fun L => ?_⟩)
  · rw [count_zero, encodeNat_zero]; exact (zeroOut_run _).1
  · exact (zeroOut_run _).2
  · have : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    nlinarith

/-! ### `m = 1` -/

def bitOut : Cmd := .seq (.setK 843 1) (.seq (.wr 2 843 0 843) (.seq (.setK 843 0) (.wr 2 843 0 3)))

theorem bitOut_run (st : St) (hle : st.sc 3 ≤ 1) :
    outOf ((Cmd.run bitOut st).1.ar 2) = (if st.sc 3 = 0 then [] else [true]) ∧ (Cmd.run bitOut st).2 ≤ 8 := by
  have h : (Cmd.run bitOut st).1.ar 2 = Function.update (Function.update (st.ar 2) 1 1) 0 (st.sc 3) := by
    simp [bitOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, St.setAr, St.putAr]
  refine ⟨?_, by simp [bitOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]⟩
  rw [h]
  by_cases h3 : st.sc 3 = 0
  · simp [outOf, h3]
  · have : ∃ n, st.sc 3 = n + 1 := ⟨st.sc 3 - 1, by omega⟩
    obtain ⟨n, hn⟩ := this
    have hn0 : n = 0 := by omega
    subst hn0
    simp [outOf, hn]

theorem zc_one_le (x : Inst) (τ : List Bool) : Zc 1 x τ = 0 ∨ Zc 1 x τ = 1 := by
  by_cases h : 0 < Zc 1 x τ
  · right
    have hg := ECDLP.L70.Zc_pos_good 1 x τ h
    rw [ECDLP.L102.Zc_one x τ hg]
    split_ifs with h1
    · rfl
    · rw [ECDLP.L102.Zc_one x τ hg, if_neg h1] at h; omega
  · left; omega

theorem countingRate_one : type_of% (ECDLP109.countingRate 1) := by
  obtain ⟨c, G, T, Tg, hG, hz, hT, hTg⟩ := ECDLP.L92.merge_data' 0 ECDLP.L102.eng1 1400 1 10 le_rfl le_rfl (by norm_num) le_rfl
    ECDLP.L102.engVal_one ECDLP.L102.engCost_one
  have hcc : CCSpec 1 (.seq c bitOut) (fun L => T L + 10) := by
    intro x st hGx hconf
    obtain ⟨h0, hA, h2, hbits⟩ := hconf
    have hok : okInst 1 x (pre x) := ⟨List.prefix_refl _, le_max_right _ _⟩
    obtain ⟨cv, cc⟩ := hz.spec x st (pre x) hGx h0 hA h2 hbits hok
    have hle : ((Cmd.run c st).1).sc 3 ≤ 1 := by
      rw [cv]; split_ifs <;> omega
    obtain ⟨b1, b2⟩ := bitOut_run (Cmd.run c st).1 hle
    simp only [Cmd.run_seq]
    rw [cv] at b1
    refine ⟨?_, by omega⟩
    rcases zc_one_le x (pre x) with hz0 | hz1
    · rw [b1, hz0, encodeNat_zero]; simp
    · rw [b1, hz1]; simp [encodeNat]; rfl
  refine countingRate_of_bound 1 (cntTop G 10 (.seq c bitOut)) (fun L => Tg L + 21 * L + (T L + 10) + 8)
    (fun a => (cntTop_out 1 G _ 10 (fun L => T L + 10) Tg hG hcc a).1) (fun a => (cntTop_out 1 G _ 10 (fun L => T L + 10) Tg hG hcc a).2)
    (top_bound_subexp _ Tg (fun k hk => ?_) hTg)
  obtain ⟨C, hC⟩ := hT k hk
  refine ⟨C + 10, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := hC L
  nlinarith

/-! ### `m ≥ 2` -/

theorem countingRate_ge2 (r : ℕ) (hr : 1 ≤ r) : type_of% (ECDLP109.countingRate (r + 1)) := by
  obtain ⟨Tg, hG, hTg⟩ := gate_hook' 1400 1 le_rfl le_rfl (by norm_num) Gx2 (hookCmd (r + 1)) 10 775 le_rfl (Th (r + 1))
    (hook_spec (r + 1) (by omega))
  obtain ⟨T, hcc, hTs⟩ := cc_spec r hr 1400 le_rfl
  refine countingRate_of_bound (r + 1) (cntTop _ 10 (ccCmd r 1400)) (fun L => Tg L + 21 * L + T L + 8)
    (fun a => (cntTop_out (r + 1) _ _ 10 T Tg hG hcc a).1) (fun a => (cntTop_out (r + 1) _ _ 10 T Tg hG hcc a).2)
    (top_bound_subexp T Tg hTs (hTg (fun k hk => Th_subexp (r + 1) k hk)))

/-- **The counting theorem, no hypotheses.** -/
theorem countingRate_all : ∀ m : ℕ, type_of% (ECDLP109.countingRate m) := by
  intro m
  match m with
  | 0 => exact countingRate_zero
  | 1 => exact countingRate_one
  | r + 2 => exact countingRate_ge2 (r + 1) (by omega)

end ECDLP.L132
