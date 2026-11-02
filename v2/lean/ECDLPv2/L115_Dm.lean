import ECDLPv2.L109_Res

/-!
# L115 / Dm: `dmLoop` with the exact residue (`309 = D % m`) and `modBodyR` with the full frame facts
Rudich's `dmLoop_spec` states `sc 309 % m = deepMult % m`; the loop invariant also gives `sc 309 < m` (each turn ends with `% m`, the start value
`1 < m`), hence `sc 309 = deepMult % m`.  `modBodyR_spec2` is `L109.modBodyR_spec'` plus: `309 = D % j`, and the scalar frame.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset ECDLP.L109

attribute [local irreducible] cset

/-- **The multiplier modulo `m`, exact.** -/
theorem dmLoop_spec' (st : St) {ℓ L m : ℕ} (hm : 1 < m) (h307 : st.sc 307 = ℓ) (h12 : st.sc 12 = L)
    (h10 : st.sc 10 = m) :
    (Cmd.run (dmLoop UP) st).1.sc 309 = deepMult K0u ℓ L % m ∧
      (∀ y < 1000, ¬ WD y → y ≠ 306 → (Cmd.run (dmLoop UP) st).1.sc y = st.sc y) ∧
      (Cmd.run (dmLoop UP) st).1.ar = st.ar := by
  have hm0 : 0 < m := by omega
  rw [dmLoop]
  repeat rw [Cmd.run_seq]
  set s1 := (Cmd.run (.copy 40 12) st).1
  set s2 := (Cmd.run (.setK 309 1) s1).1
  have g2 : ∀ y, y ≠ 309 → y ≠ 40 → s2.sc y = st.sc y := fun y a b => by
    simp [s2, s1, Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b]
  let DI : ℕ → St → Prop := fun j s =>
    (∀ d, d + j = ℓ → ∃ lam, s.sc 40 = lam ∧ (s.sc 309 * deepMult K0u d lam) % m = deepMult K0u ℓ L % m) ∧
    (∀ y < 1000, ¬ WD y → y ≠ 306 → s.sc y = s2.sc y) ∧ s.ar = s2.ar ∧ s.sc 309 < m
  have h0 : DI 0 s2 := ⟨fun d hd => ⟨L, by simp [s2, s1, Cmd.run_setK, Cmd.run_copy, h12], by
      obtain rfl : d = ℓ := by omega
      simp [s2, Cmd.run_setK]⟩, fun _ _ _ _ => rfl, rfl, by simp [s2, Cmd.run_setK]; exact hm⟩
  have hI := Cmd.loop_inv (b := 307) (c := 306) (body := dmBody UP) (st := s2) DI h0 (by
    intro j s hj ⟨hI, sfr, sar, slt⟩
    have e307 : s2.sc 307 = ℓ := by rw [g2 307 (by norm_num) (by norm_num), h307]
    rw [e307] at hj
    set s' := s.setSc 306 j
    obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
    obtain ⟨lam, e40, e309⟩ := hI (d + 1) (by omega)
    have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
    obtain ⟨r40, r309, rfr, rar⟩ := dmBody_spec s' (d := d) (L := lam) (m := m) hm0
      (by rw [g 307 (by norm_num), sfr 307 (by norm_num) (by simp [WD]) (by norm_num), e307]; simp [s'])
      (by rw [g 40 (by norm_num), e40])
      (by rw [g 10 (by norm_num), sfr 10 (by norm_num) (by simp [WD]) (by norm_num),
        g2 10 (by norm_num) (by norm_num), h10])
    refine ⟨fun d' hd' => ?_, fun y hy hW h306 => ?_, by rw [rar]; exact sar, ?_⟩
    · obtain rfl : d' = d := by omega
      refine ⟨_, r40, ?_⟩
      rw [r309, g 309 (by norm_num), mod_mul3, ← e309, deepMult]
    · rw [rfr y hy hW, g y h306, sfr y hy hW h306]
    · rw [r309]; exact Nat.mod_lt _ hm0)
  rw [g2 307 (by norm_num) (by norm_num), h307] at hI
  obtain ⟨hv, hfr, har, hlt⟩ := hI
  obtain ⟨lam, -, e⟩ := hv 0 (by omega)
  refine ⟨?_, fun y hy hW h306 => ?_, ?_⟩
  · have h1 : (Cmd.run (.loop 307 306 (dmBody UP)) s2).1.sc 309 % m = deepMult K0u ℓ L % m := by
      rw [← e, deepMult, mul_one]
    rw [← h1, Nat.mod_eq_of_lt hlt]
  · simp only [WD] at hW
    rw [hfr y hy (by simp only [WD]; omega) h306, g2 y (by omega) (by omega)]
  · rw [har]; rfl

end ECDLP.L115
