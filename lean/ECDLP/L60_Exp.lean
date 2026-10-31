import ECDLP.L60_Fam

/-!
# L60: the exponent of the uniform engine, for an abstract network family

Generalisation of `FactoringAux/UniExp.lean` (`uni_exp`): for every `NetFamily F` with `F.Spec`, one
exponent `Z n` bounds all requirements of the uniform engine and `Z n ≤ n / k + C_k` for every `k`.
The levels/chain parts of Rudich's file (`USmall`, `small_poly`, `small_bound`, `UGood`, `chainMax_le`,
`NPof_le`, ...) are reused unchanged; only the lemmas that mention the top network are re-proved, with
the symbolic constant `F.c` in place of Rudich's literals (so thresholds `2 c ≤ ℓ` appear).
-/

namespace ECDLP.L60

open Factoring.Aux

namespace NetFamily

variable {F : NetFamily}

/-! ### Polynomial bounds in `P = Kb 48 ℓ` -/

theorem good_factsG (hS : F.Spec) {ℓ n : ℕ} (hc : 2 * F.c ≤ ℓ) (h : UGood ℓ n) :
    48 ≤ Kb K0u ℓ ∧ ℓ ≤ Kb K0u ℓ ∧ 1 ≤ n ∧ n ≤ Kb K0u ℓ ^ 700 ∧ F.X n ^ 4 ≤ Kb K0u ℓ ^ 701 := by
  obtain ⟨-, h2, h3⟩ := h
  rw [Kb_succ] at h3
  have hP := Kb48_ge48 ℓ
  have hl := (lt_Kb48 ℓ).le
  have hS4 := hS.X4_le n
  generalize Kb K0u ℓ = P at h2 h3 hP hl ⊢
  have h9 : (9 : ℕ) ^ 40 ≤ P ^ 60 := le_trans (by norm_num) (Nat.pow_le_pow_left hP 60)
  have hn : n ≤ P ^ 700 := calc n ≤ (9 * P ^ 16) ^ 40 := h3.le
      _ = 9 ^ 40 * P ^ 640 := by ring
      _ ≤ P ^ 60 * P ^ 640 := Nat.mul_le_mul_right _ h9
      _ = P ^ 700 := by ring
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h2
  refine ⟨hP, hl, hn1, hn, ?_⟩
  have h2c : 2 * F.c ≤ P := by omega
  calc F.X n ^ 4 ≤ F.c * n + F.c := hS4
    _ ≤ 2 * F.c * n := by have := Nat.mul_le_mul_left F.c hn1; nlinarith
    _ ≤ P * P ^ 700 := Nat.mul_le_mul h2c hn
    _ = P ^ 701 := by ring

theorem good_boundsG (hS : F.Spec) {ℓ n : ℕ} (hc : 2 * F.c ≤ ℓ) (h : UGood ℓ n) :
    Gs K0u ℓ ≤ Kb K0u ℓ ^ 9 ∧ Gm4 K0u ℓ ≤ Kb K0u ℓ ^ 36 ∧ ℓ * Gm4 K0u ℓ ≤ Kb K0u ℓ ^ 37 ∧
      F.mbn K0u ℓ n ≤ Kb K0u ℓ ^ 778 ∧ F.Wn K0u ℓ n + 1 ≤ Kb K0u ℓ ^ 740 ∧ F.nodes n ≤ Kb K0u ℓ ^ 702 := by
  obtain ⟨hP, hl, -, -, hS'⟩ := good_factsG hS hc h
  have hmb := mbn_le hS (K0 := K0u) (by norm_num) ℓ n
  have hW := Wn_le F K0u ℓ n
  have hmN := hS.nodes_le n
  have hcW : F.cWn K0u ℓ = F.c + F.c * Gs K0u ℓ + 2 * ℓ * Gm4 K0u ℓ + 1 := rfl
  have hcm : F.cmbn K0u ℓ = 2 * F.c + 9 + 4 * ℓ * Gm4 K0u ℓ * F.cWn K0u ℓ := rfl
  have hG4 : Gm4 K0u ℓ = Gs K0u ℓ * Gs K0u ℓ * (Gs K0u ℓ * Gs K0u ℓ) := rfl
  have hg : Gs K0u ℓ = 3 * Kb K0u ℓ ^ 8 := rfl
  have hcP : F.c ≤ Kb K0u ℓ := by omega
  have hc2P : 2 * F.c ≤ Kb K0u ℓ := by omega
  generalize F.X n ^ 4 = S4 at hmb hW hmN hS'
  generalize F.mbn K0u ℓ n = mb at hmb ⊢
  generalize F.Wn K0u ℓ n = W at hW ⊢
  generalize F.nodes n = mN at hmN ⊢
  generalize F.cmbn K0u ℓ = cm at hcm hmb
  generalize F.cWn K0u ℓ = cW at hcW hW hcm
  generalize F.c = c at hcP hc2P hcW hcm hmN
  generalize Gm4 K0u ℓ = G4 at hcW hcm hG4 ⊢
  generalize Gs K0u ℓ = g at hcW hG4 hg ⊢
  generalize Kb K0u ℓ = P at hP hl hS' hg hcP hc2P ⊢
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hP2 : 2304 ≤ P ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hP hP
  have hg9 : g ≤ P ^ 9 := by
    rw [hg]
    calc 3 * P ^ 8 ≤ P * P ^ 8 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 9 := by ring
  have h36 : G4 ≤ P ^ 36 := by
    rw [hG4]
    calc g * g * (g * g) ≤ P ^ 9 * P ^ 9 * (P ^ 9 * P ^ 9) :=
          Nat.mul_le_mul (Nat.mul_le_mul hg9 hg9) (Nat.mul_le_mul hg9 hg9)
      _ = P ^ 36 := by ring
  have h37 : ℓ * G4 ≤ P ^ 37 := calc ℓ * G4 ≤ P * P ^ 36 := Nat.mul_le_mul hl h36
      _ = P ^ 37 := by ring
  have hcW' : cW ≤ P ^ 39 := by
    have a1 : 1 ≤ P ^ 38 := Nat.one_le_pow _ _ (by omega)
    have a2 : c * g ≤ P ^ 38 := calc c * g ≤ P * P ^ 9 := Nat.mul_le_mul hcP hg9
        _ = P ^ 10 := by ring
        _ ≤ P ^ 38 := hpw 10 38 (by norm_num)
    have a3 : 2 * ℓ * G4 ≤ P ^ 38 := calc 2 * ℓ * G4 = 2 * (ℓ * G4) := by ring
        _ ≤ P * P ^ 37 := Nat.mul_le_mul (by omega) h37
        _ = P ^ 38 := by ring
    have a5 : c ≤ P ^ 38 := le_trans hcP (by simpa using hpw 1 38 (by norm_num))
    have a4 : 4 * P ^ 38 ≤ P ^ 39 := calc 4 * P ^ 38 ≤ P * P ^ 38 := Nat.mul_le_mul_right _ (by omega)
        _ = P ^ 39 := by ring
    omega
  have hcm' : cm ≤ P ^ 77 := by
    have a1 : 4 * ℓ * G4 * cW ≤ 4 * P ^ 76 := calc 4 * ℓ * G4 * cW = 4 * (ℓ * G4 * cW) := by ring
        _ ≤ 4 * (P ^ 37 * P ^ 39) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h37 hcW')
        _ = 4 * P ^ 76 := by ring
    have a2 : 2 * c + 9 ≤ P ^ 76 := le_trans (by nlinarith : 2 * c + 9 ≤ P ^ 2) (hpw 2 76 (by norm_num))
    have a4 : 5 * P ^ 76 ≤ P ^ 77 := calc 5 * P ^ 76 ≤ P * P ^ 76 := Nat.mul_le_mul_right _ (by omega)
        _ = P ^ 77 := by ring
    omega
  refine ⟨hg9, h36, h37, ?_, ?_, ?_⟩
  · calc mb ≤ cm * S4 := hmb
      _ ≤ P ^ 77 * P ^ 701 := Nat.mul_le_mul hcm' hS'
      _ = P ^ 778 := by ring
  · calc W + 1 ≤ cW * S4 := hW
      _ ≤ P ^ 39 * P ^ 701 := Nat.mul_le_mul hcW' hS'
      _ = P ^ 740 := by ring
  · calc mN ≤ c * S4 := hmN
      _ ≤ P * P ^ 701 := Nat.mul_le_mul hcP hS'
      _ = P ^ 702 := by ring

/-- Every logarithm is at most `801 P`. -/
theorem good_logsG (hS : F.Spec) {ℓ n : ℕ} (hc : 2 * F.c ≤ ℓ) (h : UGood ℓ n) :
    Nat.log 2 (F.mbn K0u ℓ n) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (F.Wn K0u ℓ n + 1) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (n + ℓ + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (F.mbn K0u ℓ n + 16 * n + Kb K0u ℓ + Gs K0u ℓ + F.nodes n + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (F.Wn K0u ℓ n + F.mbn K0u ℓ n + Gs K0u ℓ + Gs K0u ℓ + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (F.mbn K0u ℓ n + K0u + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (Kb K0u ℓ + 2) + 1 ≤ 801 * Kb K0u ℓ := by
  obtain ⟨hP, hl, -, hn, -⟩ := good_factsG hS hc h
  obtain ⟨hg, -, -, hmb, hW, hmN⟩ := good_boundsG hS hc h
  have hK0 : K0u = 48 := rfl
  rw [hK0]
  generalize F.mbn K0u ℓ n = mb at hmb ⊢
  generalize F.Wn K0u ℓ n = W at hW ⊢
  generalize F.nodes n = mN at hmN ⊢
  generalize Gs K0u ℓ = g at hg ⊢
  generalize Kb K0u ℓ = P at hP hl hn hg hmb hW hmN ⊢
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hP2 : 2304 ≤ P ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hP hP
  have hQ : 48 * P ^ 799 ≤ P ^ 800 := calc 48 * P ^ 799 ≤ P * P ^ 799 := Nat.mul_le_mul_right _ hP
      _ = P ^ 800 := by ring
  have hp1 : P ≤ P ^ 799 := by simpa using hpw 1 799 (by norm_num)
  have a1 : mb ≤ P ^ 799 := le_trans hmb (hpw _ _ (by norm_num))
  have a2 : W + 1 ≤ P ^ 799 := le_trans hW (hpw _ _ (by norm_num))
  have a3 : 16 * n ≤ P ^ 799 := calc 16 * n ≤ P ^ 2 * P ^ 700 := Nat.mul_le_mul (by omega) hn
      _ = P ^ 702 := by ring
      _ ≤ P ^ 799 := hpw _ _ (by norm_num)
  have a5 : g ≤ P ^ 799 := le_trans hg (hpw _ _ (by norm_num))
  have a6 : mN ≤ P ^ 799 := le_trans hmN (hpw _ _ (by norm_num))
  have a7 : 64 ≤ P ^ 799 := le_trans (by omega) (le_trans hP2 (hpw _ _ (by norm_num)))
  have key : ∀ x, x ≤ P ^ 800 → Nat.log 2 x + 1 ≤ 801 * P := fun x hx => by have := log_le_P hx; omega
  exact ⟨key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega),
    key _ (by omega), key _ (by omega)⟩

end NetFamily

end ECDLP.L60
