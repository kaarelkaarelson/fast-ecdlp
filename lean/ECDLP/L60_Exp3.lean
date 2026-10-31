import ECDLP.L60_Exp2

/-!
# L60: the exponent of the uniform engine, part 3: `uni_exp_gen`

Generalisation of `small_zC`, `small_zP`, `small_zT`, `Zof`, `Zu`, `uni_exp` (`FactoringAux/UniExp.lean`).
-/

namespace ECDLP.L60

open Factoring.Aux

namespace NetFamily

variable {F : NetFamily}

/-- **The chain's exponents are `o(n)`.** -/
theorem small_zCG (hS : F.Spec) : USmall F.zC := by
  intro k hk
  obtain ⟨D, hD⟩ : ∃ D, D = 28 * F.Wcon * k := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ := ev_WG hS
  obtain ⟨X2, hX2⟩ := ev_W0G hS (2 * k * 24 ^ D)
  refine ⟨X1 + X2 + 2 * F.c + 2 * k * 8017 + 4 * k + 4 * k * 801, fun ℓ n hX h => ?_⟩
  have hP := Kb48_ge48 ℓ
  have hcl : 2 * F.c ≤ ℓ := by omega
  obtain ⟨-, h36, -⟩ := good_boundsG hS hcl h
  obtain ⟨-, -, -, -, hA2, hA3, -⟩ := good_logsG hS hcl h
  have hW := hX1 ℓ n (by omega) h
  have hW0 := hX2 ℓ n (by omega) h
  have q1 := ev_poly (2 * k * 8017) 37 (by norm_num) (by omega) h
  have q2 := ev_poly (4 * k) 36 (by norm_num) (by omega) h
  have q3 := ev_poly (4 * k * 801) 1 (by norm_num) (by omega) h
  rw [pow_one] at q3
  have hG4 : Gs K0u ℓ * Gs K0u ℓ * (Gs K0u ℓ * Gs K0u ℓ) = Gm4 K0u ℓ := rfl
  have h24 : 1 ≤ 24 ^ D := Nat.one_le_pow _ _ (by norm_num)
  have hkW0 : 2 * k * F.W0n K0u ℓ n ≤ n :=
    le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h24)) hW0
  show k * chainMax (F.mbn K0u ℓ n) K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) ≤ n
  suffices hc : chainMax (F.mbn K0u ℓ n) K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) ≤ n / k by
    exact le_trans (Nat.mul_le_mul_left _ hc) (Nat.mul_div_le n k)
  refine chainMax_le K0u (n / k) (F.mbn K0u ℓ n) (F.Wn K0u ℓ n) (F.W0n K0u ℓ n) (Gs K0u ℓ) (le_refl _) ?_ ?_ ℓ _
    (K_le_G _) (chain_hyp1 hS (K0 := K0u) (by norm_num) ℓ n)
    (chain_hyp2 hS (K0 := K0u) (by norm_num) ℓ n)
  · intro d N hN hN23
    rw [hG4] at hN ⊢
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    set G4 := Gm4 K0u ℓ
    have hK48 : 48 ≤ Kb K0u d := Kb48_ge48 d
    have hdK : d < Kb K0u d := lt_Kb48 d
    set B := Nat.log 2 (F.Wn K0u ℓ n + F.mbn K0u ℓ n + Gs K0u ℓ + Gs K0u ℓ + 64) + 1 with hB
    have hpoly : 2 * k * (7 + (G4 + 9) * B) ≤ n := by
      have t1 : (G4 + 9) * B ≤ 10 * Kb K0u ℓ ^ 36 * (801 * Kb K0u ℓ) := by
        refine Nat.mul_le_mul ?_ hA2
        have : 1 ≤ Kb K0u ℓ ^ 36 := Nat.one_le_pow _ _ (by omega)
        omega
      have t2 : 10 * Kb K0u ℓ ^ 36 * (801 * Kb K0u ℓ) = 8010 * Kb K0u ℓ ^ 37 := by ring
      have t3 : 1 ≤ Kb K0u ℓ ^ 37 := Nat.one_le_pow _ _ (by omega)
      calc 2 * k * (7 + (G4 + 9) * B) ≤ 2 * k * (8017 * Kb K0u ℓ ^ 37) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * k * 8017 * Kb K0u ℓ ^ 37 := by ring
        _ ≤ n := q1
    have hmain : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) ≤ n := by
      by_cases hDK : D ≤ Kb K0u d
      · refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
        calc 2 * k * (14 * (N + 2 * G4)) ≤ 2 * k * (14 * (F.Wcon * n)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
          _ = D * n := by rw [hD]; ring
          _ ≤ Kb K0u d * n := Nat.mul_le_mul_right _ hDK
      · have hd1 : d + 1 ≤ D := by omega
        have hND : N ≤ 24 ^ D * F.W0n K0u ℓ n := by
          have e : 23 ^ D = 23 ^ (D - (d + 1)) * 23 ^ (d + 1) := by rw [← pow_add]; congr 1; omega
          have e' : 24 ^ D = 24 ^ (D - (d + 1)) * 24 ^ (d + 1) := by rw [← pow_add]; congr 1; omega
          calc N ≤ 23 ^ D * N := Nat.le_mul_of_pos_left _ (by positivity)
            _ = 23 ^ (D - (d + 1)) * (23 ^ (d + 1) * N) := by rw [e, mul_assoc]
            _ ≤ 24 ^ (D - (d + 1)) * (24 ^ (d + 1) * F.W0n K0u ℓ n) :=
                Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) hN23
            _ = 24 ^ D * F.W0n K0u ℓ n := by rw [e', mul_assoc]
        have hdiv : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) ≤ k * (N + 2 * G4) := by
          refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) ?_
          refine le_trans (Nat.div_le_div_left hK48 (by norm_num)) ?_
          have : 2 * k * (14 * (N + 2 * G4)) = 28 * (k * (N + 2 * G4)) := by ring
          rw [this]; omega
        have h1 : 2 * (k * N) ≤ n := by
          calc 2 * (k * N) ≤ 2 * (k * (24 ^ D * F.W0n K0u ℓ n)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hND)
            _ = 2 * k * 24 ^ D * F.W0n K0u ℓ n := by ring
            _ ≤ n := hW0
        have h2 : 4 * k * G4 ≤ n := le_trans (Nat.mul_le_mul_left _ h36) q2
        have e : k * (N + 2 * G4) = k * N + 2 * (k * G4) := by ring
        have e2 : 4 * k * G4 = 4 * (k * G4) := by ring
        omega
    have e1 : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) = 2 * (k * (14 * (N + 2 * G4) / Kb K0u d)) := by ring
    have e2 : 2 * k * (7 + (G4 + 9) * B) = 2 * (k * (7 + (G4 + 9) * B)) := by ring
    have e3 : (14 * (N + 2 * G4) / Kb K0u d + 7 + (G4 + 9) * B) * k =
        k * (14 * (N + 2 * G4) / Kb K0u d) + k * (7 + (G4 + 9) * B) := by ring
    omega
  · apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have e1 : (F.W0n K0u ℓ n + 2 * (Nat.log 2 (F.mbn K0u ℓ n + K0u + 64) + 1)) * k =
        k * F.W0n K0u ℓ n + 2 * (k * (Nat.log 2 (F.mbn K0u ℓ n + K0u + 64) + 1)) := by ring
    have e2 : 2 * k * F.W0n K0u ℓ n = 2 * (k * F.W0n K0u ℓ n) := by ring
    have e3 : 4 * (k * (Nat.log 2 (F.mbn K0u ℓ n + K0u + 64) + 1)) ≤ 4 * k * 801 * Kb K0u ℓ := by
      calc 4 * (k * (Nat.log 2 (F.mbn K0u ℓ n + K0u + 64) + 1)) ≤ 4 * (k * (801 * Kb K0u ℓ)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA3)
        _ = 4 * k * 801 * Kb K0u ℓ := by ring
    omega

/-- The polynomial items. -/
def zP (F : NetFamily) (ℓ n : ℕ) : ℕ :=
  ℓ * Gm4 K0u ℓ * (Nat.log 2 (F.Wn K0u ℓ n + 1) + 1) + (Nat.log 2 (F.mbn K0u ℓ n) + 1) +
  (Nat.log 2 (n + ℓ + 64) + 1) + 40 * (Nat.log 2 (Kb K0u ℓ) + 1) +
  (3 * Kb K0u ℓ ^ 8 + 50) * (Nat.log 2 (Kb K0u ℓ + 2) + 1)

theorem small_zPG (hS : F.Spec) : USmall F.zP := by
  refine small_poly_thr (2 * F.c) 36000 38 (by norm_num) fun ℓ n hc h => ?_
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  obtain ⟨a1, a2, a3, -, -, -, a7⟩ := good_logsG hS hc h
  have a4 : Nat.log 2 (Kb K0u ℓ) + 1 ≤ 801 * Kb K0u ℓ :=
    le_trans (Nat.add_le_add_right (Nat.log_mono_right (by omega : Kb K0u ℓ ≤ Kb K0u ℓ + 2)) 1) a7
  unfold zP
  set P := Kb K0u ℓ
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have p1 : P ≤ P ^ 38 := by simpa using hpw 1 38 (by norm_num)
  have t1 : ℓ * Gm4 K0u ℓ * (Nat.log 2 (F.Wn K0u ℓ n + 1) + 1) ≤ 801 * P ^ 38 :=
    calc _ ≤ P ^ 37 * (801 * P) := Nat.mul_le_mul h37 a2
      _ = 801 * P ^ 38 := by ring
  have t5 : (3 * P ^ 8 + 50) * (Nat.log 2 (P + 2) + 1) ≤ 801 * P ^ 38 := by
    have h1 : 48 ≤ P ^ 8 := le_trans hP (by simpa using hpw 1 8 (by norm_num))
    have h2 : 48 * P ^ 8 ≤ P * P ^ 8 := Nat.mul_le_mul_right _ hP
    have h3 : 3 * P ^ 8 + 50 ≤ P ^ 9 := by
      have e : P * P ^ 8 = P ^ 9 := by ring
      omega
    calc _ ≤ P ^ 9 * (801 * P) := Nat.mul_le_mul h3 a7
      _ = 801 * P ^ 10 := by ring
      _ ≤ 801 * P ^ 38 := Nat.mul_le_mul_left _ (hpw _ _ (by norm_num))
  generalize (3 * P ^ 8 + 50) * (Nat.log 2 (P + 2) + 1) = T5 at t5 ⊢
  omega

/-- The top's exponents. -/
def zT (F : NetFamily) (ℓ n : ℕ) : ℕ := F.eTop K0u ℓ n (F.mbn K0u ℓ n)

theorem small_zTG (hS : F.Spec) : USmall F.zT :=
  small_mono (fun ℓ n _ => eTop_splitG hS ℓ n _) (small_add (small_f1G hS) (small_add (small_f2G hS) (small_f3G hS)))

/-- The exponent at `ℓ` levels. -/
def Zof (F : NetFamily) (ℓ n : ℕ) : ℕ := F.zT ℓ n + F.zC ℓ n + F.zP ℓ n

/-- **The exponent of the uniform engine** at input length `n`. -/
def Zu (F : NetFamily) (n : ℕ) : ℕ := F.Zof (ellOf n) n

theorem small_ZofG (hS : F.Spec) : USmall F.Zof :=
  small_add (small_add (small_zTG hS) (small_zCG hS)) (small_zPG hS)

/-- **The exponent of the uniform engine is `o(n)`, for every family with the size interface.**
One `Z` bounds every requirement of the uniform engine (`K0 = 48`, `ℓ = ellOf n`), and
`Z n ≤ n / k + C_k` for every `k`. -/
theorem uni_exp_gen (hS : F.Spec) : ∃ Z : ℕ → ℕ,
    (∀ n, F.eTop K0u (ellOf n) n (2 * F.Mof K0u (ellOf n) n + 1) ≤ Z n) ∧
    (∀ n, DeepE (Z n) (2 * F.Mof K0u (ellOf n) n + 1) K0u (ellOf n)
      (F.Ltop (Kb K0u (ellOf n)) (Gs K0u (ellOf n)) n)) ∧
    (∀ n, NPof K0u (ellOf n) (F.Ltop (Kb K0u (ellOf n)) (Gs K0u (ellOf n)) n) ≤ 2 ^ Z n) ∧
    (∀ n, 2 * F.Mof K0u (ellOf n) n + 1 ≤ 2 ^ Z n) ∧ (∀ n, n + ellOf n + 64 ≤ 2 ^ Z n) ∧
    (∀ n, Kb K0u (ellOf n) ^ 40 ≤ 2 ^ Z n) ∧ (∀ n, lvlV (Kb K0u (ellOf n)) ≤ 2 ^ Z n) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, Z n ≤ n / k + C := by
  have hT : ∀ n, F.zT (ellOf n) n ≤ F.Zu n := fun n => by unfold Zu Zof; omega
  have hC : ∀ n, F.zC (ellOf n) n ≤ F.Zu n := fun n => by unfold Zu Zof; omega
  have hP : ∀ n, F.zP (ellOf n) n ≤ F.Zu n := fun n => by unfold Zu Zof; omega
  refine ⟨F.Zu, fun n => hT n, fun n => deepE_chainMax _ _ _ _ _ (hC n), fun n => ?_, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, small_bound (small_ZofG hS)⟩
  · have h := hP n
    unfold zP at h
    refine le_trans (NPof_le K0u (F.Wn K0u (ellOf n) n) (Gs K0u (ellOf n)) (le_refl _) (ellOf n) _
      (K_le_G _) (chain_hyp1 hS (K0 := K0u) (by norm_num) (ellOf n) n)) ?_
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    show ellOf n * Gm4 K0u (ellOf n) * (Nat.log 2 (F.Wn K0u (ellOf n) n + 1) + 1) ≤ F.Zu n
    omega
  · have h := hP n
    unfold zP at h
    exact le_trans (le_two_pow_log _).le (two_pow_le (by unfold mbn at h; omega))
  · have h := hP n
    unfold zP at h
    exact le_trans (le_two_pow_log _).le (two_pow_le (by omega))
  · have h := hP n
    unfold zP at h
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    omega
  · have h := hP n
    unfold zP at h
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    omega

end NetFamily

end ECDLP.L60
