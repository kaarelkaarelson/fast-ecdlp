import ECDLP.L60_Exp

/-!
# L60: the exponent of the uniform engine, part 2 (top, chain, assembly)

Generalisation of `FactoringAux/UniExp.lean` lines 140-505: `eTop_split`, `small_f1..3`, `ev_W`,
`ev_W0`, `small_zC`, `small_zP`, `uni_exp`, for an abstract `NetFamily` with its `Spec`.
-/

namespace ECDLP.L60

open Factoring.Aux

theorem small_poly_thr {f : ℕ → ℕ → ℕ} (X0 c a : ℕ) (ha : a < 40)
    (h : ∀ ℓ n, X0 ≤ ℓ → UGood ℓ n → f ℓ n ≤ c * Kb K0u ℓ ^ a) : USmall f :=
  fun k _ => ⟨X0 + k * c, fun ℓ n hX hg => by
    have := ev_poly (k * c) a ha (by omega) hg
    calc k * f ℓ n ≤ k * (c * Kb K0u ℓ ^ a) := Nat.mul_le_mul_left _ (h ℓ n (by omega) hg)
      _ = k * c * Kb K0u ℓ ^ a := by ring
      _ ≤ n := this⟩

namespace NetFamily

variable {F : NetFamily}

/-! ### The top -/

theorem eTop_splitG (hS : F.Spec) (ℓ n mb : ℕ) : F.eTop K0u ℓ n mb ≤
    F.c * F.X n ^ 4 / Kb K0u ℓ + (2 * F.c * (Gs K0u ℓ * F.X n ^ 3) + F.ePoly (Kb K0u ℓ) (Gs K0u ℓ) n mb) := by
  have hK2 : 2 ≤ Kb K0u ℓ := le_trans (by norm_num) (Kb48_ge48 ℓ)
  have hKg : Kb K0u ℓ ≤ Gs K0u ℓ := K_le_G _
  have h := hS.eFam_le (Kb K0u ℓ) (Gs K0u ℓ) n hK2 hKg
  have hK1 : 0 < Kb K0u ℓ := by omega
  have hg0 : 1 ≤ Gs K0u ℓ := by omega
  have h3 : F.c * F.X n ^ 3 ≤ F.c * (Gs K0u ℓ * F.X n ^ 3) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hg0)
  have h2 : F.eFam (Kb K0u ℓ) (Gs K0u ℓ) n ≤ F.c * F.X n ^ 4 / Kb K0u ℓ +
      (F.c * (Gs K0u ℓ * F.X n ^ 3) + F.c * F.X n ^ 3) := by
    have : F.eFam (Kb K0u ℓ) (Gs K0u ℓ) n ≤ (F.c * F.X n ^ 4 + Kb K0u ℓ * (F.c * (Gs K0u ℓ * F.X n ^ 3) + F.c * F.X n ^ 3)) / Kb K0u ℓ :=
      (Nat.le_div_iff_mul_le hK1).mpr (by rw [mul_comm]; exact h)
    rwa [Nat.add_mul_div_left _ _ hK1] at this
  unfold eTop
  have e : 2 * F.c * (Gs K0u ℓ * F.X n ^ 3) = 2 * (F.c * (Gs K0u ℓ * F.X n ^ 3)) := by ring
  omega

theorem small_f1G (hS : F.Spec) : USmall (fun ℓ n => F.c * F.X n ^ 4 / Kb K0u ℓ) := by
  intro k hk
  refine ⟨2 * k * F.c * F.c, fun ℓ n hX h => ?_⟩
  have hlt := lt_Kb48 ℓ
  have hP := Kb48_ge48 ℓ
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h.2.1
  have hS4 := hS.X4_le n
  have hc := F.hc
  show k * (F.c * F.X n ^ 4 / Kb K0u ℓ) ≤ n
  generalize F.X n ^ 4 = S4 at hS4 ⊢
  generalize Kb K0u ℓ = P at hlt hP ⊢
  refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
  have e0 : S4 ≤ 2 * F.c * n := by nlinarith
  have e1 : k * (F.c * S4) ≤ k * (F.c * (2 * F.c * n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e0)
  have e2 : (2 * k * F.c * F.c) * n ≤ P * n := Nat.mul_le_mul_right _ (by omega)
  have e3 : k * (F.c * (2 * F.c * n)) = (2 * k * F.c * F.c) * n := by ring
  omega

/-- The absorption of `a · g · X^3` into `n`. -/
theorem ev_gX3 (hS : F.Spec) (a : ℕ) : ∃ X0, ∀ ℓ n, X0 ≤ ℓ → UGood ℓ n →
    a * (Gs K0u ℓ * F.X n ^ 3) ≤ n := by
  obtain ⟨M0, hM0⟩ : ∃ M0, M0 = 12 * 48 ^ 3 * F.c ^ 4 * a ^ 4 := ⟨_, rfl⟩
  refine ⟨4 * M0 + 1, fun ℓ n hX h => ?_⟩
  have hP := Kb48_ge48 ℓ
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h.2.1
  have hev := ev_poly (4 * M0 + 1) 32 (by norm_num) hX h
  have hS4 := hS.X4_le n
  have hc := F.hc
  obtain ⟨β, hβ⟩ : ∃ β, β = 4 * F.c * a * Gs K0u ℓ := ⟨_, rfl⟩
  have hab := absorb_cube β (F.X n)
  have e1 : β * (4 * β) ^ 3 = M0 * Kb K0u ℓ ^ 32 := by
    rw [hβ, hM0]; show _ = _; 
    show (4 * F.c * a * (3 * Kb K0u ℓ ^ 8)) * (4 * (4 * F.c * a * (3 * Kb K0u ℓ ^ 8))) ^ 3 = _; ring
  have e2 : β * F.X n ^ 3 = 4 * F.c * (a * (Gs K0u ℓ * F.X n ^ 3)) := by rw [hβ]; ring
  rw [e1] at hab
  generalize a * (Gs K0u ℓ * F.X n ^ 3) = Y at e2 ⊢
  generalize β * F.X n ^ 3 = BX at e2 hab
  generalize F.X n ^ 4 = S4 at hS4 hab
  generalize Kb K0u ℓ ^ 32 = P32 at hev hab
  have q1 : 4 * M0 * P32 ≤ n := by nlinarith
  have q2 : n ≤ F.c * n := Nat.le_mul_of_pos_left _ (by omega)
  have q3 : F.c ≤ F.c * n := Nat.le_mul_of_pos_right _ hn1
  have q4 : 4 * (S4 / 4) ≤ S4 := Nat.mul_div_le S4 4
  have q5 : 4 * (M0 * P32) = 4 * M0 * P32 := by ring
  have : 16 * F.c * Y ≤ 3 * F.c * n := by
    have : 4 * BX ≤ 4 * (S4 / 4 + M0 * P32) := Nat.mul_le_mul_left _ hab
    have : 4 * BX = 16 * F.c * Y := by rw [e2]; ring
    nlinarith
  have : F.c * (16 * Y) ≤ F.c * (3 * n) := by nlinarith
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem small_f2G (hS : F.Spec) : USmall (fun ℓ n => 2 * F.c * (Gs K0u ℓ * F.X n ^ 3)) := by
  intro k hk
  obtain ⟨X0, hX0⟩ := ev_gX3 hS (k * (2 * F.c))
  refine ⟨X0, fun ℓ n hX h => ?_⟩
  have := hX0 ℓ n hX h
  calc k * (2 * F.c * (Gs K0u ℓ * F.X n ^ 3)) = k * (2 * F.c) * (Gs K0u ℓ * F.X n ^ 3) := by ring
    _ ≤ n := this

theorem small_f3G (hS : F.Spec) :
    USmall (fun ℓ n => F.ePoly (Kb K0u ℓ) (Gs K0u ℓ) n (F.mbn K0u ℓ n)) := by
  refine small_poly_thr (2 * F.c) 801 10 (by norm_num) fun ℓ n hc h => ?_
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, -, hA, -⟩ := good_logsG hS hc h
  unfold ePoly
  have hg : Gs K0u ℓ + 4 ≤ Kb K0u ℓ ^ 9 := by
    show 3 * Kb K0u ℓ ^ 8 + 4 ≤ _
    have h1 : 1 ≤ Kb K0u ℓ ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h2 : 48 * Kb K0u ℓ ^ 8 ≤ Kb K0u ℓ * Kb K0u ℓ ^ 8 := Nat.mul_le_mul_right _ hP
    have e : Kb K0u ℓ * Kb K0u ℓ ^ 8 = Kb K0u ℓ ^ 9 := by ring
    omega
  calc _ ≤ Kb K0u ℓ ^ 9 * (801 * Kb K0u ℓ) := Nat.mul_le_mul hg hA
    _ = 801 * Kb K0u ℓ ^ 10 := by ring

/-! ### The chain -/

/-- The constant bounding `W` by a multiple of `n`. -/
def Wcon (F : NetFamily) : ℕ := 2 * F.c * F.c + 2

/-- The bits of every level: `W ≤ Wcon · n`. -/
theorem ev_WG (hS : F.Spec) : ∃ X, ∀ ℓ n, X ≤ ℓ → UGood ℓ n → F.Wn K0u ℓ n ≤ F.Wcon * n := by
  obtain ⟨X1, hX1⟩ := ev_gX3 hS F.c
  refine ⟨X1 + 2, fun ℓ n hX h => ?_⟩
  have hev := ev_poly 2 37 (by norm_num) (by omega) h
  have hP := Kb48_ge48 ℓ
  have h1 := hX1 ℓ n (by omega) h
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h.2.1
  have hS4 := hS.X4_le n
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  have hc := F.hc
  have hW : F.Wn K0u ℓ n = F.c * F.X n ^ 4 + F.c * (Gs K0u ℓ * F.X n ^ 3) + 2 * ℓ * Gm4 K0u ℓ := rfl
  have e3 : 2 * ℓ * Gm4 K0u ℓ = 2 * (ℓ * Gm4 K0u ℓ) := by ring
  have p1 : 2 * Kb K0u ℓ ^ 37 ≤ n := hev
  have p2 : 2 * (ℓ * Gm4 K0u ℓ) ≤ 2 * Kb K0u ℓ ^ 37 := Nat.mul_le_mul_left _ h37
  have q0 : F.X n ^ 4 ≤ 2 * F.c * n := by nlinarith
  have q1 : F.c * F.X n ^ 4 ≤ F.c * (2 * F.c * n) := Nat.mul_le_mul_left _ q0
  have q2 : F.c * (2 * F.c * n) = 2 * F.c * F.c * n := by ring
  have q3 : F.Wcon * n = 2 * F.c * F.c * n + 2 * n := by unfold Wcon; ring
  omega

/-- The bits of the bottom are `o(n)`. -/
theorem ev_W0G (hS : F.Spec) (a : ℕ) : ∃ X, ∀ ℓ n, X ≤ ℓ → UGood ℓ n → a * F.W0n K0u ℓ n ≤ n := by
  obtain ⟨X1, hX1⟩ := ev_WG hS
  obtain ⟨j, hj⟩ := exists_ell (2 * a * F.Wcon)
  refine ⟨X1 + j + 6 * a, fun ℓ n hX h => ?_⟩
  have hW := hX1 ℓ n (by omega) h
  have hWc : 1 ≤ F.Wcon := by unfold Wcon; omega
  have hb : 2 * a * F.Wcon * 23 ^ ℓ ≤ 24 ^ ℓ :=
    pow_dec (le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))) hj) ℓ (by omega)
  have hev := ev_poly (6 * a) 37 (by norm_num) (by omega) h
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  have hNt : F.Ntn K0u ℓ n ≤ F.Wn K0u ℓ n := by unfold Wn; omega
  have hW0 : F.W0n K0u ℓ n = 23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0u ℓ := rfl
  have m1 : 2 * a * (23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ) ≤ n := by
    refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
    calc 2 * a * (23 ^ ℓ * F.Ntn K0u ℓ n) ≤ 2 * a * (23 ^ ℓ * (F.Wcon * n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans hNt hW))
      _ = (2 * a * F.Wcon * 23 ^ ℓ) * n := by ring
      _ ≤ 24 ^ ℓ * n := Nat.mul_le_mul_right _ hb
  have m2 : 2 * a * (1 + 2 * ℓ * Gm4 K0u ℓ) ≤ n := by
    have : 1 + 2 * ℓ * Gm4 K0u ℓ ≤ 3 * Kb K0u ℓ ^ 37 := by
      have : 1 ≤ Kb K0u ℓ ^ 37 := Nat.one_le_pow _ _ (by omega)
      have : 2 * ℓ * Gm4 K0u ℓ = 2 * (ℓ * Gm4 K0u ℓ) := by ring
      omega
    calc _ ≤ 2 * a * (3 * Kb K0u ℓ ^ 37) := Nat.mul_le_mul_left _ this
      _ = 6 * a * Kb K0u ℓ ^ 37 := by ring
      _ ≤ n := hev
  rw [hW0]
  have e : a * (23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0u ℓ) =
      a * (23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ) + a * (1 + 2 * ℓ * Gm4 K0u ℓ) := by ring
  have e2 : 2 * a * (23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ) = 2 * (a * (23 ^ ℓ * F.Ntn K0u ℓ n / 24 ^ ℓ)) := by ring
  have e3 : 2 * a * (1 + 2 * ℓ * Gm4 K0u ℓ) = 2 * (a * (1 + 2 * ℓ * Gm4 K0u ℓ)) := by ring
  omega

/-- The largest exponent along the chain. -/
def zC (F : NetFamily) (ℓ n : ℕ) : ℕ :=
  chainMax (F.mbn K0u ℓ n) K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)

end NetFamily

end ECDLP.L60
