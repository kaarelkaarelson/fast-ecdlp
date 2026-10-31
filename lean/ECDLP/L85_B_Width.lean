import ECDLP.L85_B_Side

/-!
# L72 / Width: an explicit expression for the top width of the edge family (item 3)

`Ltop K g n = (K * Ub + g * (Ub / g + Wm)) / K^3`, `Ub = Uc * X^4`, `Wm = Wcn * X^3`, `X = 2^s`, `s = sOf n`.
`edgeL0 r K g` has `K`, `g`, `K^3` as literals (the `L0E` field of a `TopShape`); `edgeL0v r` reads them from the
variables `5, 6, 7` (the engine's literal variables), and the size parameter `s` from variable `11`.
Proved: value (`eval_edgeL0v`), literal-freeness (`edgeL0_LS`), variable bound, depth, and the cost bound
`cost <= PB DB V` from the family's requirement at `Wv V` (needs only `r + 1 <= 2^19000`).
-/
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB ECDLP.L65 ECDLP.L60 UCost85

/-- `X^c = 2^(c s)` read from variable 11 -/
def XpE (c : ℕ) : Ex := pow2 20 (.mul (.lit c) (.var 11))
def edgeU (r : ℕ) : Ex := .mul (.lit (Uc r)) (XpE 4)
def edgeW (r : ℕ) : Ex := .mul (.lit (Wcn r)) (XpE 3)

/-- the top width with `K`, `g`, `K^3` as literals -/
def edgeL0 (r K g : ℕ) : Ex :=
  .div (.add (.mul (.lit K) (edgeU r)) (.mul (.lit g) (.add (.div (edgeU r) (.lit g)) (edgeW r)))) (.lit (K ^ 3))

/-- the top width with `K`, `g`, `K^3` in the variables `5`, `6`, `7` -/
def edgeL0v (r : ℕ) : Ex :=
  .div (.add (.mul (.var 5) (edgeU r)) (.mul (.var 6) (.add (.div (edgeU r) (.var 6)) (edgeW r)))) (.var 7)

section eval
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_XpE (c : ℕ) : eval σ A (XpE c) = (2 ^ σ 11) ^ c := by
  simp only [XpE, eval_pow2, Ex.eval]; rw [← pow_mul, mul_comm]

theorem eval_edgeU (r : ℕ) : eval σ A (edgeU r) = Uc r * (2 ^ σ 11) ^ 4 := by
  simp only [edgeU, Ex.eval, eval_XpE]

theorem eval_edgeW (r : ℕ) : eval σ A (edgeW r) = Wcn r * (2 ^ σ 11) ^ 3 := by
  simp only [edgeW, Ex.eval, eval_XpE]

theorem eval_edgeL0 (r K g : ℕ) :
    eval σ A (edgeL0 r K g) = (K * (Uc r * (2 ^ σ 11) ^ 4) +
      g * (Uc r * (2 ^ σ 11) ^ 4 / g + Wcn r * (2 ^ σ 11) ^ 3)) / K ^ 3 := by
  simp only [edgeL0, Ex.eval, eval_edgeU, eval_edgeW]

theorem eval_edgeL0v (r K g : ℕ) (h5 : σ 5 = K) (h6 : σ 6 = g) (h7 : σ 7 = K ^ 3) :
    eval σ A (edgeL0v r) = (K * (Uc r * (2 ^ σ 11) ^ 4) +
      g * (Uc r * (2 ^ σ 11) ^ 4 / g + Wcn r * (2 ^ σ 11) ^ 3)) / K ^ 3 := by
  simp only [edgeL0v, Ex.eval, eval_edgeU, eval_edgeW, h5, h6, h7]

theorem edgeL0_eval_Ltop (r K g n : ℕ) (h : σ 11 = sOf n) :
    eval σ A (edgeL0 r K g) = LtopE r K g n := by
  rw [eval_edgeL0, h]; rfl

end eval

theorem edgeL0_LS (r K g : ℕ) : LS (topOk K g) (edgeL0 r K g) (edgeL0v r) := by
  have h5 : topOk K g 5 K := TopV.ok5
  have h6 : topOk K g 6 g := TopV.ok6
  have h7 : topOk K g 7 (K ^ 3) := TopV.ok7
  have hnb : ∀ x, 10 ≤ x → ∀ k, ¬ topOk K g x k := fun x hx => topOk_nb hx
  simp only [edgeL0, edgeL0v, edgeU, edgeW, XpE, pow2]
  repeat ls_step

theorem edgeL0v_vb (r : ℕ) : VB 1000 (edgeL0v r) := by
  simp only [edgeL0v, edgeU, edgeW, XpE, pow2, VB, and_true, true_and, and_self]; omega

theorem edgeL0v_dp (r : ℕ) : Ex.dp (edgeL0v r) ≤ 100 := by
  simp only [edgeL0v, edgeU, edgeW, XpE, pow2, Ex.dp]; omega

end ECDLP.L85B

namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB ECDLP.L65 ECDLP.L60 UCost85

theorem cube_le_two_pow : ∀ K : ℕ, 16 ≤ K → K ^ 3 ≤ 2 ^ (K - 1) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have h1 : (K + 1) ^ 3 ≤ 2 * K ^ 3 := by nlinarith [sq_nonneg K, Nat.zero_le K]
    have h2 : 2 ^ (K + 1 - 1) = 2 * 2 ^ (K - 1) := by
      rw [show K + 1 - 1 = (K - 1) + 1 by omega, pow_succ]; ring
    omega

theorem Kb_ge_K0 (K0 : ℕ) : ∀ d, K0 ≤ Kb K0 d
  | 0 => le_rfl
  | d + 1 => by
      have := Kb_ge_K0 K0 d
      show K0 ≤ (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8)
      have h1 : Kb K0 d ≤ Kb K0 d ^ 8 := Nat.le_self_pow (by norm_num) _
      nlinarith

/-- the numerator of the top width is below `W` when the width's exponential is -/
theorem arith_num (N K W : ℕ) (hK : 16 ≤ K) (h1 : K ^ 3 ≤ W) (h2 : 2 ^ (N / K ^ 3 * K) ≤ W) : N ≤ W := by
  have hK3 : 0 < K ^ 3 := by positivity
  obtain ⟨L, hL⟩ : ∃ L, L = N / K ^ 3 := ⟨_, rfl⟩
  rw [← hL] at h2
  have hN : N < K ^ 3 * (L + 1) := by
    have h3 := Nat.div_add_mod N (K ^ 3)
    have h4 := Nat.mod_lt N hK3
    rw [← hL] at h3
    rw [mul_add, mul_one]; omega
  rcases Nat.eq_zero_or_pos L with h0 | h0
  · rw [h0] at hN; omega
  · have c1 := cube_le_two_pow K hK
    have c2 : L + 1 ≤ 2 ^ L := Nat.succ_le_of_lt Nat.lt_two_pow_self
    have c3 : K ^ 3 * (L + 1) ≤ 2 ^ (K - 1) * 2 ^ L := Nat.mul_le_mul c1 c2
    have c4 : 2 ^ (K - 1) * 2 ^ L = 2 ^ (K - 1 + L) := (pow_add _ _ _).symm
    have c5 : K - 1 + L ≤ L * K := by
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; nlinarith
    have c6 : 2 ^ (K - 1 + L) ≤ 2 ^ (L * K) := Nat.pow_le_pow_right (by norm_num) c5
    omega

end ECDLP.L85B

namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB ECDLP.L65 ECDLP.L60 UCost85

theorem num_le {r n ℓ W : ℕ} (R : EdgeReq r W 2 K0u ℓ n) :
    Kb K0u ℓ * Ub r n + Gs K0u ℓ * (Ub r n / Gs K0u ℓ + Wm r n) ≤ W := by
  have hK48 : 48 ≤ Kb K0u ℓ := Kb_ge_K0 K0u ℓ
  refine arith_num _ (Kb K0u ℓ) W (by omega) (by have := R.hK3; omega) ?_
  exact R.hLK

/-- **Value bound of the literal-free top width** at the value bound `W` (a family requirement at `W`). -/
theorem edgeL0v_bdd {r n ℓ W : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hr : r + 1 ≤ 2 ^ 19000)
    (R : EdgeReq r W 2 K0u ℓ n)
    (tk : ∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) (h11 : σ 11 = sOf n) :
    Bdd W σ A (edgeL0v r) := by
  set K := Kb K0u ℓ with hKdef
  set g := 3 * K ^ 8 with hgdef
  have hK48 : 48 ≤ K := Kb_ge_K0 K0u ℓ
  have hg1 : 1 ≤ g := by have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have hKG : K * g ≤ W := R.hKG
  have hK3 : 64 * K ^ 3 ≤ W := R.hK3
  have hU : Ub r n ≤ W := ok_U0 hr R
  have e5 : σ 5 = K := tk 5 K TopV.ok5
  have e6 : σ 6 = g := tk 6 g TopV.ok6
  have e7 : σ 7 = K ^ 3 := tk 7 (K ^ 3) TopV.ok7
  set X := 2 ^ sOf n with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hsX : sOf n < X := Nat.lt_two_pow_self
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) _
  have hX34 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
  have hUdef : Ub r n = Uc r * X ^ 4 := rfl
  have hWdef : Wm r n = Wcn r * X ^ 3 := rfl
  have hUc4 : 4 ≤ Uc r := by unfold Uc; omega
  have hWc1 : 1 ≤ Wcn r := by unfold Wcn; omega
  have hX4U : X ^ 4 ≤ Ub r n := by rw [hUdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hUcU : Uc r ≤ Ub r n := by rw [hUdef]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hX3W : X ^ 3 ≤ Wm r n := by rw [hWdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hWcW : Wcn r ≤ Wm r n := by rw [hWdef]; exact Nat.le_mul_of_pos_right _ (by positivity)
  -- the numerator
  set N := K * Ub r n + g * (Ub r n / g + Wm r n) with hN
  have hNW : N ≤ W := num_le R
  have hKU : K * Ub r n ≤ N := Nat.le_add_right _ _
  have hgP : g * (Ub r n / g + Wm r n) ≤ N := Nat.le_add_left _ _
  have hP : Ub r n / g + Wm r n ≤ g * (Ub r n / g + Wm r n) := Nat.le_mul_of_pos_left _ (by omega)
  have hUK : Ub r n ≤ K * Ub r n := Nat.le_mul_of_pos_left _ (by omega)
  have hWmN : Wm r n ≤ N := le_trans (Nat.le_add_left _ _) (le_trans hP hgP)
  have hW2 : 2 ≤ W := by have : 0 < K ^ 3 := by positivity
                         omega
  have h4X : 4 * X ^ 4 ≤ Ub r n := by rw [hUdef]; exact Nat.mul_le_mul_right _ hUc4
  have s4 : 4 * sOf n ≤ W := by omega
  have s3 : 3 * sOf n ≤ W := by omega
  have q4 : 2 ^ (4 * sOf n) = X ^ 4 := by rw [hX, ← pow_mul, mul_comm]
  have q3 : 2 ^ (3 * sOf n) = X ^ 3 := by rw [hX, ← pow_mul, mul_comm]
  have hUX : Uc r * X ^ 4 ≤ W := by rw [← hUdef]; exact hU
  have hWX : Wcn r * X ^ 3 ≤ W := by rw [← hWdef]; omega
  have hp4 : Bdd W σ A (XpE 4) :=
    B_pow2 (B_mul (B_lit (by omega)) (B_var (by rw [h11]; omega))
      (by simp only [Ex.eval, h11]; omega)) hW2 (by
        simp only [Ex.eval, h11]; rw [q4]; omega)
  have hp3 : Bdd W σ A (XpE 3) :=
    B_pow2 (B_mul (B_lit (by omega)) (B_var (by rw [h11]; omega))
      (by simp only [Ex.eval, h11]; omega)) hW2 (by
        simp only [Ex.eval, h11]; rw [q3]; omega)
  have eU : eval σ A (edgeU r) = Ub r n := by rw [eval_edgeU, h11]; rfl
  have eWm : eval σ A (edgeW r) = Wm r n := by rw [eval_edgeW, h11]; rfl
  have hBU : Bdd W σ A (edgeU r) :=
    B_mul (B_lit (by omega)) hp4 (by rw [eval_XpE, h11]; exact hUX)
  have hBW : Bdd W σ A (edgeW r) :=
    B_mul (B_lit (by omega)) hp3 (by rw [eval_XpE, h11]; exact hWX)
  refine B_div (B_add (B_mul (B_var (by rw [e5]; exact le_trans (Nat.le_mul_of_pos_right _ hg1) hKG)) hBU ?_)
    (B_mul (B_var (by rw [e6]; exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) hKG)) (B_add (B_div hBU (B_var (by rw [e6]; exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) hKG))) hBW ?_) ?_) ?_)
    (B_var (by rw [e7]; omega))
  · simp only [Ex.eval, e5, eU]; omega
  · simp only [Ex.eval, e6, eU, eWm]; omega
  · simp only [Ex.eval, e6, eU, eWm]; omega
  · simp only [Ex.eval, e5, e6, eU, eWm]; omega

/-- **The cost of the top width** (`TopIface.l0_cost`). -/
theorem edgeL0v_cost {r n ℓ V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hr : r + 1 ≤ 2 ^ 19000)
    (R : EdgeReq r (Wv V) 2 K0u ℓ n)
    (tk : ∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) (h11 : σ 11 = sOf n) :
    cost σ A (edgeL0v r) ≤ PB DB V :=
  cost_le_PB (edgeL0v_bdd hr R tk h11) (edgeL0v_dp r)

end ECDLP.L85B
