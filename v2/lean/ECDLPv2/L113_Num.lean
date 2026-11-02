import ECDLPv2.L113_Crt
import FactoringAux.EngineMain

/-!
# L113 / Num: the numerical hypotheses of `crtC_run` for the counting application
* `hbig_of_lt_pow` : every positive common multiple of `1..2M` (`M = n+ML+4`) exceeds any `V < 2^(n+ML)`;
  applies to `V = D * c` (`D ≤ 2^ML`, `c < 2^n`) and to `V = D`.
* `fact_lt_pow` : `(K+1)! < 2^((K+1)^2)`, the width condition of `crtC_run`.
-/
set_option linter.unusedVariables false
namespace ECDLP.L113

theorem hbig_of_lt_pow {n ML V : ℕ} (hV : V < 2 ^ (n + ML)) :
    ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ 2 * (n + ML + 4) → i ∣ Y) → V < Y := by
  apply big_of_lt (M := n + ML + 4) (by omega)
  have h2 := Factoring.Aux.two_pow_big (n + ML)
  calc (2 * (n + ML + 4) + 1) * V < (2 * (n + ML + 4) + 1) * 2 ^ (n + ML) := Nat.mul_lt_mul_of_pos_left hV (by omega)
    _ ≤ 2 ^ (n + ML + 8) * 2 ^ (n + ML) := Nat.mul_le_mul_right _ (by omega)
    _ = 4 ^ (n + ML + 4) := by
        rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; ring

theorem hbig_count {n ML D c : ℕ} (hDl : D ≤ 2 ^ ML) (hc : c < 2 ^ n) :
    ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ 2 * (n + ML + 4) → i ∣ Y) → D * c < Y := by
  apply hbig_of_lt_pow
  calc D * c ≤ 2 ^ ML * c := Nat.mul_le_mul_right _ hDl
    _ < 2 ^ ML * 2 ^ n := Nat.mul_lt_mul_of_pos_left hc (by positivity)
    _ = 2 ^ (n + ML) := by ring

theorem hbig_mult {n ML D : ℕ} (hn : 1 ≤ n) (hDl : D ≤ 2 ^ ML) :
    ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ 2 * (n + ML + 4) → i ∣ Y) → D < Y := by
  apply hbig_of_lt_pow
  calc D ≤ 2 ^ ML := hDl
    _ < 2 ^ (n + ML) := by
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem fact_lt_pow (K : ℕ) : (K + 1).factorial < 2 ^ ((K + 1) * (K + 1)) := by
  have h1 : (K + 1).factorial ≤ (K + 1) ^ (K + 1) := Nat.factorial_le_pow (K + 1)
  have h2 : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
  calc (K + 1).factorial ≤ (K + 1) ^ (K + 1) := h1
    _ < (2 ^ (K + 1)) ^ (K + 1) := Nat.pow_lt_pow_left h2 (by omega)
    _ = 2 ^ ((K + 1) * (K + 1)) := by rw [← pow_mul]

end ECDLP.L113
