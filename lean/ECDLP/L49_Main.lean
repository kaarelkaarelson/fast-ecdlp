import Mathlib
import ECDLP.L49_Dil
import ECDLP.L46_Cover

/-!
# L49 (3): the coverage chain for a fixed curve, averaging over dilations `u ∈ Kˣ`

Two named hypotheses only:
* `DilationNondeg A B (n+1) T D'` (L49_Dil): Lemma N′ + degree bound for dilations;
* `FactorBaseVar A B T c` : Lemma F, `∑_u (f^(u) − X)² ≤ c X |Kˣ|` (needs Weil; not in Mathlib).
-/
namespace ECDLP.L49

open Finset ECDLP.L40 ECDLP.L43 ECDLP.L46

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Hypothesis (Lemma F)**: variance of the factor-base size over dilations of the fixed curve. -/
def FactorBaseVar (A B : K) (T : Finset K) (c : ℝ) : Prop :=
  ∑ u : Kˣ, (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - T.card) ^ 2
    ≤ c * T.card * Fintype.card Kˣ

/-- the average-energy constant over dilations -/
noncomputable def Mdil (K : Type*) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) (T : Finset K) (D' : ℕ) : ℝ :=
  (dfac (n + 1) : ℝ) * 4 ^ (n + 1) * (T.card : ℝ) ^ (n + 1)
    + 4 ^ (n + 1) * (2 * D') * (T.card : ℝ) ^ (2 * (n + 1)) / (Fintype.card Kˣ : ℝ)

theorem Mdil_pos (n : ℕ) (T : Finset K) (D' : ℕ) (hX : 0 < T.card) : 0 < Mdil K n T D' := by
  unfold Mdil
  have : (0 : ℝ) < dfac (n + 1) := by
    exact_mod_cast Finset.prod_pos (fun i _ => by omega)
  positivity

theorem disc_dil (A B : K) (u : Kˣ) :
    disc ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) = (u : K) ^ 12 * disc A B := by
  unfold disc; ring

theorem disc_dil_ne (A B : K) (u : Kˣ) (hd : disc A B ≠ 0) :
    disc ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ≠ 0 := by
  rw [disc_dil]; exact mul_ne_zero (pow_ne_zero _ u.ne_zero) hd

/-- **Average energy over dilations**: `∑_u Eng(E_u) ≤ Mdil · |Kˣ|`. -/
theorem avg_energy_dil (hK : ringChar K ≠ 2) (A B : K) (hd : disc A B ≠ 0) (T : Finset K)
    (n D' : ℕ) (hN : DilationNondeg A B (n + 1) T D') :
    ∑ u : Kˣ, (Eng T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) : ℝ)
      ≤ Mdil K n T D' * (Fintype.card Kˣ : ℝ) := by
  classical
  have hq : (0 : ℝ) < Fintype.card Kˣ := by exact_mod_cast Fintype.card_pos
  have h1 : ∀ u : Kˣ, (Eng T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) : ℝ)
      ≤ (((badU A B (n + 1) T).filter (fun x => x.1 = u)).card : ℝ) := fun u =>
    by exact_mod_cast eng_le_badU hK T n A B u (disc_dil_ne A B u hd)
  have h2 := fiber_univ' (badU A B (n + 1) T)
  have hsk := badU_card A B (n + 1) D' T hN
  calc _ ≤ ∑ u : Kˣ, (((badU A B (n + 1) T).filter (fun x => x.1 = u)).card : ℝ) :=
        sum_le_sum (fun u _ => h1 u)
    _ = ((badU A B (n + 1) T).card : ℝ) := by exact_mod_cast h2.symm
    _ ≤ (dfac (n + 1) : ℝ) * 4 ^ (n + 1) * (T.card : ℝ) ^ (n + 1) * (Fintype.card Kˣ : ℝ)
        + 4 ^ (n + 1) * (2 * D') * (T.card : ℝ) ^ (2 * (n + 1)) := by exact_mod_cast hsk
    _ = _ := by unfold Mdil; field_simp

end ECDLP.L49
