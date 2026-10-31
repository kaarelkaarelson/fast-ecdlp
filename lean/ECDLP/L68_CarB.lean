import ECDLP.L68_Car
import ECDLP.L69_Bdd

/-!
# L68 / CarB: value bounds (`Bdd V`) of the car-gate expressions (down payment on L69's `PExB.bout` / `bwt`)

For the car expressions `carOutE`, `carWE` every intermediate value is `<= V` as soon as
`4 * (2^b * 8 * 2^M) <= V` and the two inputs are in range (`vc < 2^(M+3)`, `vr < 2^M + 1`, as a digit of a setting
code read with `digE` always is: `digE` ends with `% nm`).  The expressions read no array (`rd`), so the layout
clash of array 3 does not touch them.
-/
noncomputable section
namespace ECDLP.L68
open Factoring.Aux Ex

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem bdd_tE {V vb vM vj vc vr : ℕ} {pb pM : ℕ} (hb : σ vb = pb) (hM : σ vM = pM) (hpb : 1 ≤ pb) (hpM : 1 ≤ pM)
    (hc : σ vc ≤ 8 * pM) (hr : σ vr ≤ pM + 1) (hZ : 4 * (pb * (8 * pM)) ≤ V) (hj : σ vj ≤ V) :
    Bdd V σ A (tE vb vM vj vc vr) := by
  have hZ1 : 8 * pM ≤ pb * (8 * pM) := Nat.le_mul_of_pos_left _ hpb
  have hZ2 : pb ≤ pb * (8 * pM) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [tE, Bdd, Ex.eval, hb, hM]
  generalize pb * (8 * pM) = Z at *
  have hcv : σ vc ≤ V := by omega
  split_ifs <;> omega


theorem tN_le (pb pM j ci r : ℕ) (hc : ci ≤ 8 * pM) (hr : r ≤ pM + 1) (hpb : 1 ≤ pb) (hpM : 1 ≤ pM) :
    tN pb pM j ci r ≤ pb * (8 * pM) + 8 * pM + pM + 1 := by
  have hZ1 : 8 * pM ≤ pb * (8 * pM) := Nat.le_mul_of_pos_left _ hpb
  unfold tN
  generalize pb * (8 * pM) = Z at *
  split_ifs <;> omega

theorem bdd_carOutE {V vb vM vj vc vr : ℕ} {pb pM : ℕ} (hb : σ vb = pb) (hM : σ vM = pM) (hpb : 1 ≤ pb) (hpM : 1 ≤ pM)
    (hc : σ vc ≤ 8 * pM) (hr : σ vr ≤ pM + 1) (hZ : 4 * (pb * (8 * pM)) ≤ V) (hj : σ vj ≤ V) :
    Bdd V σ A (carOutE vb vM vj vc vr) := by
  have hT := bdd_tE (A := A) (vb := vb) (vM := vM) (vj := vj) (vc := vc) (vr := vr) hb hM hpb hpM hc hr hZ hj
  have hL := tN_le pb pM (σ vj) (σ vc) (σ vr) hc hr hpb hpM
  have hZ1 : 8 * pM ≤ pb * (8 * pM) := Nat.le_mul_of_pos_left _ hpb
  have hZ2 : pb ≤ pb * (8 * pM) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [carOutE, Bdd, Ex.eval, eval_tE, hb, hM] at hT ⊢
  generalize pb * (8 * pM) = Z at *
  refine ⟨⟨⟨⟨hT, by omega⟩, ⟨by omega, by omega, by omega⟩, ?_⟩, ⟨by omega, by omega, by omega⟩⟩, by omega, by omega, by omega⟩
  have := Nat.div_le_self (tN pb pM (σ vj) (σ vc) (σ vr)) pb
  omega


theorem bdd_carWE {V vb vM vj vA2 vc vr : ℕ} {pb pM : ℕ} (hb : σ vb = pb) (hM : σ vM = pM) (hpb : 1 ≤ pb) (hpM : 1 ≤ pM)
    (hc : σ vc ≤ 8 * pM) (hr : σ vr ≤ pM + 1) (hZ : 4 * (pb * (8 * pM)) ≤ V) (hj : σ vj + 1 ≤ V) (hA : σ vA2 ≤ V) :
    Bdd V σ A (carWE vb vM vj vA2 vc vr) := by
  have hT := bdd_tE (A := A) (vb := vb) (vM := vM) (vj := vj) (vc := vc) (vr := vr) hb hM hpb hpM hc hr hZ (by omega)
  have hL := tN_le pb pM (σ vj) (σ vc) (σ vr) hc hr hpb hpM
  have hZ1 : 8 * pM ≤ pb * (8 * pM) := Nat.le_mul_of_pos_left _ hpb
  have hZ2 : pb ≤ pb * (8 * pM) := Nat.le_mul_of_pos_right _ (by omega)
  have hd := Nat.div_le_self (tN pb pM (σ vj) (σ vc) (σ vr)) pb
  have hm := Nat.mod_le (tN pb pM (σ vj) (σ vc) (σ vr)) pb
  simp only [carWE, Bdd, Ex.eval, eval_tE, hb, hM] at hT ⊢
  generalize pb * (8 * pM) = Z at *
  generalize tN pb pM (σ vj) (σ vc) (σ vr) = t at *
  simp only [hT, true_and]
  split_ifs <;> omega

end ECDLP.L68
end
