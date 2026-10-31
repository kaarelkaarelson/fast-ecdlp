import ECDLP.L34_Accept

/-!
# L34 / Main: **gadget accepts iff the integer identity holds**
-/
namespace ECDLP.L34

open Finset Factoring.Aux

variable {ι : Type}

namespace Par
variable (P : Par) (F : Form ι)

theorem A_pos : 0 < P.A := by
  rcases Nat.eq_zero_or_pos P.A with h | h
  · have := P.hA; rw [h] at this; exact absurd this.symm (by positivity)
  · exact h

/-- The integer coefficient of the combined convolution. -/
def e (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (j : ℕ) : ℤ :=
  ∑ t : Fin F.n, F.ε t * (cv (P.A * P.A) (P.sq (dg (F.l t))) (P.sq (dg (F.r t))) j : ℕ)

theorem sq_lt (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) (i : ℕ) : P.sq x i < 2 ^ P.b := by
  unfold sq; split_ifs with h
  · exact (x ⟨i, h⟩).2
  · exact Nat.pow_pos (by norm_num)

theorem sq_zero (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) (i : ℕ) (hi : 2 ^ P.k ≤ i) : P.sq x i = 0 := by
  unfold sq; rw [dif_neg (by omega)]

/-- The gate-level coefficient is the integer coefficient (as a residue). -/
theorem coef_eq (hM : 1 ≤ P.M) (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (j : ℕ) (hj : j < P.A * P.A) :
    P.coef F dg j = ((P.e F dg j : ℤ) : P.Rg) := by
  have hA0 := P.A_pos
  have h1 : j % P.A < P.A := Nat.mod_lt _ hA0
  have h2 : j / P.A < P.A := Nat.div_lt_of_lt_mul hj
  have gen := ib_mid_fa_gen P.A P.ω P.tInv P.k P.ω_pow P.hA (P.tInv_mul hM)
    (fun t => (F.ε t : P.Rg)) F.l F.r (fun i m => (P.sq (dg i) m : P.Rg))
    (fun i m hm => by simp [P.sq_zero _ _ hm]) (j % P.A) (j / P.A) h1 h2
  have key : P.coef F dg j = _ := gen
  rw [key, Nat.mod_add_div]
  unfold e
  rw [P.hA]
  push_cast
  refine sum_congr rfl fun t _ => ?_
  rw [cast_cv]

theorem e_abs_le (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (j : ℕ) :
    |P.e F dg j| ≤ (Form.mass F : ℤ) * ((2 ^ P.k * (2 ^ P.b * 2 ^ P.b) : ℕ) : ℤ) := by
  unfold e Form.mass
  refine (abs_sum_le_sum_abs _ _).trans ?_
  push_cast
  rw [sum_mul]
  refine sum_le_sum fun t _ => ?_
  rw [abs_mul, Int.abs_natCast, Int.abs_eq_natAbs]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast cv_le P.b (2 ^ P.k) _ _ _ (P.sq_lt _) (P.sq_lt _) (P.sq_zero _) j

/-- Exactness: under the size condition the signed representative is the integer coefficient. -/
theorem valMinAbs_coef (hM : 1 ≤ P.M) (hb : 2 * (Form.mass F * (2 ^ P.k * (2 ^ P.b * 2 ^ P.b))) ≤ 2 ^ P.M)
    (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (j : ℕ) (hj : j < P.A * P.A) :
    (P.coef F dg j).valMinAbs = P.e F dg j := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨P.coef_eq F hM dg j hj, ?_⟩
  have h := abs_le.1 (P.e_abs_le F dg j)
  have hb' : (2 : ℤ) * ((Form.mass F : ℤ) * ((2 ^ P.k * (2 ^ P.b * 2 ^ P.b) : ℕ) : ℤ)) ≤ 2 ^ P.M := by
    exact_mod_cast hb
  simp only [Set.mem_Ioc]
  push_cast
  constructor <;> nlinarith [h.1, h.2]

/-- The combined coefficients sum to the form. -/
theorem sum_e (hD : 2 * 2 ^ P.k ≤ P.A * P.A) (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) :
    ∑ j ∈ range (P.A * P.A), P.e F dg j * 2 ^ (P.b * j) =
      ∑ t : Fin F.n, F.ε t * ((P.val (dg (F.l t)) : ℤ) * (P.val (dg (F.r t)) : ℤ)) := by
  unfold e
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have := numOf_mul_numOf P.b (2 ^ P.k) (P.A * P.A) hD (P.sq (dg (F.l t))) (P.sq (dg (F.r t)))
    (P.sq_zero _) (P.sq_zero _)
  have hT : ∑ j ∈ range (P.A * P.A), ((cv (P.A * P.A) (P.sq (dg (F.l t))) (P.sq (dg (F.r t))) j : ℕ) : ℤ) * 2 ^ (P.b * j)
      = ((P.val (dg (F.l t)) : ℤ) * (P.val (dg (F.r t)) : ℤ)) := by
    unfold val
    have h2 := congrArg (fun n : ℕ => (n : ℤ)) this
    simp only [Nat.cast_mul, Nat.cast_sum] at h2
    rw [h2]
    refine sum_congr rfl fun j _ => ?_
    push_cast; rfl
  simp_rw [← hT, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **The gadget accepts a digit assignment iff the integer identity holds.** -/
theorem accept_iff (hM : 1 ≤ P.M) (hD : 2 * 2 ^ P.k ≤ P.A * P.A)
    (hb : 2 * (Form.mass F * (2 ^ P.k * (2 ^ P.b * 2 ^ P.b))) ≤ 2 ^ P.M)
    (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) :
    P.accept F dg ↔ P.Holds F dg := by
  unfold accept Holds
  rw [chainZ_iff, zero_add, ← P.sum_e F hD dg]
  have : ∑ j ∈ range (P.A * P.A), (P.coef F dg (0 + j)).valMinAbs * 2 ^ (P.b * j) =
      ∑ j ∈ range (P.A * P.A), P.e F dg j * 2 ^ (P.b * j) := by
    refine sum_congr rfl fun j hj => ?_
    rw [zero_add, P.valMinAbs_coef F hM hb dg j (mem_range.1 hj)]
  rw [this]

end Par
end ECDLP.L34
