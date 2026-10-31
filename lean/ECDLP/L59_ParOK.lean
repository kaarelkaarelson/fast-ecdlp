import ECDLP.L59_Param

/-!
# L59 / ParOK: `ParOK'` for the explicit parameters, for every prime-size input (no lower bound on `L`)
-/
noncomputable section
namespace ECDLP.L59
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38 ECDLP.L51 ECDLP.L35 ECDLP.L54 ECDLP.L56

variable {n K : ℕ}

theorem sizeArith (L : ℕ) :
    12 * (2 ^ kP L * (2 ^ bP L * 2 ^ bP L)) ≤ 2 ^ (2 ^ kP L * wP L) := by
  have h := wP_mul L
  have hD : DP L = 2 ^ kP L := rfl
  rw [hD] at h
  calc 12 * (2 ^ kP L * (2 ^ bP L * 2 ^ bP L)) ≤ 16 * (2 ^ kP L * (2 ^ bP L * 2 ^ bP L)) := by
        have : 0 ≤ 2 ^ kP L * (2 ^ bP L * 2 ^ bP L) := Nat.zero_le _
        omega
    _ = 2 ^ (4 + kP L + (bP L + bP L)) := by
        rw [pow_add, pow_add, pow_add]; ring
    _ ≤ 2 ^ (2 ^ kP L * wP L) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Explicit `ParOK'`.** For every `p > 0` and every instance data below `p`, every prefix and every
numbering `e` of the identities, the explicit parameters satisfy `ParOK'`. -/
theorem parOK_explicit (p a b xR yR n : ℕ) (hp : 0 < p) (ha : a < p) (hb : b < p) (hx : xR < p)
    (hy : yR < p) (π : List Bool) (e : Cn n ≃ Fin K) :
    ParOK' (instOf p a b xR yR n) (ell p n) π e (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) := by
  have hbD : Bits (Nat.size p) < bP (Nat.size p) * DP (Nat.size p) := Bits_lt _
  have hDk : (NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k = bP (Nat.size p) * DP (Nat.size p) := rfl
  refine ⟨bP_pos _, ?_, fun c => ?_, fun c => ?_⟩
  · rw [hDk]
    have : ell p n ≤ Nat.size p := Nat.size_le_size (Bd_le hp n)
    unfold Bits at hbD; omega
  · rw [hDk]
    refine lt_of_lt_of_le (cv_lt p a b xR yR n hp ha hb hx hy c) ?_
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hbD.le
  · refine sizeOK_fr _ e (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c ?_ ?_ ?_
    · show 1 ≤ 2 ^ kP (Nat.size p) * wP (Nat.size p)
      exact Nat.one_le_iff_ne_zero.2 (by have := wP_pos (Nat.size p); have := DP_pos (Nat.size p); unfold DP at this; positivity)
    · show 2 * 2 ^ kP (Nat.size p) ≤ AP (Nat.size p) * AP (Nat.size p)
      exact (AA_eq _).ge
    · exact sizeArith _

end ECDLP.L59
end
