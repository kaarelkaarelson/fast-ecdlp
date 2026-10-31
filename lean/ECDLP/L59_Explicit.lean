import ECDLP.L59_Size
import ECDLP.L59_Final

/-!
# L59 / Explicit: size bounds for the edge network with the explicit parameters, in the input bit length `L`
-/
noncomputable section
namespace ECDLP.L59
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c))

/-- **Max setting length.**  With the explicit parameters every gate has setting length at most
`164 (nmax+1) · A · D` bits, where `(A·D)⁴ ≤ 4 L³` (so `A·D ≤ 4^{1/4} L^{3/4}`; `L ≥ 4`). -/
theorem settingBits_explicit (L nmax : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax)
    (ok : ι → Fin (NParE L).A → Dg (NParE L) → Prop) (g : CG ι ιc (NParE L).A) :
    settingBits (w := fun _ : Fin K => wP L) φ F ok g ≤ 164 * (nmax + 1) * (AP L * DP L) := by
  have h := settingBits_le (w := fun _ : Fin K => wP L) φ F ok nmax hn g
  have hS := eS_le_explicit L
  have hA : 1 ≤ AP L := Nat.one_le_two_pow
  have hD := DP_ge_two L
  have hAD : DP L ≤ AP L * DP L := Nat.le_mul_of_pos_left _ hA
  cases g with
  | src i s => simp only at h; nlinarith
  | gt c g =>
    have hM := eM_le_explicit L c
    cases g with
    | fa j s => simp only at h; nlinarith
    | mid k =>
      simp only at h
      have : nmax * (NParE L).A * eM (NParE L) (fun _ => wP L) c ≤ nmax * AP L * (82 * DP L) := Nat.mul_le_mul (le_refl _) hM
      nlinarith
    | ib j =>
      simp only at h
      have : (NParE L).A * eM (NParE L) (fun _ => wP L) c ≤ AP L * (82 * DP L) := Nat.mul_le_mul (le_refl _) hM
      nlinarith
    | car j => simp only at h; nlinarith

theorem settingBits_explicit_L (L nmax : ℕ) (hL : 4 ≤ L) :
    (164 * (nmax + 1) * (AP L * DP L)) ^ 4 ≤ (164 * (nmax + 1)) ^ 4 * 4 * L ^ 3 := by
  have := AD_four_le L hL
  calc _ = (164 * (nmax + 1)) ^ 4 * (AP L * DP L) ^ 4 := by ring
    _ ≤ (164 * (nmax + 1)) ^ 4 * (4 * L ^ 3) := by gcongr
    _ = _ := by ring

/-- **Number of gates** with explicit parameters: `≤ A (|ι| + K (nmax + 2 + A))`, `A⁴ ≤ 4 L`. -/
theorem gates_explicit (L nmax : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) :
    Fintype.card (CG ι ιc (NParE L).A) ≤ AP L * (Fintype.card ι + K * (nmax + 2 + AP L)) :=
  card_CG_le (AP L) nmax hn

end

/-- explicit parameter bounds: all in one place -/
theorem param_bounds (L : ℕ) (hL : 4 ≤ L) :
    DP L * DP L ≤ L ∧ L ≤ 16 * (DP L * DP L) ∧ AP L ^ 4 ≤ 4 * L ∧ (AP L * DP L) ^ 4 ≤ 4 * L ^ 3 ∧
      bP L ≤ 36 * DP L ∧ DP L * wP L ≤ 80 * DP L :=
  ⟨D_sq_le L hL, L_le_D_sq L, A_four_le L hL, AD_four_le L hL, bP_le L, M_le L⟩

end ECDLP.L59
end
