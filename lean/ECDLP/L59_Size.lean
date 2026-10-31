import ECDLP.L59_ParOK
import ECDLP.L57_Edge

/-!
# L59 / Size: simple size facts for the edge network with the explicit parameters
-/
noncomputable section
namespace ECDLP.L59
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57

/-! ### parameter inequalities in terms of the input bit length `L` -/

theorem DP_eq (L : ℕ) : DP L = 2 ^ (2 * jm1 L + 1) := rfl

/-- `D² ≤ L` once `L ≥ 4`. -/
theorem D_sq_le (L : ℕ) (hL : 4 ≤ L) : DP L * DP L ≤ L := by
  have hlog : 2 ≤ Nat.log 2 L := by
    have : 2 ^ 2 ≤ L := by omega
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 this
  have h1 : 4 * jm1 L + 2 ≤ Nat.log 2 L := by unfold jm1; omega
  calc DP L * DP L = 2 ^ (4 * jm1 L + 2) := by rw [DP_eq, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ Nat.log 2 L := Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ L := Nat.pow_log_le_self 2 (by omega)

/-- `L ≤ 16 D²` for all `L`. -/
theorem L_le_D_sq (L : ℕ) : L ≤ 16 * (DP L * DP L) := by
  have h1 : Nat.log 2 L + 1 ≤ 4 * jm1 L + 2 + 4 := by unfold jm1; omega
  have hL : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have : 16 * (DP L * DP L) = 2 ^ (4 * jm1 L + 2 + 4) := by
    rw [DP_eq, ← pow_add]; rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  rw [this]
  exact hL.le.trans (Nat.pow_le_pow_right (by norm_num) h1)

/-- `A⁴ = 4 D²` -/
theorem A_four (L : ℕ) : AP L ^ 4 = 4 * (DP L * DP L) := by
  have := AA_eq L
  calc AP L ^ 4 = (AP L * AP L) * (AP L * AP L) := by ring
    _ = _ := by rw [this]; ring

/-- `A⁴ ≤ 4 L`, i.e. `A ≤ (4L)^{1/4}` -/
theorem A_four_le (L : ℕ) (hL : 4 ≤ L) : AP L ^ 4 ≤ 4 * L := by
  rw [A_four]; have := D_sq_le L hL; omega

/-- `(A·D)⁴ ≤ 4 L³`, i.e. `A·D ≤ 4^{1/4} L^{3/4}` -/
theorem AD_four_le (L : ℕ) (hL : 4 ≤ L) : (AP L * DP L) ^ 4 ≤ 4 * L ^ 3 := by
  have h := D_sq_le L hL
  calc (AP L * DP L) ^ 4 = AP L ^ 4 * (DP L * DP L) * (DP L * DP L) := by ring
    _ = 4 * ((DP L * DP L) * (DP L * DP L) * (DP L * DP L)) := by rw [A_four]; ring
    _ ≤ 4 * (L * L * L) := by gcongr
    _ = 4 * L ^ 3 := by ring

theorem DP_ge_one (L : ℕ) : 1 ≤ DP L := DP_pos L
theorem DP_ge_two (L : ℕ) : 2 ≤ DP L := by
  rw [DP_eq]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kP_lt_DP (L : ℕ) : kP L < DP L := Nat.lt_two_pow_self

/-- digit-count multiplier: `b ≤ 36 D` -/
theorem bP_le (L : ℕ) : bP L ≤ 36 * DP L := by
  have h1 := Bits_lt L
  have h2 : bP L * DP L ≤ Bits L + DP L := by
    unfold bP
    have := Nat.div_mul_le_self (Bits L) (DP L)
    nlinarith
  have hL := L_le_D_sq L
  have hD := DP_ge_two L
  have h3 : bP L * DP L ≤ 36 * DP L * DP L := by unfold Bits at h2; nlinarith
  exact Nat.le_of_mul_le_mul_right (by nlinarith) (DP_pos L)

/-- ring exponent `M = D w ≤ 80 D` -/
theorem M_le (L : ℕ) : DP L * wP L ≤ 80 * DP L := by
  have h := bP_le L
  have hk := kP_lt_DP L
  have hD := DP_ge_two L
  unfold wP
  have := Nat.div_mul_le_self (2 * bP L + kP L + 4) (DP L)
  rw [Nat.mul_add, Nat.mul_comm (DP L) ((2 * bP L + kP L + 4) / DP L)]
  nlinarith

/-- `eM ≤ 82 D` for the explicit parameters -/
theorem eM_le_explicit (L : ℕ) {K : ℕ} (c : Fin K) :
    eM (NParE L) (fun _ => wP L) c ≤ 82 * DP L := by
  have := M_le L
  have hD := DP_ge_two L
  show 2 ^ kP L * wP L + 4 ≤ _
  have : 2 ^ kP L = DP L := rfl
  rw [this]; omega

theorem eS_le_explicit (L : ℕ) : eS (NParE L) ≤ 37 * (AP L * DP L) := by
  have hb := bP_le L
  have hh : hP L ≤ AP L := by unfold hP AP; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 1 ≤ AP L := Nat.one_le_two_pow
  have hD := DP_ge_two L
  show bP L * hP L + 1 ≤ _
  have : bP L * hP L ≤ 36 * DP L * AP L := Nat.mul_le_mul hb hh
  nlinarith

/-! ### number of gates -/

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} [Fintype ι] [∀ c, Fintype (ιc c)]
  [∀ c, DecidableEq (ιc c)] [DecidableEq ι]

theorem card_Gate (ι' : Type) [Fintype ι'] [DecidableEq ι'] (A : ℕ) :
    Fintype.card (Gate ι' A) = Fintype.card ι' * A + (A + (A + A * A)) := by
  rw [Fintype.card_congr (gateEquiv ι' A)]
  simp [Fintype.card_sum, Fintype.card_prod]

instance : ∀ A : ℕ, Fintype (CG ι ιc A) := fun A => Fintype.ofEquiv _ (cgEquiv ι ιc A).symm

/-- exact number of gates of the per-identity network -/
theorem card_CG (A : ℕ) :
    Fintype.card (CG ι ιc A) =
      Fintype.card ι * A + ∑ c : Fin K, (Fintype.card (ιc c) * A + (A + (A + A * A))) := by
  rw [Fintype.card_congr (cgEquiv ι ιc A)]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, card_Gate]

/-- gates `≤ A · (|ι| + K (nmax + 2 + A))` -/
theorem card_CG_le (A nmax : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) :
    Fintype.card (CG ι ιc A) ≤ A * (Fintype.card ι + K * (nmax + 2 + A)) := by
  rw [card_CG]
  have : ∑ c : Fin K, (Fintype.card (ιc c) * A + (A + (A + A * A))) ≤ ∑ _c : Fin K, A * (nmax + 2 + A) :=
    sum_le_sum fun c _ => by nlinarith [hn c]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
  nlinarith

end

/-! ### maximum setting length -/

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- free-variable bits of a gate -/
def freeBits (N0 : NPar) : CG ι ιc N0.A → ℕ
  | .src _ _ => N0.b * N0.h
  | .gt _ _ => 0

theorem card_free_le (g : CG ι ιc N0.A) : Fintype.card (CF ι ιc N0 g) ≤ 2 ^ freeBits N0 g := by
  cases g with
  | src i s =>
    show Fintype.card (Dg N0) ≤ 2 ^ (N0.b * N0.h)
    simp [Dg, ← pow_mul]
  | gt c g =>
    show Fintype.card Unit ≤ 2 ^ 0
    simp

/-- setting length (in bits) of a gate: `⌈log₂ |setting|⌉` -/
def settingBits (g : CG ι ιc N0.A) : ℕ :=
  Nat.clog 2 (Fintype.card ((edgeNet (w := w) φ F ok).S g))

theorem settingBits_le_inW (g : CG ι ιc N0.A) :
    settingBits (w := w) φ F ok g ≤ freeBits N0 g + PForcedW.inW (edgeNet (w := w) φ F ok) g := by
  classical
  unfold settingBits
  apply Nat.clog_le_of_le_pow
  have hS : Fintype.card ((edgeNet (w := w) φ F ok).S g) =
      Fintype.card (CF ι ιc N0 g) *
        ∏ j : {j // j ∈ paC (w := w) φ g}, Fintype.card (CM2 ι ιc N0 w j.1) := by
    show Fintype.card (CF ι ιc N0 g × (∀ j : {j // j ∈ paC (w := w) φ g}, CM2 ι ιc N0 w j.1)) = _
    rw [Fintype.card_prod, Fintype.card_pi]
  rw [hS]
  have hp : ∏ j : {j // j ∈ paC (w := w) φ g}, Fintype.card (CM2 ι ιc N0 w j.1) ≤
      2 ^ PForcedW.inW (edgeNet (w := w) φ F ok) g := by
    calc ∏ j : {j // j ∈ paC (w := w) φ g}, Fintype.card (CM2 ι ιc N0 w j.1)
        ≤ ∏ j : {j // j ∈ paC (w := w) φ g}, 2 ^ ((edgeNet (w := w) φ F ok).w j.1) :=
          Finset.prod_le_prod' (fun j _ => Nat.le_pow_clog one_lt_two _)
      _ = 2 ^ ∑ j : {j // j ∈ paC (w := w) φ g}, (edgeNet (w := w) φ F ok).w j.1 := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ 2 ^ PForcedW.inW (edgeNet (w := w) φ F ok) g := by
          apply Nat.pow_le_pow_right (by norm_num)
          unfold PForcedW.inW
          rw [Finset.sum_coe_sort (paC (w := w) φ g) (fun j => (edgeNet (w := w) φ F ok).w j)]
          exact sum_le_sum fun j _ => Nat.le_succ _
  calc _ ≤ 2 ^ freeBits N0 g * 2 ^ PForcedW.inW (edgeNet (w := w) φ F ok) g :=
        Nat.mul_le_mul (card_free_le g) hp
    _ = _ := (pow_add _ _ _).symm

/-- setting length of each gate in terms of the parameters -/
theorem settingBits_le (nmax : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (g : CG ι ιc N0.A) :
    settingBits (w := w) φ F ok g ≤
      match g with
      | .src _ _ => eS N0
      | .gt _ (Gate.fa _ _) => eS N0
      | .gt c (Gate.mid _) => nmax * N0.A * eM N0 w c
      | .gt c (Gate.ib _) => N0.A * eM N0 w c
      | .gt c (Gate.car _) => 2 * eM N0 w c := by
  have h1 := settingBits_le_inW (w := w) φ F ok g
  have h2 := inW_le (w := w) φ F ok g
  cases g with
  | src i s => simp only [freeBits, eS] at *; omega
  | gt c g =>
    cases g with
    | fa j s => simp only [freeBits] at *; omega
    | mid k =>
      simp only [freeBits] at *
      have : Fintype.card (ιc c) * N0.A * eM N0 w c ≤ nmax * N0.A * eM N0 w c := by gcongr; exact hn c
      omega
    | ib j => simp only [freeBits] at *; omega
    | car j => simp only [freeBits] at *; omega

end

end ECDLP.L59
end
