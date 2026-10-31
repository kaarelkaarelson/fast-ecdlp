import ECDLP.L90_BddA

/-!
# L90 / BddB: value bounds of `jm1E`, `prel`, and of `AEx, hEx, pbEx, bEx, MEx`

Numeric facts about `L = Nat.size p` only: `2 L + 4 <= V`, `2^L <= V`, `40 <= V`, `2^(bP L) <= V`, `2^(2^(kP L) * wP L) <= V`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83

/-- numeric side conditions on `V` (about `L = Nat.size p` and the shape parameters) -/
structure LNum (V L : ℕ) : Prop where
  h40 : 40 ≤ V
  hL4 : 2 * L + 4 ≤ V
  hL2 : 2 ^ L ≤ V
  hpb : 2 ^ bP L ≤ V
  hM2 : 2 ^ (2 ^ kP L * wP L) ≤ V

theorem D_le (L : ℕ) : 2 ^ kP L ≤ 2 * L + 2 := by
  have h1 : 2 * jm1 L ≤ Nat.log 2 L := by unfold jm1; omega
  have h2 : 2 ^ kP L = 2 ^ (2 * jm1 L) * 2 := by unfold kP; rw [pow_succ]
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have : 2 * jm1 0 ≤ 0 := by simpa using h1
    have : 2 * jm1 0 = 0 := by omega
    rw [h2, this]; simp
  · have h3 : 2 ^ (2 * jm1 L) ≤ 2 ^ Nat.log 2 L := Nat.pow_le_pow_right (by norm_num) h1
    have h4 : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 (by omega)
    omega

theorem bP_lt (L : ℕ) : bP L < 2 ^ bP L := Nat.lt_two_pow_self

theorem M_ge (L : ℕ) : 2 * bP L + kP L + 4 < 2 ^ kP L * wP L := by
  have hD := DP_pos L
  unfold DP at hD
  unfold wP DP
  generalize 2 ^ kP L = D at hD ⊢
  generalize 2 * bP L + kP L + 4 = x
  have h1 := Nat.lt_div_mul_add (a := x) hD
  have h2 : D * (x / D + 1) = x / D * D + D := by ring
  omega

section
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (u : ℕ) {L : ℕ}

theorem bdd_log2E (N : LNum V L) (h63 : σ (u + 63) = L) : Bdd V σ A (log2E u (.var (u + 63))) := by
  have h2 : 2 ≤ V := by have := N.h40; omega
  refine bdd_nsum_le1 (by show σ (u + 63) ≤ V; rw [h63]; have := N.hL4; omega) (by simp [Ex.eval, h63]; have := N.hL4; omega) ?_ ?_
  · intro j hj
    simp only [Ex.eval, h63] at hj
    have e1 : Function.update σ (u + 60) j (u + 63) = L := by rw [Function.update_of_ne (by omega)]; exact h63
    have e2 : Function.update σ (u + 60) j (u + 60) = j := Function.update_self ..
    have := N.hL4
    refine bdd_ifLt (by show Function.update σ (u + 60) j (u + 63) ≤ V; omega) ?_ (fun _ => bdd_lit (Nat.zero_le V)) (fun _ => bdd_lit (by omega))
    have hjL : j + 1 ≤ L := by omega
    refine bdd_pow2 (x := u + 61) ⟨?_, ?_, ?_⟩ h2 ?_
    · show Function.update σ (u + 60) j (u + 60) ≤ V; omega
    · show 1 ≤ V; omega
    · simp only [Ex.eval]; rw [e2]; omega
    · simp only [Ex.eval]; rw [e2]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hjL) N.hL2
  · intro j; exact eval_ifLt01 _ _

theorem eval_log2E' (h63 : σ (u + 63) = L) : Ex.eval σ A (log2E u (.var (u + 63))) = Nat.log 2 L := by
  have := eval_log2E (u := u) (σ := σ) (A := A) (.var (u + 63))
    (fun j => by show Function.update σ (u + 60) j (u + 63) = σ (u + 63); simp [Function.update_apply])
  simpa [Ex.eval, h63] using this

theorem bdd_jm1E (N : LNum V L) (h63 : σ (u + 63) = L) : Bdd V σ A (jm1E u) := by
  have h4 := N.hL4
  have h40 := N.h40
  have hlog := eval_log2E' u (σ := σ) (A := A) h63
  have hle : Nat.log 2 L ≤ L := Nat.log_le_self 2 L
  refine ⟨⟨⟨bdd_log2E u N h63, (show 2 ≤ V by omega), ?_⟩, (show 4 ≤ V by omega)⟩, (show 1 ≤ V by omega)⟩
  simp only [Ex.eval]; rw [hlog]; omega

end

section prel
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (u : ℕ) {n : ℕ}
  {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem st_63 (σ : ℕ → ℕ) (L : ℕ) : st u σ L (u + 63) = L := by simp [st, Function.update_apply]
theorem st_64 (σ : ℕ → ℕ) (L : ℕ) : st u σ L (u + 64) = jm1 L := by simp [st, Function.update_apply]
theorem st_65 (σ : ℕ → ℕ) (L : ℕ) : st u σ L (u + 65) = kP L := by simp [st, Function.update_apply]
theorem st_66 (σ : ℕ → ℕ) (L : ℕ) : st u σ L (u + 66) = DP L := by simp [st, Function.update_apply]
theorem st_67 (σ : ℕ → ℕ) (L : ℕ) : st u σ L (u + 67) = bP L := by simp [st, Function.update_apply]

theorem jm1_le (L : ℕ) : jm1 L ≤ L := by
  have := Nat.log_le_self 2 L; unfold jm1; omega

theorem bdd_prel (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hs : 2 ^ σ 0 ≤ V)
    (N : LNum V (Nat.size p)) (body : Ex) (hb : Bdd V (st u σ (Nat.size p)) A body) : Bdd V σ A (prel u body) := by
  have h4 := N.hL4
  have h40 := N.h40
  have hjm := jm1_le (Nat.size p)
  have hD := D_le (Nat.size p)
  have hM := M_ge (Nat.size p)
  have hMV : 2 ^ kP (Nat.size p) * wP (Nat.size p) ≤ V :=
    le_trans (Nat.lt_two_pow_self).le N.hM2
  have hbP := bP_lt (Nat.size p)
  have hbV : bP (Nat.size p) ≤ V := by have := N.hpb; omega
  have hkP : kP (Nat.size p) = 2 * jm1 (Nat.size p) + 1 := rfl
  have hDe : DP (Nat.size p) = 2 ^ kP (Nat.size p) := rfl
  refine ⟨bdd_szE u H hR hs, ?_⟩
  rw [eval_szE u hR]
  refine ⟨bdd_jm1E u N (by simp), ?_⟩
  rw [eval_jm1E u (Nat.size p) (by simp)]
  set L := Nat.size p with hLdef
  have g63 : ∀ τ : ℕ → ℕ, τ (u + 63) = L → Ex.eval τ A (.var (u + 63)) = L := fun τ h => h
  have hdiv : (2 * L + 3) / DP L ≤ 2 * L + 3 := Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · -- kP
    have e64 : Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L) (u + 64) = jm1 L := by simp
    simp only [Bdd, Ex.eval, e64]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> omega
  have e64 : Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L) (u + 64) = jm1 L := by simp
  have e65 : Ex.eval (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) A
      (((lit 2).mul (var (u + 64))).add (lit 1)) = kP L := by simp [Ex.eval, e64, hkP]
  rw [e65]
  have e65' : Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L) (u + 65) = kP L := by simp
  refine ⟨?_, ?_⟩
  · refine bdd_pow2 (x := u + 60) ?_ (by omega) ?_
    · show Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L) (u + 65) ≤ V
      rw [e65']; omega
    · simp only [Ex.eval, e65']; omega
  have e66 : Ex.eval (Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L)) A
      (pow2 (u + 60) (var (u + 65))) = DP L := by
    rw [eval_pow2]; simp [Ex.eval, DP]
  rw [e66]
  have e63 : Function.update (Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L)) (u + 66) (DP L) (u + 63) = L := by simp
  have e66' : Function.update (Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L)) (u + 66) (DP L) (u + 66) = DP L := by simp
  refine ⟨?_, ?_⟩
  · simp only [Bdd, Ex.eval, e63, e66']
    refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_⟩ <;> omega
  have e67 : Ex.eval (Function.update (Function.update (Function.update (Function.update σ (u + 63) L) (u + 64) (jm1 L)) (u + 65) (kP L)) (u + 66) (DP L)) A
      (((((lit 2).mul (var (u + 63))).add (lit 3)).div (var (u + 66))).add (lit 1)) = bP L := by
    simp [Ex.eval, e63, e66', bP, ECDLP.L59.Bits]
  rw [e67]
  exact hb


section params
variable (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hs : 2 ^ σ 0 ≤ V)
  (N : LNum V (Nat.size p))
include H hR hs N

theorem bdd_AEx : Bdd V σ A (AEx u) := by
  refine bdd_prel u H hR hs N _ ?_
  have hD := D_le (Nat.size p)
  have h4 := N.hL4
  have hjm := jm1_le (Nat.size p)
  have h2 : 2 ≤ V := by have := N.h40; omega
  refine bdd_pow2 (x := u + 60) ⟨?_, ?_, ?_⟩ h2 ?_
  · show st u σ (Nat.size p) (u + 64) ≤ V; rw [st_64]; omega
  · show 1 ≤ V; omega
  · simp only [Ex.eval, st_64]; omega
  · simp only [Ex.eval, st_64]
    refine le_trans (Nat.pow_le_pow_right (by norm_num) (show jm1 (Nat.size p) + 1 ≤ kP (Nat.size p) by unfold kP; omega)) ?_
    omega

theorem bdd_hEx : Bdd V σ A (hEx u) := by
  refine bdd_prel u H hR hs N _ ?_
  have hD := D_le (Nat.size p)
  have h4 := N.hL4
  have hjm := jm1_le (Nat.size p)
  have h2 : 2 ≤ V := by have := N.h40; omega
  refine bdd_pow2 (x := u + 60) ?_ h2 ?_
  · show st u σ (Nat.size p) (u + 64) ≤ V; rw [st_64]; omega
  · simp only [Ex.eval, st_64]
    refine le_trans (Nat.pow_le_pow_right (by norm_num) (show jm1 (Nat.size p) ≤ kP (Nat.size p) by unfold kP; omega)) ?_
    omega

theorem bdd_pbEx : Bdd V σ A (pbEx u) := by
  refine bdd_prel u H hR hs N _ ?_
  have hbP := bP_lt (Nat.size p)
  have h2 : 2 ≤ V := by have := N.h40; omega
  have hpb := N.hpb
  refine bdd_pow2 (x := u + 60) ?_ h2 ?_
  · show st u σ (Nat.size p) (u + 67) ≤ V; rw [st_67]; omega
  · simp only [Ex.eval, st_67]; exact hpb

theorem bdd_bEx : Bdd V σ A (bEx u) := by
  refine bdd_prel u H hR hs N _ ?_
  have hbP := bP_lt (Nat.size p)
  have hpb := N.hpb
  show st u σ (Nat.size p) (u + 67) ≤ V; rw [st_67]; omega

theorem bdd_MEx : Bdd V σ A (MEx u) := by
  refine bdd_prel u H hR hs N _ ?_
  have hD := D_le (Nat.size p)
  have h4 := N.hL4
  have hM := M_ge (Nat.size p)
  have hbP := bP_lt (Nat.size p)
  have hpb := N.hpb
  have hMV : 2 ^ kP (Nat.size p) * wP (Nat.size p) ≤ V := le_trans (Nat.lt_two_pow_self).le N.hM2
  have h40 := N.h40
  have hDp := DP_pos (Nat.size p)
  have hDe : DP (Nat.size p) = 2 ^ kP (Nat.size p) := rfl
  have hMV' : DP (Nat.size p) * ((2 * bP (Nat.size p) + kP (Nat.size p) + 4) / DP (Nat.size p) + 1) ≤ V := by
    rw [hDe]; exact hMV
  have hq1 : (2 * bP (Nat.size p) + kP (Nat.size p) + 4) / DP (Nat.size p) + 1 ≤
      DP (Nat.size p) * ((2 * bP (Nat.size p) + kP (Nat.size p) + 4) / DP (Nat.size p) + 1) :=
    Nat.le_mul_of_pos_left _ hDp
  have hM' : 2 * bP (Nat.size p) + kP (Nat.size p) + 4 < DP (Nat.size p) * ((2 * bP (Nat.size p) + kP (Nat.size p) + 4) / DP (Nat.size p) + 1) := by
    rw [hDe]; exact hM
  have hq2 : (2 * bP (Nat.size p) + kP (Nat.size p) + 4) / DP (Nat.size p) ≤ 2 * bP (Nat.size p) + kP (Nat.size p) + 4 :=
    Nat.div_le_self _ _
  simp only [Bdd, Ex.eval, st_65, st_66, st_67]
  refine ⟨?_, ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩ <;> omega

end params

end prel

end ECDLP.L90
end
