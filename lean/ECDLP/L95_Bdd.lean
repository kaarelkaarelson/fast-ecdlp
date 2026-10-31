import ECDLP.L95_Par

/-!
# L95 / Bdd: value bounds of the rewritten prelude (`szE2, log2E2, jm1E2, prel2, AEx2 .. MEx2, epsEx2`)

Numeric hypotheses: `H : BN V sigma A n` (contains `2 sigma0 + 2 <= V`) and `LNum2 V L` = L90's `LNum` WITHOUT `2^L <= V`.
NO hypothesis `2^(sigma 0) <= V` and no `2^(size p) <= V` is used anywhere.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83 ECDLP.L90

/-- numeric side conditions on `V`, about `L = Nat.size p`: L90's `LNum` without `2^L <= V` -/
structure LNum2 (V L : ℕ) : Prop where
  h40 : 40 ≤ V
  hL4 : 2 * L + 4 ≤ V
  hpb : 2 ^ bP L ≤ V
  hM2 : 2 ^ (2 ^ kP L * wP L) ≤ V

theorem LNum2_of (V L : ℕ) (N : LNum V L) : LNum2 V L := ⟨N.h40, N.hL4, N.hpb, N.hM2⟩

theorem ite01_le (c : Prop) [Decidable c] : (if c then 1 else 0) ≤ 1 := by split <;> simp

section
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (u : ℕ) {n : ℕ}

theorem bdd_szE2 (H : BN V σ A n) : Bdd V σ A (szE2 u) := by
  have h0 := H.h0
  have h2 := H.h2
  have h0' : ∀ j, Function.update σ (u + 60) j 0 = σ 0 := fun j => Function.update_of_ne (by omega) _ _
  refine bdd_nsum_le1 (n := .var 0) (by show σ 0 ≤ V; omega) (by show σ 0 ≤ V; omega) ?_ ?_
  · intro j hj
    have hj' : j < σ 0 := hj
    have e00 : Ex.eval σ A (.var 0) = σ 0 := rfl
    refine bdd_ifLt (bdd_lit (Nat.zero_le V)) ?_ (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (Nat.zero_le V))
    refine bdd_nsum_le1 (n := .var 0) (by show Function.update σ (u + 60) j 0 ≤ V; rw [h0']; omega)
      (by show Function.update σ (u + 60) j 0 ≤ V; rw [h0']; omega) ?_ ?_
    · intro k hk
      have hk' : k < σ 0 := by
        have : k < Function.update σ (u + 60) j 0 := hk
        rwa [h0'] at this
      have t0 : Function.update (Function.update σ (u + 60) j) (u + 61) k 0 = σ 0 := by
        rw [Function.update_of_ne (by omega)]; exact h0' j
      have t1 : Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 61) = k := Function.update_self ..
      have t2 : Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 60) = j := by
        rw [Function.update_of_ne (by omega)]; exact Function.update_self ..
      refine bdd_ifLt (show Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 61) ≤ V by rw [t1]; omega)
        (show Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 60) ≤ V by rw [t2]; omega)
        (fun _ => bdd_lit (Nat.zero_le V)) (fun _ => ?_)
      refine bdd_nbitW (w := .var 0) (show Function.update (Function.update σ (u + 60) j) (u + 61) k 0 ≤ V by rw [t0]; omega)
        (show Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 61) ≤ V by rw [t1]; omega)
        (show Function.update (Function.update σ (u + 60) j) (u + 61) k 0 ≤ V by rw [t0]; omega) H.hA (by omega)
    · intro k
      simp only [Ex.eval]
      by_cases hh : Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 61) < Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 60)
      · simp only [hh, if_true]; omega
      · simp only [hh, if_false]; exact eval_nbitW_le' _ _ _
  · intro j
    exact ite01_le _

theorem bdd_log2E2 {L : ℕ} (N : LNum2 V L) (h63 : σ (u + 63) = L) : Bdd V σ A (log2E2 u (.var (u + 63))) := by
  have h4 := N.hL4
  have h40 := N.h40
  refine bdd_nsum_le1 (n := .var (u + 63)) (by show σ (u + 63) ≤ V; omega) (by show σ (u + 63) ≤ V; omega) ?_ ?_
  · intro j hj
    have hj' : j < L := by
      have : j < σ (u + 63) := hj
      omega
    have e1 : Function.update σ (u + 60) j (u + 63) = L := by rw [Function.update_of_ne (by omega)]; exact h63
    have e2 : Function.update σ (u + 60) j (u + 60) = j := Function.update_self ..
    refine bdd_ifLt (bdd_lit (Nat.zero_le V)) ?_ (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (Nat.zero_le V))
    have hit : ∀ j', iterF (fun j'' s => Ex.eval (Function.update (Function.update (Function.update σ (u + 60) j) (u + 61) j'') (u + 62) s) A
        (Ex.div (Ex.var (u + 62)) (Ex.lit 2))) (Ex.eval (Function.update σ (u + 60) j) A (.var (u + 63))) j' = L / 2 ^ j' := by
      intro j'
      rw [show Ex.eval (Function.update σ (u + 60) j) A (.var (u + 63)) = L from e1, ← iterF_half]
      congr 1
      funext j'' s
      simp [Ex.eval]
    refine ⟨?_, ?_, ?_⟩
    · show Bdd V (Function.update σ (u + 60) j) A (Ex.add (Ex.var (u + 60)) (Ex.lit 1))
      refine ⟨show Function.update σ (u + 60) j (u + 60) ≤ V by rw [e2]; omega, bdd_lit (by omega), ?_⟩
      simp only [Ex.eval]; rw [e2]; omega
    · show Function.update σ (u + 60) j (u + 63) ≤ V
      rw [e1]; omega
    · intro j' hj'
      rw [hit]
      refine ⟨show _ ≤ V from ?_, bdd_lit (by omega)⟩
      simp only [Function.update_self]
      exact le_trans (Nat.div_le_self _ _) (by omega)
  · intro j
    exact ite01_le _

end

section prel2
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (u : ℕ) {n : ℕ}
  {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} {L : ℕ}

theorem bdd_jm1E2 (N : LNum2 V L) (h63 : σ (u + 63) = L) : Bdd V σ A (jm1E2 u) := by
  have h4 := N.hL4
  have h40 := N.h40
  have hlog := eval_log2E2' u (σ := σ) (A := A) L h63
  have hle : Nat.log 2 L ≤ L := Nat.log_le_self 2 L
  refine ⟨⟨⟨bdd_log2E2 u N h63, (show 2 ≤ V by omega), ?_⟩, (show 4 ≤ V by omega)⟩, (show 1 ≤ V by omega)⟩
  simp only [Ex.eval]; rw [hlog]; omega

theorem bdd_prel2 (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW)
    (N : LNum2 V (Nat.size p)) (body : Ex) (hb : Bdd V (st u σ (Nat.size p)) A body) : Bdd V σ A (prel2 u body) := by
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
  refine ⟨bdd_szE2 u H, ?_⟩
  rw [eval_szE2 u hR]
  refine ⟨bdd_jm1E2 u N (by simp), ?_⟩
  rw [eval_jm1E2 u (Nat.size p) (by simp)]
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
variable (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW)
  (N : LNum2 V (Nat.size p))
include H hR N

theorem bdd_AEx2 : Bdd V σ A (AEx2 u) := by
  refine bdd_prel2 u H hR N _ ?_
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

theorem bdd_hEx2 : Bdd V σ A (hEx2 u) := by
  refine bdd_prel2 u H hR N _ ?_
  have hD := D_le (Nat.size p)
  have h4 := N.hL4
  have hjm := jm1_le (Nat.size p)
  have h2 : 2 ≤ V := by have := N.h40; omega
  refine bdd_pow2 (x := u + 60) ?_ h2 ?_
  · show st u σ (Nat.size p) (u + 64) ≤ V; rw [st_64]; omega
  · simp only [Ex.eval, st_64]
    refine le_trans (Nat.pow_le_pow_right (by norm_num) (show jm1 (Nat.size p) ≤ kP (Nat.size p) by unfold kP; omega)) ?_
    omega

theorem bdd_pbEx2 : Bdd V σ A (pbEx2 u) := by
  refine bdd_prel2 u H hR N _ ?_
  have hbP := bP_lt (Nat.size p)
  have h2 : 2 ≤ V := by have := N.h40; omega
  have hpb := N.hpb
  refine bdd_pow2 (x := u + 60) ?_ h2 ?_
  · show st u σ (Nat.size p) (u + 67) ≤ V; rw [st_67]; omega
  · simp only [Ex.eval, st_67]; exact hpb

theorem bdd_bEx2 : Bdd V σ A (bEx2 u) := by
  refine bdd_prel2 u H hR N _ ?_
  have hbP := bP_lt (Nat.size p)
  have hpb := N.hpb
  show st u σ (Nat.size p) (u + 67) ≤ V; rw [st_67]; omega

theorem bdd_MEx2 : Bdd V σ A (MEx2 u) := by
  refine bdd_prel2 u H hR N _ ?_
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

end prel2

section eps2
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ} (cv tv u : ℕ)
  {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem bdd_epsEx2 (H : BN V σ A n) (hn : 40 * n + 40 ≤ V) (hc : σ cv < 18 * n + 12) (ht : σ tv ≤ V)
    (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (N : LNum2 V (Nat.size p)) :
    Bdd V σ A (epsEx2 u n cv tv) := by
  have h2 : 2 ≤ V := by omega
  refine bdd_ifLt (bdd_negEx cv H hn hc tv ht) (bdd_lit (by omega)) (fun _ => bdd_lit (by omega)) (fun _ => ?_)
  refine bdd_pow2 (bdd_MEx2 u H hR N) h2 ?_
  rw [eval_MEx2 u hR]
  exact N.hM2

end eps2

end ECDLP.L95
end
