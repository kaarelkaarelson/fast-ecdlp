import ECDLP.L92_Final
import ECDLP.L88_Eng

/-!
# L92 / Hr: removing `r + 1 <= 2^19000` from the engine interface (item 3)

`famH r` is `edgeFamily r` with the extra requirement `Ub r n <= V` in `FamOK` (and the matching extra exponent `Uc + 4 X` in `eFam`, which is
what makes `Spec.req_of_exp` provable without the size hypothesis on `r`).  `ShapeData`, the top width bound and `TopIface` are re-run
for `famH r` with `Ub r n <= V` taken from `FamOK` instead of `ok_U0 hr`.  The proofs are those of L85_B (Core, Width, Final), copied.
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A

/-- `edgeFamily r` with `Ub r n <= V` built into `FamOK` -/
def famH (r : ℕ) : NetFamily :=
  { edgeFamily r with
    eFam := fun K g n => eFamE r K g n + (Uc r + 4 * Xs n)
    FamOK := fun V m K0 ℓ n => EdgeReq r V m K0 ℓ n ∧ Ub r n ≤ V }

/-- **Value bound of the literal-free top width** at the value bound `W` (a family requirement at `W`). -/
theorem edgeL0v_bddH {r n ℓ W : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (R : EdgeReq r W 2 K0u ℓ n) (hU : Ub r n ≤ W)
    (tk : ∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) (h11 : σ 11 = sOf n) :
    Bdd W σ A (edgeL0v r) := by
  set K := Kb K0u ℓ with hKdef
  set g := 3 * K ^ 8 with hgdef
  have hK48 : 48 ≤ K := Kb_ge_K0 K0u ℓ
  have hg1 : 1 ≤ g := by have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have hKG : K * g ≤ W := R.hKG
  have hK3 : 64 * K ^ 3 ≤ W := R.hK3
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
theorem edgeL0v_costH {r n ℓ V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (R : EdgeReq r (Wv V) 2 K0u ℓ n) (hU : Ub r n ≤ Wv V)
    (tk : ∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) (h11 : σ 11 = sOf n) :
    cost σ A (edgeL0v r) ≤ PB DB V :=
  cost_le_PB (edgeL0v_bddH R hU tk h11) (edgeL0v_dp r)


/-- **`ShapeData` for the edge family** from the gate-network core (the side condition `r + 1 <= 2^19000` is for
`ok_U0`). -/
def shapeData_edgeH (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    ShapeData DB (famH r) (edgeShape r E gE btE) (searchMv E gE btE) (tabMv E gE btE) where
  hsF n := rfl
  hLtop K g n := rfl
  hSX K := searchM_LS C.syn K (3 * K ^ 8)
  hTX K := tabM_LS C.syn K (3 * K ^ 8)
  hRd g := cpM_rd C.syn g
  dpS K g := searchM_dp C.syn K g 13 14
  dpT K g := tabM_dp C.syn K g
  D m n k A := (C.D m n k A).toRep
  hcong m n k A A' h := by rw [C.hcong m n k A A' h]
  hyp m n k A g hg σ₀ hm hkn h10 h11 h0 h2 :=
    coarsenHyp_of_cluster (C.rep m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) (C.hgI m n k A) hg
      (C.clh m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hm
  fits m n k A g hg := by
    have hf := (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg (C.hrow m n k A) (Wm r n)
      (C.hmax m n k A)).1
    intro γ
    refine le_trans (hf γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _
  total m n k A g hg :=
    le_trans (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg (C.hrow m n k A) (Wm r n)
      (C.hmax m n k A)).2 (C.htot m n k A)
  Wc n g := Pb r g n
  csz m n k A g hg γ := by
    refine le_trans (coarsen_s_le (C.D m n k A).κ (clus (C.D m n k A).wt g hg) γ (C.D m n k A).wt
      (fun a _ => C.hheld m n k A a)) (Nat.pow_le_pow_right (by norm_num) ?_)
    refine le_trans (clus_wt_sum_le (C.D m n k A).wt (Wm r n) (C.hmax m n k A) g hg γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _
  bdd V m ℓ n k A R hm hkn hA σ₀ h10 h11 h0 h2 hg := by
    have hK2 : 2 ≤ Kb K0u ℓ := Kb_ge K0u (by norm_num) ℓ
    obtain ⟨hEb, hgb, hbb⟩ := C.bnd V m ℓ n k A R.1 hkn hA σ₀ ⟨h10, h11, h0, h2⟩
    have hmm : m * m ≤ V := R.1.mm
    have hV1 : 1 ≤ V := by have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity); omega
    have hW : ∑ a, (C.D m n k A).wt a ≤ V := le_trans (C.htot m n k A) (R.2)
    have hgW : Gs K0u ℓ * ∑ a, (C.D m n k A).wt a ≤ V := by
      refine le_trans (Nat.mul_le_mul_left _ (C.htot m n k A)) (le_trans (gUb_le hK2) R.1.hgrp)
    exact coarsenBdd_of_cluster hg (C.clh m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hEb hgb hbb hmm
      (Gs_le_V (by norm_num) R.1) (le_trans (gI_sq_le (g := Gs K0u ℓ) (C.hnodes m n k A)) R.1.hWc) hV1 hW hgW
      (C.hrow m n k A) (C.hheld m n k A) (Wm r n) (C.hmax m n k A) (Pb r (Gs K0u ℓ) n)
      (Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _) R.1.hWc
  ok_mm R := R.1.mm
  ok_Kg R := R.1.hKg
  ok_gg R := R.1.hgg
  ok_KG R := R.1.hKG
  ok_g1 R := R.1.hg1
  ok_U0 R := R.2
  ok_P0 R := R.1.hWc
  ok_grp R := R.1.hgrp
  ok_LK R := R.1.hLK
  ok_m1 R := R.1.hm
  ok_hn R := R.1.hn
  ok_deep R := R.1.deep
  vS := searchMv_vb C.syn
  vT := tabMv_vb C.syn


end ECDLP.L85B
end
