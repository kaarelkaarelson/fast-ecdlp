import ECDLP.L104_VUni
import ECDLP.L96_F
import ECDLP.L92_Hr3

/-!
# L104 / Core: `ShapeDataF` and `TopIfaceF` for `famH r` from the frame-restricted core `EdgeCoreF` (L96)
Copy of L92 `shapeData_edgeH` / L92 `topIface_edgeH`; every field of `EdgeCore` is read through `C.fields m n k A hP`, i.e. only at memories satisfying `P n A`.
-/
noncomputable section
namespace ECDLP.L104A
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A ECDLP.L85B

def shapeDataF_edgeH (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P DB r E gE btE) :
    ShapeDataF DB P (famH r) (edgeShape r E gE btE) (searchMv E gE btE) (tabMv E gE btE) where
  hsF n := rfl
  hLtop K g n := rfl
  hSX K := searchM_LS C.syn K (3 * K ^ 8)
  hTX K := tabM_LS C.syn K (3 * K ^ 8)
  hRd g := cpM_rd C.syn g
  dpS K g := searchM_dp C.syn K g 13 14
  dpT K g := tabM_dp C.syn K g
  D m n k A := (C.D m n k A).toRep
  hcong m n k A A' h := by rw [C.hcong m n k A A' h]
  hPc := hPc
  hPn := hPn
  hyp m n k A hP g hg σ₀ hm hkn h10 h11 h0 h2 :=
    coarsenHyp_of_cluster ((C.fields m n k A hP).rep σ₀ hm hkn ⟨h10, h11, h0, h2⟩) (C.fields m n k A hP).hgI hg
      ((C.fields m n k A hP).clh σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hm
  fits m n k A hP g hg := by
    have hf := (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg ((C.fields m n k A hP).hrow) (Wm r n)
      ((C.fields m n k A hP).hmax)).1
    intro γ
    refine le_trans (hf γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right ((C.fields m n k A hP).htot)) _
  total m n k A hP g hg :=
    le_trans (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg ((C.fields m n k A hP).hrow) (Wm r n)
      ((C.fields m n k A hP).hmax)).2 ((C.fields m n k A hP).htot)
  Wc n g := Pb r g n
  csz m n k A hP g hg γ := by
    refine le_trans (coarsen_s_le (C.D m n k A).κ (clus (C.D m n k A).wt g hg) γ (C.D m n k A).wt
      (fun a _ => (C.fields m n k A hP).hheld a)) (Nat.pow_le_pow_right (by norm_num) ?_)
    refine le_trans (clus_wt_sum_le (C.D m n k A).wt (Wm r n) ((C.fields m n k A hP).hmax) g hg γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right ((C.fields m n k A hP).htot)) _
  bdd V m ℓ n k A hP R hm hkn hA σ₀ h10 h11 h0 h2 hg := by
    have hK2 : 2 ≤ Kb K0u ℓ := Kb_ge K0u (by norm_num) ℓ
    obtain ⟨hEb, hgb, hbb⟩ := (C.fields m n k A hP).bnd V ℓ R.1 hkn hA σ₀ ⟨h10, h11, h0, h2⟩
    have hmm : m * m ≤ V := R.1.mm
    have hV1 : 1 ≤ V := by have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity); omega
    have hW : ∑ a, (C.D m n k A).wt a ≤ V := le_trans ((C.fields m n k A hP).htot) (R.2)
    have hgW : Gs K0u ℓ * ∑ a, (C.D m n k A).wt a ≤ V := by
      refine le_trans (Nat.mul_le_mul_left _ ((C.fields m n k A hP).htot)) (le_trans (gUb_le hK2) R.1.hgrp)
    exact coarsenBdd_of_cluster hg ((C.fields m n k A hP).clh σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hEb hgb hbb hmm
      (Gs_le_V (by norm_num) R.1) (le_trans (gI_sq_le (g := Gs K0u ℓ) ((C.fields m n k A hP).hnodes)) R.1.hWc) hV1 hW hgW
      ((C.fields m n k A hP).hrow) ((C.fields m n k A hP).hheld) (Wm r n) ((C.fields m n k A hP).hmax) (Pb r (Gs K0u ℓ) n)
      (Nat.add_le_add_right (Nat.div_le_div_right ((C.fields m n k A hP).htot)) _) R.1.hWc
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



theorem topIfaceF_edgeH (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P DB r E gE btE) :
    TopIfaceF DB P (famH r) (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE) :=
  topIfaceF_of_shape (shapeDataF_edgeH r hPc hPn C) (edgeL0v r) (edgeL0v_vb r) (edgeL0v_eval r)
    (fun V ℓ n σ A R tk h11 _ => edgeL0v_costH R.1 R.2 tk h11)

end ECDLP.L104A
end
