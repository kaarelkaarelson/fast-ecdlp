import ECDLP.L75_Ib3
import ECDLP.L79_Dig2

/-!
# L79 / IbC: the `ib` node expression with a digit expression `D` in place of `digE X u (u+1)`
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L68 (ibE hatE pwE sumE mulE eval_fv rp_ibOut rp_mul rp_hat Rp)
open ECDLP.L75 (ibE2 rp_ibOut2 ibZ pm_mid_lt ib_child out_ib_q mid_mem_ib)

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}

def ibBodyD (D pmidE : Ex) : Ex := .lett (u + 1) pmidE D

def ibOutL2D (D : Ex) (vq vA x1 : ℕ) (e0 tE kE pmidE : Ex) : Ex :=
  .lett u (.var (u + 5)) (.lett (u + 2) (.var (u + 7)) (ibE2 vq vA x1 e0 tE kE (ibBodyD (u := u) D pmidE)))

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ



theorem ib_hout2D (D : Ex) {vq vA x1 : ℕ} (hvq : u + 10 ≤ vq ∧ vq < x1) (hvA : u + 10 ≤ vA ∧ vA < x1) (hx1 : u + 10 ≤ x1)
    {a b : Fin g} {c : Fin K} {j1 : Fin N0.A} (hka : e.symm a = CG.gt c (Gate.ib j1))
    (hpa : e.symm a ∈ (edgeNetM (w := w) φ F ok m).pa (e.symm b)) (hM : 1 ≤ (NP N0 w c).M)
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = N0.A)
    {e0 tE kE pmidE : Ex} (h0 : Ex.FV (fun y => u + 10 ≤ y ∧ y < x1) e0) (hT : Ex.FV (fun y => u + 10 ≤ y ∧ y < x1) tE)
    (hE : Ex.eval σ A e0 = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1))
    (hTv : Ex.eval σ A tE = (NP N0 w c).tInv.val)
    (hk : Ex.FV (fun y => u + 10 ≤ y ∧ y < x1) kE)
    (hkv : ∀ j : Fin (N0.A * N0.A), e.symm b = CG.gt c (Gate.car j) → Ex.eval σ A kE = j.val / N0.A)
    (hpm : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → ∀ (i : ℕ) (hi : i < N0.A), σ' x1 = i →
      Ex.eval σ' A pmidE = e (CG.gt c (Gate.mid ⟨i, hi⟩)))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z)
    (hD : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, u + 10 ≤ y → y < x1 → τ y = σ y) → ∀ (i : Fin N0.A), τ u = a →
      τ (u + 1) = e (CG.gt c (Gate.mid i)) →
      τ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
        (hF := edge_free_nonempty φ F ok m)).e a z → Ex.eval τ A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.mid i)))
    (ha : σ (u + 5) = a) :
    Ex.eval σ A (ibOutL2D (u := u) D vq vA x1 e0 tE kE pmidE) =
      ec (ι := ι) (ιc := ιc) (w := w) (e.symm a) ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b)) := by
  obtain ⟨j, hbj, -⟩ := ib_child (w := w) φ c j1 (e.symm b) (hka ▸ hpa)
  rw [hbj, out_ib_q (w := w) φ F ok m c j1 (e.symm a) hka z c j]
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have a2 : σ2 (u + 5) = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact ha
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  have hz2 : σ2 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]; exact hz
  have low : ∀ y, u + 10 ≤ y → σ2 y = σ y := by
    intro y hy
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have hq2 : σ2 vq = 2 ^ (NP N0 w c).M + 1 := by rw [low vq hvq.1]; exact hq'
  have hA2 : σ2 vA = N0.A := by rw [low vA hvA.1]; exact hA'
  have hE2 : Ex.eval σ2 A e0 = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
    rw [← eval_fv h0 (fun y hy => (low y hy.1).symm)]; exact hE
  have hT2 : Ex.eval σ2 A tE = (NP N0 w c).tInv.val := by
    rw [← eval_fv hT (fun y hy => (low y hy.1).symm)]; exact hTv
  have hK2 : Ex.eval σ2 A kE = j.val / N0.A := by
    rw [← eval_fv hk (fun y hy => (low y hy.1).symm)]
    exact hkv j hbj
  have hbody : ∀ i < N0.A, Rp (Function.update σ2 x1 i) A (ibBodyD (u := u) D pmidE) (ibZ (w := w) φ F ok m c j1 z i) := by
    intro i hi
    set σ3 := Function.update σ2 x1 i with hσ3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
    have hp := hpm σ3 (fun y hy1 hy2 => by
        rw [hσ3, Function.update_of_ne (by omega)]; exact low y hy1) i hi (by rw [hσ3, Function.update_self])
    set σ4 := Function.update σ3 (u + 1) (Ex.eval σ3 A pmidE) with hσ4
    have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
    have hd : Ex.eval σ4 A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.mid ⟨i, hi⟩)) :=
      hD σ4 g4 (fun y hy1 hy2 => by
        rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact low y hy1) ⟨i, hi⟩
        (by rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact u2)
        (by rw [hσ4, Function.update_self, hp])
        (by rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact hz2)
    unfold Rp
    show Ex.eval σ4 A D = _
    rw [hd]
    unfold ibZ
    rw [dif_pos hi, ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt (pm_mid_lt (w := w) φ F ok m c j1 ⟨i, hi⟩ _ hka z)).symm
  have hmain := rp_ibOut2 (σ := σ2) (A := A) (NP N0 w c) hM hq2 (show vq < x1 by omega) (show vA < x1 by omega) hA2
    (e0 := e0) (tE := tE) (k := kE) (u := ibBodyD (u := u) D pmidE)
    (Ex.FV_mono (fun y hy => by omega) _ h0) (Ex.FV_mono (fun y hy => by omega) _ hk) hE2 hT2 hK2
    (ibZ (w := w) φ F ok m c j1 z) hbody
  exact hmain


end node
end ECDLP.L79
end
