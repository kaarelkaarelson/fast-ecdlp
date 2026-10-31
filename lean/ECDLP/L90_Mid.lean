import ECDLP.L79_KindC

/-!
# L90 / Mid: the mid gate of an identity with NO used slot (`(F c).n = 0`, empty slot type)

`rp_mid0`, `rp_midMsg0`: `rp_mid` / `rp_midMsg` of L68 for `n = 0`; no slot decoder `dec`, no term oracles, no `Y`.
`mid_hout0`: `mid_houtD` of L79 for `(F c).n = 0` (no `dec`, `hl`, `hr`, `hpfa`, `hD`, `heps`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79
open ECDLP.L74 (midIn mid_child mid_fa_mem out_mid_q Agr eval_midIn)

section ring
variable {q : ℕ} [NeZero q] {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vq : ℕ}

theorem rp_mid0 (hq : σ vq = q) (hq2 : 2 < q) {vA x1 x2 x3 vI vS : ℕ} (hvq : vq < x1) (hvA : vA < x1)
    {A' : ℕ} (hA : σ vA = A')
    {ei ew k1 j1 nE epsE lE rE yE : Ex}
    (hei : Ex.FV (· < x1) ei) (hk1 : Ex.FV (· < x1) k1) (hj1 : Ex.FV (· < x1) j1)
    (hn : Ex.FV (· < x1) nE)
    {Ei K1 J1 : ℕ} (hEi : Ex.eval σ A ei = Ei) (hK1 : Ex.eval σ A k1 = K1)
    (hJ1 : Ex.eval σ A j1 = J1) (hnv : Ex.eval σ A nE = 0) :
    Rp σ A (midE vq vA x1 x2 x3 vI vS ei ew k1 j1 nE epsE lE rE yE)
      (faOut A' ((2 : ZMod q) ^ Ei) K1 (fun _ => 0) J1) := by
  refine rp_fa hq hq2 hvq hvA hA hei hk1 hj1 hEi hK1 hJ1 _ fun k₂ hk₂ => ?_
  have hq1 : (Function.update σ x1 k₂) vq = q := by rw [Function.update_of_ne (by omega)]; exact hq
  have hn1 : Ex.eval (Function.update σ x1 k₂) A nE = 0 := by rw [eval_stab hn (le_refl _)]; exact hnv
  show Rp _ A _ (0 : ZMod q)
  rw [show (0 : ZMod q) = ∑ i ∈ range 0, (fun _ => (0 : ZMod q)) i by simp]
  exact rp_sum hq1 hn1 (fun _ => (0 : ZMod q)) (fun i hi => absurd hi (by omega))

end ring

section msg
variable {q : ℕ} [NeZero q] {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vq : ℕ}

theorem rp_midMsg0 {ι : Type} (N : NPar) (hM : 1 ≤ N.M) (F : Form ι) {vq vA x1 x2 x3 vI vS : ℕ}
    (hq : σ vq = 2 ^ N.M + 1) (hvq : vq < x1) (hvA : vA < x1) (hA : σ vA = N.A)
    {ei ew k1 j1 nE epsE lE rE yE : Ex}
    (hei : Ex.FV (· < x1) ei) (hk1 : Ex.FV (· < x1) k1) (hj1 : Ex.FV (· < x1) j1)
    (hn : Ex.FV (· < x1) nE)
    {K1 J1 : ℕ} (hEi : Ex.eval σ A ei = N.w * (2 ^ (N.k + 1) - 1))
    (hK1 : Ex.eval σ A k1 = K1) (hJ1 : Ex.eval σ A j1 = J1) (hnv : Ex.eval σ A nE = F.n) (hn0 : F.n = 0)
    (Y : ι → ℕ → N.Rg) :
    Rp σ A (midE vq vA x1 x2 x3 vI vS ei ew k1 j1 nE epsE lE rE yE) (N.midMsg F K1 Y J1) := by
  classical
  have hmid := rp_mid0 (q := 2 ^ N.M + 1) (A := A) (x2 := x2) (x3 := x3) (vI := vI) (vS := vS) (ew := ew) (epsE := epsE)
    (lE := lE) (rE := rE) (yE := yE) hq (q_gt N hM) hvq hvA hA hei hk1 hj1 hn hEi hK1 hJ1 (by rw [hnv, hn0])
  have e1 : N.ωi = (2 : ZMod (2 ^ N.M + 1)) ^ (N.w * (2 ^ (N.k + 1) - 1)) := by
    unfold Par.ωi Par.ω; rw [pow_mul]
  unfold Par.midMsg
  rw [e1]
  haveI : IsEmpty (Fin F.n) := by rw [hn0]; infer_instance
  have hfun : (fun k₂ => ∑ t : Fin F.n, (F.ε t : N.Rg) * (hatOut N.A N.ω (Y (F.l t)) k₂ * hatOut N.A N.ω (Y (F.r t)) k₂)) =
      (fun _ => (0 : N.Rg)) := by
    funext k₂; simp
  rw [hfun]
  exact hmid

end msg

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)
  {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

/-- **`hout` for a mid node whose identity has no term** (`(F c).n = 0`): no slot decoder is needed. -/
theorem mid_hout0 (D : Ex) {vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vK))
    (hvA : vA < u ∨ (u + 2 < vA ∧ vA < vK)) (hvei : vei < u ∨ (u + 2 < vei ∧ vei < vK))
    (hvw : vw < u ∨ (u + 2 < vw ∧ vw < vK))
    (hK : u + 10 ≤ vK) (hJ : u + 10 ≤ vJ) (hKJ : vK < vJ) (hK1 : vK < x1) (hJ1 : vJ < x1) (hx1 : u + 10 ≤ x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    {a b : Fin g} {c : Fin K} {k : Fin N0.A} (hM : 1 ≤ (NP N0 w c).M) (hka : e.symm a = CG.gt c (Gate.mid k))
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = (NP N0 w c).A)
    (hei' : σ vei = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1)) (hw' : σ vw = (NP N0 w c).w)
    (hab : e.symm a ∈ paC (w := w) φ (e.symm b)) {kE j1E nE epsE lE rE pfaE : Ex}
    (hkE : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A kE = k.val)
    (hjE : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ c' : Fin K, ∀ j₁ : Fin N0.A, e.symm b = CG.gt c' (Gate.ib j₁) →
      Ex.eval σ' A j1E = j₁.val)
    (hnFV : Ex.FV (· < x1) nE)
    (hn : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A nE = (F c).n) (hn0 : (F c).n = 0)
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z)
    (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Ex.eval σ A (midOutLD (u := u) D vq vA vei vw vK vJ x1 x2 x3 vI vS kE j1E nE epsE lE rE pfaE) =
      ec (ι := ι) (ιc := ιc) (w := w) (e.symm a) ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b)) := by
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, e.symm b = CG.gt c (Gate.ib j₁) := by
    rw [hka] at hab; exact mid_child φ c k hab
  obtain ⟨σ5, h, g5, h1, h2, h3, h4, h5, h6⟩ := eval_midIn hu hC hσ (body := midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw)
    (.var vK) (.var vJ) nE epsE lE rE (midYD (u := u) D pfaE)) hK hJ hKJ (b := b) (c' := c) (j₁ := j₁) hka hkE
    (fun σ' hσ' => hjE σ' hσ' c j₁ hj₁) z hz ha hb
  obtain ⟨Y, hY1, hY2⟩ := out_mid_q (w := w) φ F ok m c k (e.symm a) hka z c j₁ (e.symm b) hj₁
  rw [hY2]
  unfold midOutLD
  rw [h]
  have hq7 : σ5 vq = 2 ^ (NP N0 w c).M + 1 := by rw [h6 _ hvq]; exact hq'
  have hA7 : σ5 vA = (NP N0 w c).A := by rw [h6 _ hvA]; exact hA'
  have hei7 : σ5 vei = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by rw [h6 _ hvei]; exact hei'
  exact rp_midMsg0 (NP N0 w c) hM (F c) (σ := σ5) (A := A) (vq := vq) (vA := vA) (x1 := x1) (x2 := x2) (x3 := x3)
    (vI := vI) (vS := vS) hq7 (by omega) (by omega) hA7
    (ei := .var vei) (ew := .var vw) (k1 := .var vK) (j1 := .var vJ) (nE := nE) (epsE := epsE) (lE := lE) (rE := rE)
    (yE := midYD (u := u) D pfaE) (by simp only [Ex.FV]; omega) (by simp only [Ex.FV]; omega)
    (by simp only [Ex.FV]; omega) hnFV (by simp only [Ex.eval]; exact hei7)
    (by simp only [Ex.eval]; exact h1) (by simp only [Ex.eval]; exact h2) (by rw [hn σ5 h6]) hn0 Y

end node
end ECDLP.L90
end
