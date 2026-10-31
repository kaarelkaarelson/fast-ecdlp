import ECDLP.L74_MidOut
import ECDLP.L79_Dig2

/-!
# L79 / MidC: the mid kind with the shallow digit expression

`midYD D pfaE = lett (u+1) pfaE D`: L74's `midY` with the digit expression `D` in place of `digE X u (u+1)` (depth 35).  `mid_houtD` is `mid_hout` with the
hypothesis that `D` computes the digit (`hD`), instead of `eval_digE_pm`; `midKindC` instantiates `D := digCmid u` (depth 5), so the free-variable facts
`hXnf, hXnm, hXpar` of L74's `midKind` are not needed.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (midIn mid_child mid_fa_mem out_mid_q Agr eval_midIn)

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

/-- the message of the parent `fa (dec i) s`, with the digit expression `D` (to be run with `u+1` = the parent index) -/
def midYD (D pfaE : Ex) : Ex := .lett (u + 1) pfaE D

def midOutLD (D : Ex) (vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ) (kE j1E nE epsE lE rE pfaE : Ex) : Ex :=
  midIn (u := u) vK vJ kE j1E
    (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE (midYD (u := u) D pfaE))

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

/-- **`hout` for a mid node.** -/
theorem mid_houtD (D : Ex) {vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vK))
    (hvA : vA < u ∨ (u + 2 < vA ∧ vA < vK)) (hvei : vei < u ∨ (u + 2 < vei ∧ vei < vK))
    (hvw : vw < u ∨ (u + 2 < vw ∧ vw < vK))
    (hK : u + 10 ≤ vK) (hJ : u + 10 ≤ vJ) (hKJ : vK < vJ) (hK1 : vK < x1) (hJ1 : vJ < x1) (hx1 : u + 10 ≤ x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    {a b : Fin g} {c : Fin K} {k : Fin N0.A} (hM : 1 ≤ (NP N0 w c).M) (hka : e.symm a = CG.gt c (Gate.mid k))
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = (NP N0 w c).A)
    (hei' : σ vei = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1)) (hw' : σ vw = (NP N0 w c).w)
    (hab : e.symm a ∈ paC (w := w) φ (e.symm b)) {kE j1E nE epsE lE rE pfaE : Ex} (dec : ℕ → ιc c)
    (hkE : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A kE = k.val)
    (hjE : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ c' : Fin K, ∀ j₁ : Fin N0.A, e.symm b = CG.gt c' (Gate.ib j₁) →
      Ex.eval σ' A j1E = j₁.val)
    (hnFV : Ex.FV (· < x1) nE) (hεFV : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hlFV : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hrFV : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hpfaFV : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) pfaE)
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z)
    (hDfv : Ex.FV (fun y => y < x1 ∨ y = u + 1) D)
    (hD : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → τ y = σ y) → ∀ (kk : Fin g) (i : ιc c) (s : Fin N0.A),
      e.symm kk = CG.gt c (Gate.fa i s) → τ u = a → τ (u + 1) = kk →
      τ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
        (hF := edge_free_nonempty φ F ok m)).e a z → Ex.eval τ A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.fa i s)))
    (hn : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' x2 t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t (ht : t < (F c).n),
      dec (Ex.eval (Function.update σ' x2 t) A lE) = (F c).l ⟨t, ht⟩)
    (hr : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t (ht : t < (F c).n),
      dec (Ex.eval (Function.update σ' x2 t) A rE) = (F c).r ⟨t, ht⟩)
    (hpfa : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ (i s : ℕ) (hs : s < N0.A), σ' vI = i → σ' vS = s →
      Ex.eval σ' A pfaE = e (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)))
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
  have hw7 : σ5 vw = (NP N0 w c).w := by rw [h6 _ hvw]; exact hw'
  have hfvY : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) (midYD (u := u) D pfaE) := by
    refine ⟨hpfaFV, ?_⟩
    exact Ex.FV_mono (fun y hy => by rcases hy with h | h; exact Or.inl (Or.inl h); exact Or.inr h) _ hDfv
  refine rp_midMsg (NP N0 w c) hM (F c) (σ := σ5) (A := A) (vq := vq) (vA := vA) (x1 := x1) (x2 := x2) (x3 := x3)
    (vI := vI) (vS := vS) hq7 (by omega) (by omega) h12 h23 h3I hIS hA7
    (ei := .var vei) (ew := .var vw) (k1 := .var vK) (j1 := .var vJ) (nE := nE) (epsE := epsE) (lE := lE) (rE := rE)
    (yE := midYD (u := u) D pfaE) (by simp only [Ex.FV]; omega) (by simp only [Ex.FV]; omega) (by simp only [Ex.FV]; omega)
    (by simp only [Ex.FV]; omega) hnFV hεFV hlFV hrFV hfvY (by simp only [Ex.eval]; exact hei7)
    (by simp only [Ex.eval]; exact hw7) (by simp only [Ex.eval]; exact h1) (by simp only [Ex.eval]; exact h2)
    (by rw [hn σ5 h6]) dec Y (fun t ht => heps σ5 h6 t ht) (fun t ht => hl σ5 h6 t ht) (fun t ht => hr σ5 h6 t ht) ?_
  intro i s hs
  have gI : Ag B σ₀ (Function.update σ5 vI i) := g5.upd (by omega) _
  have gS : Ag B σ₀ (Function.update (Function.update σ5 vI i) vS s) := gI.upd (by omega) _
  set c0 := Function.update (Function.update σ5 vI i) vS s with hc0
  have hp : Ex.eval c0 A pfaE = e (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)) :=
    hpfa c0 (Agr.upd (Agr.upd (show Agr u vK σ σ5 from h6) (x := vI) (by omega) i) (x := vS) (by omega) s) i s hs
      (by rw [hc0, Function.update_of_ne (by omega), Function.update_self]) (by rw [hc0, Function.update_self])
  unfold Rp
  have g1 : Ag B σ₀ (Function.update c0 (u + 1) (Ex.eval c0 A pfaE)) := gS.upd (by omega) _
  show Ex.eval (Function.update c0 (u + 1) (Ex.eval c0 A pfaE)) A D = _
  have hag : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → (Function.update c0 (u + 1) (Ex.eval c0 A pfaE)) y = σ y := by
    intro y hy
    rw [Function.update_of_ne (by omega), hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h6 y hy
  rw [hD _ g1 hag (e (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩))) (dec i) ⟨s, hs⟩ (by simp)
    (by rw [Function.update_of_ne (by omega), hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h4)
    (by rw [Function.update_self, hp])
    (by rw [Function.update_of_ne (by omega), hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h5)]
  exact hY1 (dec i) ⟨s, hs⟩


end node
end ECDLP.L79
end
