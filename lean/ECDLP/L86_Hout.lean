import ECDLP.L86_Car

/-!
# L86 / Hout: `hout` and `hwt` for the repaired car expressions `carOutXD`, `carWXD` (state = L73's decode state)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79

section node
variable {m B : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include X hu hC hσ

/-- the facts about the car binders: after `carInD`, the slots `u+93`, `u+94` hold the carry code and the ring code -/
theorem eval_carInD {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)} (body : Ex)
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j))
    (h11 : σ (u + 11) = 2 ^ (NP N0 w c).M) (h16 : σ (u + 16) = j.val)
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)
      (hF := edge_free_nonempty φ F ok m)).e a z) :
    ∃ σ2 : ℕ → ℕ, Ex.eval σ A (carInD u (u + 16) (u + 93) (u + 94) body) = Ex.eval σ2 A body ∧
      σ2 (u + 93) = carCiQ (w := w) φ F ok m c j z ∧ σ2 (u + 94) = carRQ (w := w) φ F ok m c j z ∧
      (∀ y, y ≠ u + 93 → y ≠ u + 94 → σ2 y = σ y) := by
  have g0 : Ag B σ₀ (Function.update σ (u + 2) (σ (u + 7))) := hσ.upd (by omega) _
  have z0 : (Function.update σ (u + 2) (σ (u + 7))) (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)
      (edgeEFM φ F ok m) (L.enum N0.A) (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [Function.update_self]; exact hz
  have hR := pm_car_ib L X hu hC g0 hka z z0
  rw [Function.update_self] at hR
  have hvc : Ex.eval σ A (.ifLt (.lit 0) (.var (u + 16)) (digCarC u) (.lit 0)) = carCiQ (w := w) φ F ok m c j z := by
    simp only [Ex.eval, h16]
    unfold carCiQ
    by_cases h0 : 0 < j.val
    · simp only [h0, if_true]
      have hP := pm_car_prev L X hu hC g0 hka h0 z z0
      rw [Function.update_self] at hP
      rw [hP]
      simp only [digCarC, Ex.eval, h11]
      rw [show 8 * 2 ^ (NP N0 w c).M = 2 ^ ((NP N0 w c).M + 3) by ring]
    · simp [h0]
  set σ1 := Function.update σ (u + 93) (Ex.eval σ A (.ifLt (.lit 0) (.var (u + 16)) (digCarC u) (.lit 0))) with h1
  have hr : Ex.eval σ1 A (digCarR u) = carRQ (w := w) φ F ok m c j z := by
    unfold carRQ
    rw [hR]
    simp only [digCarR, Ex.eval, h1, Function.update_of_ne (show u + 7 ≠ u + 93 by omega),
      Function.update_of_ne (show u + 11 ≠ u + 93 by omega), hz, h11]
  set σ2 := Function.update σ1 (u + 94) (Ex.eval σ1 A (digCarR u)) with h2
  refine ⟨σ2, rfl, ?_, ?_, ?_⟩
  · rw [h2, Function.update_of_ne (by omega), h1, Function.update_self, hvc]
  · rw [h2, Function.update_self, hr]
  · intro y hy1 hy2
    rw [h2, Function.update_of_ne hy2, h1, Function.update_of_ne hy1]

theorem car_houtD {a b : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j))
    (h10 : σ (u + 10) = 2 ^ (NP N0 w c).b) (h11 : σ (u + 11) = 2 ^ (NP N0 w c).M) (h16 : σ (u + 16) = j.val)
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)
      (hF := edge_free_nonempty φ F ok m)).e a z) :
    Ex.eval σ A (carOutXD u) =
      ec (ι := ι) (ιc := ιc) (w := w) ((L.enum N0.A).symm a)
        ((edgeNetM (w := w) φ F ok m).out ((L.enum N0.A).symm a) z ((L.enum N0.A).symm b)) := by
  obtain ⟨σ2, h, hc, hr, hs⟩ := eval_carInD L X hu hC hσ (carOutE (u + 10) (u + 11) (u + 16) (u + 93) (u + 94)) hka h11 h16 z hz
  rw [out_car_q (w := w) φ F ok m c j _ hka z ((L.enum N0.A).symm b)]
  unfold carOutXD
  rw [h, eval_carOutE (NP N0 w c) (by rw [hs _ (by omega) (by omega)]; exact h10) (by rw [hs _ (by omega) (by omega)]; exact h11),
    hc, hr, hs _ (by omega) (by omega), h16]

open Classical in
theorem car_hwtD (hm1 : 1 < m) {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j))
    (h10 : σ (u + 10) = 2 ^ (NP N0 w c).b) (h11 : σ (u + 11) = 2 ^ (NP N0 w c).M) (h16 : σ (u + 16) = j.val)
    (h28 : σ (u + 28) = (NP N0 w c).A * (NP N0 w c).A)
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)
      (hF := edge_free_nonempty φ F ok m)).e a z) :
    Ex.eval σ A (carWXD u) =
      if (edgeNetM (w := w) φ F ok m).W ((L.enum N0.A).symm a) z = 1 then 1 else 0 := by
  obtain ⟨σ2, h, hc, hr, hs⟩ := eval_carInD L X hu hC hσ (carWE (u + 10) (u + 11) (u + 16) (u + 28) (u + 93) (u + 94)) hka h11 h16 z hz
  rw [w_car_q (w := w) φ F ok m hm1 c j _ hka z]
  unfold carWXD
  rw [h, eval_carWE (NP N0 w c) (by rw [hs _ (by omega) (by omega)]; exact h10) (by rw [hs _ (by omega) (by omega)]; exact h11)
    (by rw [hs _ (by omega) (by omega)]; exact h28), hc, hr, hs _ (by omega) (by omega), h16]

end node
end ECDLP.L86
end
