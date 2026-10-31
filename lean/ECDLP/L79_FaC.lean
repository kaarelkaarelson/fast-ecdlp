import ECDLP.L74_Fa
import ECDLP.L79_Dig2

/-!
# L79 / FaC: the fa node expression with a digit expression `D` in place of `digE X u (u+1)`

`faInD`, `faOutLD`, `fa_houtD`: L74's `faIn`, `faOutL`, `fa_hout` with the hypothesis `hD` (D computes the digit) instead of `eval_digE_pm`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (faUE rp_faUE fa_child fa_src_mem out_fa_q Agr)

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}

/-- the scratch binding of a fa node: `u := node`, `u+2 := code`, `vs := s`, `vk := k` (child), `u+1 := src index`,
`vcd := code of the slice` -/
def faInD (D : Ex) (vs vk vcd : ℕ) (sE kE psrcE body : Ex) : Ex :=
  .lett u (.var (u + 5)) (.lett (u + 2) (.var (u + 7))
    (.lett vs sE (.lett vk kE (.lett (u + 1) psrcE (.lett vcd D body)))))

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem eval_faInD (D : Ex) {vs vk vcd : ℕ} {body sE kE psrcE : Ex} (hs : u + 10 ≤ vs) (hk : u + 10 ≤ vk) (hcd : u + 10 ≤ vcd)
    (hsk : vs < vk) (hscd : vs < vcd) (hkcd : vk < vcd)
    {a b : Fin g} {c : Fin K} {j : ιc c} {s kk : Fin N0.A} {c' : Fin K}
    (hka : e.symm a = CG.gt c (Gate.fa j s)) (hkb : e.symm b = CG.gt c' (Gate.mid kk))
    (hsE : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A sE = s.val)
    (hkE : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A kE = kk.val)
    (hpsrc : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A psrcE = e (CG.src (φ c j) s))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z)
    (hD : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → τ y = σ y) → τ u = a →
      τ (u + 1) = e (CG.src (φ c j) s) →
      τ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
        (hF := edge_free_nonempty φ F ok m)).e a z → Ex.eval τ A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.src (φ c j) s))
    (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    ∃ σ7 : ℕ → ℕ, Ex.eval σ A (faInD (u := u) D vs vk vcd sE kE psrcE body) = Ex.eval σ7 A body ∧ σ7 vs = s.val ∧
      σ7 vk = kk.val ∧ σ7 vcd = ECDLP.L68.pm (w := w) φ F ok m z (CG.src (φ c j) s) ∧
      (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ7 y = σ y) := by
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have ag2 : Agr u vs σ σ2 := (Agr.refl'.upd (by omega) _).upd (by omega) _
  have a1 : σ1 (u + 5) = a := by rw [hσ1, Function.update_of_ne (by omega)]; exact ha
  have a2 : σ2 (u + 5) = a := by rw [hσ2, Function.update_of_ne (by omega)]; exact a1
  have b2 : σ2 (u + 6) = b := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact hb
  have hz2 : σ2 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]; exact hz
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  set σ3 := Function.update σ2 vs (Ex.eval σ2 A sE) with hσ3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have ag3 : Agr u vs σ σ3 := ag2.upd (by omega) _
  have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
  have b3 : σ3 (u + 6) = b := by rw [hσ3, Function.update_of_ne (by omega)]; exact b2
  have hs3 : σ3 vs = s.val := by rw [hσ3, Function.update_self]; exact hsE σ2 ag2
  set σ4 := Function.update σ3 vk (Ex.eval σ3 A kE) with hσ4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have ag4 : Agr u vs σ σ4 := ag3.upd (by omega) _
  have a4 : σ4 (u + 5) = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact a3
  have hk4 : σ4 vk = kk.val := by rw [hσ4, Function.update_self]; exact hkE σ3 ag3
  have hs4 : σ4 vs = s.val := by rw [hσ4, Function.update_of_ne hsk.ne]; exact hs3
  set σ5 := Function.update σ4 (u + 1) (Ex.eval σ4 A psrcE) with hσ5
  have g5 : Ag B σ₀ σ5 := g4.upd (by omega) _
  have hk5 : σ5 (u + 1) = e (CG.src (φ c j) s) := by rw [hσ5, Function.update_self]; exact hpsrc σ4 ag4
  have hz5 : σ5 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3,
      Function.update_of_ne (by omega)]; exact hz2
  have u5 : σ5 u = a := by
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3,
      Function.update_of_ne (by omega)]; exact u2
  have ag5 : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ5 y = σ y := by
    intro y hy
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega),
      hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have hd : Ex.eval σ5 A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.src (φ c j) s) := hD σ5 g5 ag5 u5 hk5 hz5
  set σ6 := Function.update σ5 vcd (Ex.eval σ5 A D) with hσ6
  refine ⟨σ6, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hσ6, Function.update_of_ne hscd.ne, hσ5, Function.update_of_ne (by omega)]; exact hs4
  · rw [hσ6, Function.update_of_ne hkcd.ne, hσ5, Function.update_of_ne (by omega)]; exact hk4
  · rw [hσ6, Function.update_self, hd]
  · intro y hy
    rw [hσ6, Function.update_of_ne (by omega), hσ5, Function.update_of_ne (by omega), hσ4,
      Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega),
      hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]

/-- the local expression for the code of the message of a fa node -/
def faOutLD (D : Ex) (vq vA vh vb vw vs vk vcd x1 xp : ℕ) (sE kE psrcE : Ex) : Ex :=
  faInD (u := u) D vs vk vcd sE kE psrcE (faE vq vA x1 (.var vw) (.var vs) (.var vk) (faUE vq vh vb vcd x1 xp))

/-- **`hout` for a fa node.** -/
theorem fa_houtD (D : Ex) {vq vA vh vb vw vs vk vcd x1 xp : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vs)) (hvA : vA < u ∨ (u + 2 < vA ∧ vA < vs))
    (hvh : vh < u ∨ (u + 2 < vh ∧ vh < vs)) (hvb : vb < u ∨ (u + 2 < vb ∧ vb < vs))
    (hvw : vw < u ∨ (u + 2 < vw ∧ vw < vs)) (hs : u + 10 ≤ vs) (hk : u + 10 ≤ vk) (hcd : u + 10 ≤ vcd)
    (hsk : vs < vk) (hscd : vs < vcd) (hkcd : vk < vcd) (hx1 : u + 10 ≤ x1) (hs1 : vs < x1) (hk1 : vk < x1)
    (hcd1 : vcd < x1) (hxp : xp ≠ vb) (hxp' : xp ≠ x1)
    {a b : Fin g} {c : Fin K} {j : ιc c} {s : Fin N0.A} (hM : 1 ≤ (NP N0 w c).M)
    (hka : e.symm a = CG.gt c (Gate.fa j s))
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = (NP N0 w c).A) (hh' : σ vh = (NP N0 w c).h)
    (hb' : σ vb = 2 ^ (NP N0 w c).b) (hw' : σ vw = (NP N0 w c).w)
    (hab : e.symm a ∈ paC (w := w) φ (e.symm b)) {sE kE psrcE : Ex}
    (hsE : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A sE = s.val)
    (hkE : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → ∀ kk : Fin N0.A, ∀ c' : Fin K, e.symm b = CG.gt c' (Gate.mid kk) →
      Ex.eval σ' A kE = kk.val)
    (hpsrc : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A psrcE = e (CG.src (φ c j) s))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z)
    (hD : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → τ y = σ y) → τ u = a →
      τ (u + 1) = e (CG.src (φ c j) s) →
      τ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
        (hF := edge_free_nonempty φ F ok m)).e a z → Ex.eval τ A D = ECDLP.L68.pm (w := w) φ F ok m z (CG.src (φ c j) s))
    (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Ex.eval σ A (faOutLD (u := u) D vq vA vh vb vw vs vk vcd x1 xp sE kE psrcE) =
      ec (ι := ι) (ιc := ιc) (w := w) (e.symm a) ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b)) := by
  obtain ⟨kk, hkk⟩ : ∃ kk, e.symm b = CG.gt c (Gate.mid kk) := by
    rw [hka] at hab; exact fa_child φ c j s hab
  obtain ⟨σ7, h, h1, h2, h3, h4⟩ := eval_faInD hu hC hσ D (body := faE vq vA x1 (.var vw) (.var vs) (.var vk) (faUE vq vh vb vcd x1 xp))
    hs hk hcd hsk hscd hkcd hka hkk hsE (fun σ' hσ' => hkE σ' hσ' kk c hkk) hpsrc z hz hD ha hb
  obtain ⟨x, hx1, hx2⟩ := out_fa_q (w := w) φ F ok m c j s kk (e.symm a) hka z c (e.symm b) hkk
  rw [hx2]
  unfold faOutLD
  rw [h]
  have hcd7 : σ7 vcd = (dCode (NP N0 w c).h (NP N0 w c).b x : ℕ) := by rw [h3]; exact hx1
  have hq7 : σ7 vq = 2 ^ (NP N0 w c).M + 1 := by rw [h4 _ hvq]; exact hq'
  have hA7 : σ7 vA = (NP N0 w c).A := by rw [h4 _ hvA]; exact hA'
  have hh7 : σ7 vh = (NP N0 w c).h := by rw [h4 _ hvh]; exact hh'
  have hb7 : σ7 vb = 2 ^ (NP N0 w c).b := by rw [h4 _ hvb]; exact hb'
  have hw7 : σ7 vw = (NP N0 w c).w := by rw [h4 _ hvw]; exact hw'
  have := rp_faMsgS (NP N0 w c) hM (σ := σ7) (A := A) (vq := vq) (vA := vA) (x1 := x1) hq7 (by omega) (by omega) hA7
    (e0 := .var vw) (r := .var vs) (k := .var vk)
    (u := faUE vq vh vb vcd x1 xp) (by simp only [Ex.FV]; omega) (by simp only [Ex.FV]; omega)
    (by simp only [Ex.FV]; omega) (by simp only [Ex.eval]; exact hw7) (s := s.val) (k' := kk.val)
    (by simp only [Ex.eval]; exact h1) (by simp only [Ex.eval]; exact h2) x ?_
  · exact this
  · intro i hi
    have hne : ∀ y, y ≠ x1 → Function.update σ7 x1 i y = σ7 y := fun y hy => Function.update_of_ne hy _ _
    have := rp_faUE (σ := Function.update σ7 x1 i) (A := A) (vq := vq) (vh := vh) (vb := vb) (vcd := vcd) (x1 := x1)
      (xp := xp) (x := x) (q := 2 ^ (NP N0 w c).M + 1) (by rw [hne _ (by omega)]; exact hq7)
      (by rw [hne _ (by omega)]; exact hh7) (by rw [hne _ (by omega)]; exact hb7)
      (by rw [hne _ (by omega)]; exact hcd7) hxp hxp'
    rw [Function.update_self] at this
    exact this


end node
end ECDLP.L79
end
