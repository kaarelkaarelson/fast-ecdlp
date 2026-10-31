import ECDLP.L79_FaC
import ECDLP.L74_FaB

/-!
# L79 / FaCB: value bounds of the fa node expression with a digit expression `D` (`bdd_faInD`, `fa_boutD`)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68
open ECDLP.L74 (Agr PExB0 bdd_fa_body lt_faE faUE bdd_faE)

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  [hF : ∀ i, Nonempty ((edgeNetM (w := w) φ F ok m).Free i)]
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

/-- the scratch bindings of a fa node are bounded, and the body runs in a context with the stated values -/
theorem bdd_faInD (D : Ex) {vs vk vcd : ℕ} {body sE kE psrcE : Ex} {Ad : ℕ} (hs : u + 10 ≤ vs) (hk : u + 10 ≤ vk)
    (hcd : u + 10 ≤ vcd) (hsk : vs < vk) (hscd : vs < vcd) (hkcd : vk < vcd) {a b : Fin g}
    (hbs : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A sE)
    (hbk : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A kE)
    (hbp : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A psrcE)
    (hsA : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A sE < Ad)
    (hkA : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A kE < Ad)
    (hpg : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → ∃ kf : Fin g, Ex.eval σ' A psrcE = kf)
    (hz : σ (u + 7) ≤ V) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b)
    (hDb : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → τ y = σ y) → ∀ kf : Fin g, τ u = a →
      τ (u + 1) = kf → τ (u + 2) ≤ V → Bdd V τ A D)
    (hbody : ∀ σ7 : ℕ → ℕ, (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ7 y = σ y) → σ7 vs < Ad → σ7 vk < Ad → σ7 vcd ≤ V →
      Bdd V σ7 A body) :
    Bdd V σ A (faInD (u := u) D vs vk vcd sE kE psrcE body) ∧
      ∃ σ7 : ℕ → ℕ, Ex.eval σ A (faInD (u := u) D vs vk vcd sE kE psrcE body) = Ex.eval σ7 A body ∧
        (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ7 y = σ y) := by
  have haV : σ (u + 5) ≤ V := by rw [ha]; exact le_trans a.2.le H.hgV
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have ag2 : Agr u vs σ σ2 := (Agr.refl'.upd (by omega) _).upd (by omega) _
  have hz1 : σ1 (u + 7) ≤ V := by rw [hσ1, Function.update_of_ne (by omega)]; exact hz
  have a2 : σ2 (u + 5) = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact ha
  have b2 : σ2 (u + 6) = b := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact hb
  have hz2 : σ2 (u + 2) ≤ V := by
    rw [hσ2, Function.update_self]; exact hz1
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  set σ3 := Function.update σ2 vs (Ex.eval σ2 A sE) with hσ3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have ag3 : Agr u vs σ σ3 := ag2.upd (by omega) _
  have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
  have b3 : σ3 (u + 6) = b := by rw [hσ3, Function.update_of_ne (by omega)]; exact b2
  have hs3 : σ3 vs < Ad := by rw [hσ3, Function.update_self]; exact hsA σ2 ag2
  set σ4 := Function.update σ3 vk (Ex.eval σ3 A kE) with hσ4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have ag4 : Agr u vs σ σ4 := ag3.upd (by omega) _
  have a4 : σ4 (u + 5) = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact a3
  have hk4 : σ4 vk < Ad := by rw [hσ4, Function.update_self]; exact hkA σ3 ag3
  have hs4 : σ4 vs < Ad := by rw [hσ4, Function.update_of_ne hsk.ne]; exact hs3
  obtain ⟨kf, hkf⟩ := hpg σ4 ag4
  set σ5 := Function.update σ4 (u + 1) (Ex.eval σ4 A psrcE) with hσ5
  have g5 : Ag B σ₀ σ5 := g4.upd (by omega) _
  have hk5 : σ5 (u + 1) = kf := by rw [hσ5, Function.update_self]; exact hkf
  have hz5 : σ5 (u + 2) ≤ V := by
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3,
      Function.update_of_ne (by omega)]; exact hz2
  have u5 : σ5 u = a := by
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3,
      Function.update_of_ne (by omega)]; exact u2
  have ag5 : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ5 y = σ y := by
    intro y hy
    rw [hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega),
      hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have hd : Bdd V σ5 A D := hDb σ5 g5 ag5 kf u5 hk5 hz5
  have hdV := le_of_B hd
  set σ6 := Function.update σ5 vcd (Ex.eval σ5 A D) with hσ6
  have h6 : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ6 y = σ y := by
    intro y hy
    rw [hσ6, Function.update_of_ne (by omega), hσ5, Function.update_of_ne (by omega), hσ4,
      Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega),
      hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  refine ⟨⟨B_var haV, B_var hz1, hbs σ2 ag2, hbk σ3 ag3, hbp σ4 ag4, hd, hbody σ6 h6 ?_ ?_ ?_⟩, σ6, rfl, h6⟩
  · rw [hσ6, Function.update_of_ne hscd.ne, hσ5, Function.update_of_ne (by omega)]; exact hs4
  · rw [hσ6, Function.update_of_ne hkcd.ne, hσ5, Function.update_of_ne (by omega)]; exact hk4
  · rw [hσ6, Function.update_self]; exact hdV


/-- **Value bounds of a fa node** (the fa part of `PExB.bout`): every value met in evaluating `faOutL` is `<= V`, and so is
the result plus one.  Hypotheses: the parameter slots hold `Q = 2^M+1, A, h, 2^b, w`, the numeric inequalities
(`Q*Q <= V`, exponents `w*A^3 <= V`, `(2^b)^h <= V`) and the bounds of the three index oracles. -/
theorem fa_boutD (D : Ex) {vq vA vh vb vw vs vk vcd x1 xp : ℕ} {Q Av wv hv Bv : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vs))
    (hvA : vA < u ∨ (u + 2 < vA ∧ vA < vs)) (hvh : vh < u ∨ (u + 2 < vh ∧ vh < vs))
    (hvb : vb < u ∨ (u + 2 < vb ∧ vb < vs)) (hvw : vw < u ∨ (u + 2 < vw ∧ vw < vs)) (hs : u + 10 ≤ vs)
    (hk : u + 10 ≤ vk) (hcd : u + 10 ≤ vcd) (hsk : vs < vk) (hscd : vs < vcd) (hkcd : vk < vcd) (hx1 : u + 10 ≤ x1) (hs1 : vs < x1) (hk1 : vk < x1)
    (hcd1 : vcd < x1) (hxp : x1 < xp)
    (hq' : σ vq = Q) (hA' : σ vA = Av) (hh' : σ vh = hv) (hb' : σ vb = Bv) (hw' : σ vw = wv)
    (hQ3 : 3 ≤ Q) (hQQ : Q * Q ≤ V) (hV2 : 2 ≤ V) (hAV : Av ≤ V) (hA3 : Av * Av * Av ≤ V)
    (hwV : wv ≤ V) (hwA : wv * (Av * Av * Av) ≤ V) (hhV : hv ≤ V) (hBV : Bv ^ hv ≤ V) (hB1 : 1 ≤ Bv)
    {a b : Fin g} {sE kE psrcE : Ex}
    (hbs : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A sE)
    (hbk : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A kE)
    (hbp : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Bdd V σ' A psrcE)
    (hsA : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A sE < Av)
    (hkA : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → Ex.eval σ' A kE < Av)
    (hpg : ∀ σ' : ℕ → ℕ, Agr u vs σ σ' → ∃ kf : Fin g, Ex.eval σ' A psrcE = kf)
    (hDb : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → τ y = σ y) → ∀ kf : Fin g, τ u = a →
      τ (u + 1) = kf → τ (u + 2) ≤ V → Bdd V τ A D)
    (hz : σ (u + 7) ≤ V) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Bdd V σ A (faOutLD (u := u) D vq vA vh vb vw vs vk vcd x1 xp sE kE psrcE) ∧
      Ex.eval σ A (faOutLD (u := u) D vq vA vh vb vw vs vk vcd x1 xp sE kE psrcE) + 1 ≤ V := by
  obtain ⟨hB, σ7, he, h7⟩ := bdd_faInD X H hu hC hσ D (body := faE vq vA x1 (.var vw) (.var vs) (.var vk)
    (faUE vq vh vb vcd x1 xp)) (Ad := Av) hs hk hcd hsk hscd hkcd hbs hbk hbp hsA hkA hpg hz ha hb hDb
    (fun σ7 h7 hs7 hk7 hcd7 => bdd_fa_body (σ := σ7) (by rw [h7 _ hvq]; exact hq') (by rw [h7 _ hvA]; exact hA')
      (by rw [h7 _ hvh]; exact hh') (by rw [h7 _ hvb]; exact hb') (by rw [h7 _ hvw]; exact hw') hs7 hk7 hcd7 hQ3 hQQ hV2
      hAV hA3 hwV hwA hhV hBV hB1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hxp)
  refine ⟨hB, ?_⟩
  unfold faOutLD
  rw [he]
  have hq7 : σ7 vq = Q := by rw [h7 _ hvq]; exact hq'
  have := lt_faE (σ := σ7) (A := A) (vq := vq) (vA := vA) (x1 := x1) (v0 := vw) (vr := vs) (vk := vk)
    (u := faUE vq vh vb vcd x1 xp) (by omega)
  rw [hq7] at this
  have : Q ≤ Q * Q := Nat.le_mul_of_pos_left Q (by omega)
  omega


end node
end ECDLP.L79
end
