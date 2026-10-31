import ECDLP.L79_MidB
import ECDLP.L79_MidC

/-!
# L79 / MidCB: `mid_bout'` with a digit expression `D`

L74's `mid_bout` asks the index expression `pfaE` (which reads the loop value in slot `vI`) to be bounded for EVERY value of `vI`.
The value is always the output of the oracle `lE` / `rE`, so it is enough to ask it for values `<= V` and to know that `lE`, `rE` are `<= V` (`hlV`, `hrV`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68
open ECDLP.L74 (PExB0 Agr bdd_midIn bdd_mid_body)

section Main
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  [hF : ∀ i, Nonempty ((edgeNetM (w := w) φ F ok m).Free i)]
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)
variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

/-- **Value bounds of a mid node** (the mid part of `PExB.bout`): every value met in evaluating `midOutL` is `<= V`, and so is
the result plus one. -/
theorem mid_bout'D (D : Ex) {vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vK))
    (hvA : vA < u ∨ (u + 2 < vA ∧ vA < vK)) (hvei : vei < u ∨ (u + 2 < vei ∧ vei < vK))
    (hvw : vw < u ∨ (u + 2 < vw ∧ vw < vK))
    (hK : u + 10 ≤ vK) (hJ : u + 10 ≤ vJ) (hKJ : vK < vJ) (hK1 : vK < x1) (hJ1 : vJ < x1) (hx1 : u + 10 ≤ x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    {a b : Fin g} {c : Fin K} {k : Fin N0.A} (hM : 1 ≤ (NP N0 w c).M) (hka : e.symm a = CG.gt c (Gate.mid k))
    {Q Av wv Ei : ℕ} (hQ : Q = 2 ^ (NP N0 w c).M + 1) (hAdef : Av = N0.A)
    (hq' : σ vq = Q) (hA' : σ vA = Av) (hei' : σ vei = Ei) (hw' : σ vw = wv)
    (hQQ : Q * Q ≤ V) (hV2 : 2 ≤ V) (hAV : Av ≤ V) (hwV : wv ≤ V) (hEV : Ei ≤ V)
    (hA3 : Av * Av * Av ≤ V) (hwA : wv * (Av * Av * Av) ≤ V) (hEA : Ei * (Av * Av * Av) ≤ V)
    {kE j1E nE epsE lE rE pfaE : Ex} (dec : ℕ → ιc c)
    (hnFV : Ex.FV (· < x1) nE) (hεFV : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hlFV : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hrFV : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hpfaFV : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) pfaE)
    (hDfv : Ex.FV (fun y => y < x1 ∨ y = u + 1) D)
    (hDb : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → τ y = σ y) → ∀ (kf : Fin g) (i' : ιc c)
      (s' : Fin N0.A), e.symm kf = CG.gt c (Gate.fa i' s') → τ u = a → τ (u + 1) = kf → τ (u + 2) ≤ V →
      Bdd V τ A D ∧ Ex.eval τ A D < Q)
    (hbk : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A kE)
    (hbj : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A j1E)
    (hkA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A kE < Av)
    (hjA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A j1E < Av)
    (hnB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A nE)
    (hεB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE,
      Bdd V (Function.update σ' x2 t) A epsE ∧ Ex.eval (Function.update σ' x2 t) A epsE < Q)
    (hlB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Bdd V (Function.update σ' x2 t) A lE)
    (hrB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Bdd V (Function.update σ' x2 t) A rE)
    (hlV : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Ex.eval (Function.update σ' x2 t) A lE ≤ V)
    (hrV : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Ex.eval (Function.update σ' x2 t) A rE ≤ V)
    (hpB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ (i s : ℕ), s < Av → σ' vI = i → σ' vS = s → i ≤ V → Bdd V σ' A pfaE)
    (hpfa : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ (i s : ℕ) (hs : s < N0.A), σ' vI = i → σ' vS = s →
      Ex.eval σ' A pfaE = e (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)))
    (hz : σ (u + 7) ≤ V) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Bdd V σ A (midOutLD (u := u) D vq vA vei vw vK vJ x1 x2 x3 vI vS kE j1E nE epsE lE rE pfaE) ∧
      Ex.eval σ A (midOutLD (u := u) D vq vA vei vw vK vJ x1 x2 x3 vI vS kE j1E nE epsE lE rE pfaE) + 1 ≤ V := by
  have hQ3 : 3 ≤ Q := by
    have : 2 ^ 1 ≤ 2 ^ (NP N0 w c).M := Nat.pow_le_pow_right (by norm_num) hM
    omega
  have hQV : Q ≤ V := le_trans (Nat.le_mul_of_pos_left Q (by omega)) hQQ
  have hfvY : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) (midYD (u := u) D pfaE) := by
    refine ⟨hpfaFV, ?_⟩
    exact Ex.FV_mono (fun y hy => by rcases hy with h | h; exact Or.inl (Or.inl h); exact Or.inr h) _ hDfv
  have hall : ∀ σ4 : ℕ → ℕ, Ag B σ₀ σ4 → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → σ4 y = σ y) → σ4 (u + 5) = a → σ4 u = a →
      σ4 (u + 2) ≤ V → σ4 vK < Av → σ4 vJ < Av →
      Bdd V σ4 A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE (midYD (u := u) D pfaE)) ∧
      Ex.eval σ4 A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE (midYD (u := u) D pfaE)) < Q := by
    intro σ4 g4 h4 a4 u4 hz4 hk4 hj4
    have hq4 : σ4 vq = Q := by rw [h4 _ hvq]; exact hq'
    have hA4 : σ4 vA = Av := by rw [h4 _ hvA]; exact hA'
    have hei4 : σ4 vei = Ei := by rw [h4 _ hvei]; exact hei'
    have hw4 : σ4 vw = wv := by rw [h4 _ hvw]; exact hw'
    have hY : ∀ i s : ℕ, s < Av → i ≤ V →
        Bdd V (Function.update (Function.update σ4 vI i) vS s) A (midYD (u := u) D pfaE) ∧
        Ex.eval (Function.update (Function.update σ4 vI i) vS s) A (midYD (u := u) D pfaE) < Q := by
      intro i s hs hiV
      have gI : Ag B σ₀ (Function.update σ4 vI i) := g4.upd (by omega) _
      have gS : Ag B σ₀ (Function.update (Function.update σ4 vI i) vS s) := gI.upd (by omega) _
      set c0 := Function.update (Function.update σ4 vI i) vS s with hc0
      have hag0 : Agr u vK σ c0 :=
        Agr.upd (Agr.upd (show Agr u vK σ σ4 from h4) (x := vI) (by omega) i) (x := vS) (by omega) s
      have ha0 : c0 (u + 5) = a := by
        rw [hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a4
      have hI0 : c0 vI = i := by rw [hc0, Function.update_of_ne (by omega), Function.update_self]
      have hS0 : c0 vS = s := by rw [hc0, Function.update_self]
      have hsN : s < N0.A := hAdef ▸ hs
      have hp := hpfa c0 hag0 i s hsN hI0 hS0
      have g1 : Ag B σ₀ (Function.update c0 (u + 1) (Ex.eval c0 A pfaE)) := gS.upd (by omega) _
      have hagτ : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → (Function.update c0 (u + 1) (Ex.eval c0 A pfaE)) y = σ y := by
        intro y hy
        rw [Function.update_of_ne (by omega)]; exact hag0 y hy
      have hDD := hDb _ g1 hagτ (e (CG.gt c (Gate.fa (dec i) ⟨s, hsN⟩))) (dec i) ⟨s, hsN⟩ (by simp)
        (by rw [Function.update_of_ne (by omega), hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact u4)
        (by rw [Function.update_self, hp])
        (by rw [Function.update_of_ne (by omega), hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz4)
      exact ⟨⟨hpB c0 hag0 i s hs hI0 hS0 hiV, hDD.1⟩, hDD.2⟩
    refine bdd_mid_body (σ := σ4) hq4 hA4 hw4 hei4 hk4 hj4 hQ3 hQQ hV2 hAV hwV hEV hA3 hwA hEA (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) h12 h23 h3I hIS hnFV hεFV hlFV hrFV hfvY (hnB σ4 h4)
      (hεB σ4 h4) (hlB σ4 h4) (hrB σ4 h4) (fun t ht s hs => hY _ s hs (hlV σ4 h4 t ht)) (fun t ht s hs => hY _ s hs (hrV σ4 h4 t ht))
  obtain ⟨hB, σ4, he, g4, h4, a4, b4, u4, hz4, hk4, hj4⟩ := bdd_midIn X H hu hC hσ (body := midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw)
    (.var vK) (.var vJ) nE epsE lE rE (midYD (u := u) D pfaE)) (Ad := Av) hK hJ hKJ hbk hbj hkA hjA hz ha hb
    (fun σ4 g4 h4 a4 u4 hz4 hk4 hj4 => (hall σ4 g4 h4 a4 u4 hz4 hk4 hj4).1)
  refine ⟨hB, ?_⟩
  unfold midOutLD
  rw [he]
  have := (hall σ4 g4 h4 a4 u4 hz4 hk4 hj4).2
  have : Q ≤ Q * Q := Nat.le_mul_of_pos_left Q (by omega)
  omega


end Main
end ECDLP.L79
end
