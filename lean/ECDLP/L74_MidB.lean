import ECDLP.L74_MidOut
import ECDLP.L74_FaB

/-!
# L74 / MidB: value bounds of the mid-node expression (`PExB.bout` for a mid node)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  [hF : ∀ i, Nonempty ((edgeNetM (w := w) φ F ok m).Free i)]
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)
variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

theorem bdd_midIn {vK vJ : ℕ} {body kE j1E : Ex} {Ad : ℕ} (hK : u + 10 ≤ vK) (hJ : u + 10 ≤ vJ) (hKJ : vK < vJ)
    {a b : Fin g}
    (hbk : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A kE)
    (hbj : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A j1E)
    (hkA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A kE < Ad)
    (hjA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A j1E < Ad)
    (hz : σ (u + 7) ≤ V) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b)
    (hbody : ∀ σ4 : ℕ → ℕ, Ag B σ₀ σ4 → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → σ4 y = σ y) → σ4 (u + 5) = a → σ4 u = a →
      σ4 (u + 2) ≤ V → σ4 vK < Ad → σ4 vJ < Ad → Bdd V σ4 A body) :
    Bdd V σ A (midIn (u := u) vK vJ kE j1E body) ∧
      ∃ σ4 : ℕ → ℕ, Ex.eval σ A (midIn (u := u) vK vJ kE j1E body) = Ex.eval σ4 A body ∧ Ag B σ₀ σ4 ∧
        (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → σ4 y = σ y) ∧ σ4 (u + 5) = a ∧ σ4 (u + 6) = b ∧ σ4 u = a ∧ σ4 (u + 2) ≤ V ∧
        σ4 vK < Ad ∧ σ4 vJ < Ad := by
  have haV : σ (u + 5) ≤ V := by rw [ha]; exact le_trans a.2.le H.hgV
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have ag2 : Agr u vK σ σ2 := (Agr.refl'.upd (by omega) _).upd (by omega) _
  have hz1 : σ1 (u + 7) ≤ V := by rw [hσ1, Function.update_of_ne (by omega)]; exact hz
  have a2 : σ2 (u + 5) = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact ha
  have b2 : σ2 (u + 6) = b := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact hb
  have hz2 : σ2 (u + 2) ≤ V := by rw [hσ2, Function.update_self]; exact hz1
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  set σ3 := Function.update σ2 vK (Ex.eval σ2 A kE) with hσ3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have ag3 : Agr u vK σ σ3 := ag2.upd (by omega) _
  have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
  have b3 : σ3 (u + 6) = b := by rw [hσ3, Function.update_of_ne (by omega)]; exact b2
  have hk3 : σ3 vK < Ad := by rw [hσ3, Function.update_self]; exact hkA σ2 ag2
  set σ4 := Function.update σ3 vJ (Ex.eval σ3 A j1E) with hσ4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have h4 : ∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → σ4 y = σ y := by
    intro y hy
    rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega),
      hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have a4 : σ4 (u + 5) = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact a3
  have b4 : σ4 (u + 6) = b := by rw [hσ4, Function.update_of_ne (by omega)]; exact b3
  have u4 : σ4 u = a := by
    rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact u2
  have hz4 : σ4 (u + 2) ≤ V := by
    rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact hz2
  have hk4 : σ4 vK < Ad := by rw [hσ4, Function.update_of_ne hKJ.ne]; exact hk3
  have hj4 : σ4 vJ < Ad := by rw [hσ4, Function.update_self]; exact hjA σ3 ag3
  exact ⟨⟨B_var haV, B_var hz1, hbk σ2 ag2, hbj σ3 ag3, hbody σ4 g4 h4 a4 u4 hz4 hk4 hj4⟩, σ4, rfl, g4, h4, a4, b4, u4, hz4, hk4, hj4⟩

end node

section hat
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- the hat transform of the slot-`iv` vector: `hatYE` is bounded (and `< Q`), given the bounds of the `Y` expression -/
theorem bdd_hatYE {vq vA vw x1 x2 x3 vI vS : ℕ} {Q Av wv : ℕ} {idx yE : Ex} {σb : ℕ → ℕ}
    (hq : σ vq = Q) (hAv : σ vA = Av) (hw : σ vw = wv)
    (hQ3 : 3 ≤ Q) (hQQ : Q * Q ≤ V) (hV2 : 2 ≤ V) (hAV : Av ≤ V) (hwV : wv ≤ V)
    (hA3 : Av * Av * Av ≤ V) (hwA : wv * (Av * Av * Av) ≤ V)
    (hk : σ x1 < Av)
    (hvq : vq < x1) (hvA : vA < x1) (hvw : vw < x1) (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    (hag : ∀ y, y < x1 → σ y = σb y)
    (hidxFV : Ex.FV (fun y => y < x1 ∨ y = x2) idx) (hidx : Bdd V σ A idx)
    (hyFV : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) yE)
    (hyB : ∀ r' < Av, Bdd V (Function.update (Function.update σb vI (Ex.eval σ A idx)) vS r') A yE ∧
      Ex.eval (Function.update (Function.update σb vI (Ex.eval σ A idx)) vS r') A yE < Q) :
    Bdd V σ A (hatYE vq vA x3 vI vS (.var vw) (.var x1) idx yE) := by
  have hQV : Q ≤ V := le_trans (Nat.le_mul_of_pos_left Q (by omega)) hQQ
  have hApos : 0 < Av := by
    rcases Nat.eq_zero_or_pos Av with h0 | h0
    · rw [h0] at hk; omega
    · exact h0
  refine bdd_hatE (σ := σ) (vq := vq) (vA := vA) (x1 := x3) (v0 := vw) (vk := x1) (V := V) (by rw [hq]; omega)
    (by rw [hq]; exact hQQ) (by rw [hq]; exact hQV) hV2 ⟨by omega, by omega, by omega, by omega⟩
    (by rw [hAv]; exact hAV) (by rw [hw]; exact hwV) (by omega) ?_ ?_
  · intro i hi
    rw [hAv] at hi
    have e1 : Av * i * σ x1 ≤ Av * Av * Av := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hi.le) hk.le
    have e0 : Av * i ≤ Av * Av * Av := le_trans (Nat.mul_le_mul le_rfl hi.le)
      (Nat.le_mul_of_pos_right _ hApos)
    rw [hAv, hw]
    exact ⟨le_trans e0 hA3, le_trans e1 hA3, le_trans (Nat.mul_le_mul_left _ e1) hwA⟩
  · intro r' hr'
    rw [hAv] at hr'
    set c3 := Function.update σ x3 r' with hc3
    have hg3 : ∀ y, (y < x1 ∨ y = x2) → σ y = c3 y := fun y hy => by
      rw [hc3, Function.update_of_ne (by omega)]
    have hidx3 : Bdd V c3 A idx := (bdd_congr A idx _ σ c3 hg3 hidxFV).1 hidx
    have hidxv : Ex.eval c3 A idx = Ex.eval σ A idx := (eval_fv hidxFV (fun y hy => (hg3 y hy).symm))
    set c4 := Function.update c3 vI (Ex.eval c3 A idx) with hc4
    have hx3 : c4 x3 = r' := by
      rw [hc4, Function.update_of_ne (by omega), hc3, Function.update_self]
    set c5 := Function.update c4 vS (Ex.eval c4 A (.var x3)) with hc5
    have hc5v : Ex.eval c4 A (.var x3) = r' := hx3
    have hcan : ∀ y, (y < x1 ∨ y = vI ∨ y = vS) →
        c5 y = Function.update (Function.update σb vI (Ex.eval σ A idx)) vS r' y := by
      intro y hy
      rw [hc5, hc5v]
      by_cases hS : y = vS
      · rw [hS, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hS, Function.update_of_ne hS]
        by_cases hI : y = vI
        · rw [hI, hc4, Function.update_self, Function.update_self, hidxv]
        · rw [hc4, Function.update_of_ne hI, Function.update_of_ne hI]
          have : y < x1 := by omega
          rw [hc3, Function.update_of_ne (by omega), hag y this]
    have hyC : Bdd V c5 A yE ↔ Bdd V _ A yE := bdd_congr A yE _ _ _ hcan hyFV
    have hyE : Ex.eval c5 A yE = Ex.eval _ A yE := eval_fv hyFV hcan
    refine ⟨⟨hidx3, B_var (show c4 x3 ≤ V by rw [hx3]; omega), ?_⟩, ?_⟩
    · exact hyC.2 (hyB r' hr').1
    · show Ex.eval c5 A yE < σ vq
      rw [hyE, hq]; exact (hyB r' hr').2

end hat


section U
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- the inner sum of `midE` (over the terms `t` of the form) at a context `update σ x1 k₂` -/
theorem bdd_midU {vq vA vw x1 x2 x3 vI vS : ℕ} {Q Av wv k₂ : ℕ} {nE epsE lE rE yE : Ex}
    (hq : σ vq = Q) (hAv : σ vA = Av) (hw : σ vw = wv)
    (hQ3 : 3 ≤ Q) (hQQ : Q * Q ≤ V) (hV2 : 2 ≤ V) (hAV : Av ≤ V) (hwV : wv ≤ V)
    (hA3 : Av * Av * Av ≤ V) (hwA : wv * (Av * Av * Av) ≤ V) (hk : k₂ < Av)
    (hvq : vq < x1) (hvA : vA < x1) (hvw : vw < x1) (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    (hnFV : Ex.FV (· < x1) nE) (hεFV : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hlFV : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hrFV : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hyFV : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) yE)
    (hn : Bdd V σ A nE)
    (hε : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A epsE ∧ Ex.eval (Function.update σ x2 t) A epsE < Q)
    (hl : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A lE)
    (hr : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A rE)
    (hyl : ∀ t < Ex.eval σ A nE, ∀ s < Av,
      Bdd V (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A lE)) vS s) A yE ∧
      Ex.eval (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A lE)) vS s) A yE < Q)
    (hyr : ∀ t < Ex.eval σ A nE, ∀ s < Av,
      Bdd V (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A rE)) vS s) A yE ∧
      Ex.eval (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A rE)) vS s) A yE < Q) :
    Bdd V (Function.update σ x1 k₂) A (sumE vq x2 nE (mulE vq epsE (mulE vq
      (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE) (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE)))) ∧
    Ex.eval (Function.update σ x1 k₂) A (sumE vq x2 nE (mulE vq epsE (mulE vq
      (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE) (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE)))) < Q := by
  have hQV : Q ≤ V := le_trans (Nat.le_mul_of_pos_left Q (by omega)) hQQ
  set c1 := Function.update σ x1 k₂ with hc1
  have hg1 : ∀ y, y < x1 → σ y = c1 y := fun y hy => by rw [hc1, Function.update_of_ne (by omega)]
  have hq1 : c1 vq = Q := by rw [hc1, Function.update_of_ne (by omega)]; exact hq
  have hn1 : Bdd V c1 A nE := (bdd_congr A nE _ σ c1 hg1 hnFV).1 hn
  have hnv : Ex.eval c1 A nE = Ex.eval σ A nE := (eval_fv hnFV (fun y hy => (hg1 y hy).symm))
  have hq1' : 0 < c1 vq := by rw [hq1]; omega
  refine ⟨bdd_sumE hq1' (by rw [hq1]; exact hQV) hn1 fun t ht => ?_, by rw [← hq1] at *; exact lt_sumE hq1'⟩
  rw [hnv] at ht
  set c2 := Function.update c1 x2 t with hc2
  have hg2 : ∀ y, (y < x1 ∨ y = x2) → c2 y = Function.update σ x2 t y := fun y hy => by
    rcases hy with hy | rfl
    · rw [hc2, hc1, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    · rw [hc2, Function.update_self, Function.update_self]
  have hq2 : c2 vq = Q := by rw [hc2, Function.update_of_ne (by omega)]; exact hq1
  have hq20 : 0 < c2 vq := by rw [hq2]; omega
  have hk2 : c2 x1 < Av := by rw [hc2, Function.update_of_ne (by omega), hc1, Function.update_self]; exact hk
  have hε2 := (bdd_congr A epsE _ c2 (Function.update σ x2 t) hg2 hεFV).2 (hε t ht).1
  have hεv : Ex.eval c2 A epsE = Ex.eval (Function.update σ x2 t) A epsE := eval_fv hεFV hg2
  have hag : ∀ y, y < x1 → c2 y = σ y := fun y hy => by
    rw [hc2, hc1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hlv : Ex.eval c2 A lE = Ex.eval (Function.update σ x2 t) A lE := eval_fv hlFV hg2
  have hrv : Ex.eval c2 A rE = Ex.eval (Function.update σ x2 t) A rE := eval_fv hrFV hg2
  have hatL : Bdd V c2 A (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE) := by
    refine bdd_hatYE (σ := c2) (σb := σ) (idx := lE) (yE := yE) (x2 := x2) (by rw [hq2]) (by rw [hc2, Function.update_of_ne (by omega), hc1, Function.update_of_ne (by omega)]; exact hAv)
      (by rw [hc2, Function.update_of_ne (by omega), hc1, Function.update_of_ne (by omega)]; exact hw)
      hQ3 hQQ hV2 hAV hwV hA3 hwA hk2 hvq hvA hvw h12 h23 h3I hIS (fun y hy => hag y hy) hlFV
      ((bdd_congr A lE _ c2 (Function.update σ x2 t) hg2 hlFV).2 (hl t ht)) hyFV ?_
    intro r' hr'
    rw [hlv]; exact hyl t ht r' hr'
  have hatR : Bdd V c2 A (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE) := by
    refine bdd_hatYE (σ := c2) (σb := σ) (idx := rE) (yE := yE) (x2 := x2) (by rw [hq2]) (by rw [hc2, Function.update_of_ne (by omega), hc1, Function.update_of_ne (by omega)]; exact hAv)
      (by rw [hc2, Function.update_of_ne (by omega), hc1, Function.update_of_ne (by omega)]; exact hw)
      hQ3 hQQ hV2 hAV hwV hA3 hwA hk2 hvq hvA hvw h12 h23 h3I hIS (fun y hy => hag y hy) hrFV
      ((bdd_congr A rE _ c2 (Function.update σ x2 t) hg2 hrFV).2 (hr t ht)) hyFV ?_
    intro r' hr'
    rw [hrv]; exact hyr t ht r' hr'
  have hltL : Ex.eval c2 A (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE) < c2 vq := lt_hatE hq20
  have hltR : Ex.eval c2 A (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE) < c2 vq := lt_hatE hq20
  rw [hq2] at hltL hltR
  have hmm := bdd_mulE hatL hatR (by rw [hq2]; exact hQV) (mul_lt_le hltL hltR hQQ)
  have hltm : Ex.eval c2 A (mulE vq (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE)
      (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE)) < Q := by
    have := lt_mulE (σ := c2) (A := A) (vq := vq) (a := hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE)
      (b := hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE) hq20
    rwa [hq2] at this
  refine bdd_mulE hε2 hmm (by rw [hq2]; exact hQV) (mul_lt_le ?_ hltm hQQ)
  rw [hεv]; exact (hε t ht).2

end U


section body
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- the body of a mid node: `midE`, in a context where the slots hold the stated numbers -/
theorem bdd_mid_body {vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ} {Q Av wv Ei : ℕ} {nE epsE lE rE yE : Ex}
    (hq : σ vq = Q) (hAv : σ vA = Av) (hw : σ vw = wv) (hei : σ vei = Ei)
    (hKA : σ vK < Av) (hJA : σ vJ < Av)
    (hQ3 : 3 ≤ Q) (hQQ : Q * Q ≤ V) (hV2 : 2 ≤ V) (hAV : Av ≤ V) (hwV : wv ≤ V) (hEV : Ei ≤ V)
    (hA3 : Av * Av * Av ≤ V) (hwA : wv * (Av * Av * Av) ≤ V) (hEA : Ei * (Av * Av * Av) ≤ V)
    (hvq : vq < x1) (hvA : vA < x1) (hvw : vw < x1) (hvei : vei < x1) (hvK : vK < x1) (hvJ : vJ < x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS)
    (hnFV : Ex.FV (· < x1) nE) (hεFV : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hlFV : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hrFV : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hyFV : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) yE)
    (hn : Bdd V σ A nE)
    (hε : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A epsE ∧ Ex.eval (Function.update σ x2 t) A epsE < Q)
    (hl : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A lE)
    (hr : ∀ t < Ex.eval σ A nE, Bdd V (Function.update σ x2 t) A rE)
    (hyl : ∀ t < Ex.eval σ A nE, ∀ s < Av,
      Bdd V (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A lE)) vS s) A yE ∧
      Ex.eval (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A lE)) vS s) A yE < Q)
    (hyr : ∀ t < Ex.eval σ A nE, ∀ s < Av,
      Bdd V (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A rE)) vS s) A yE ∧
      Ex.eval (Function.update (Function.update σ vI (Ex.eval (Function.update σ x2 t) A rE)) vS s) A yE < Q) :
    Bdd V σ A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE yE) ∧
      Ex.eval σ A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE yE) < Q := by
  have hQV : Q ≤ V := le_trans (Nat.le_mul_of_pos_left Q (by omega)) hQQ
  have hApos : 0 < Av := by omega
  have hKJ : σ vK * σ vJ ≤ Av * Av * Av := le_trans (Nat.mul_le_mul hKA.le hJA.le)
    (Nat.le_mul_of_pos_right _ hApos)
  have hAA : Av * Av ≤ Av * Av * Av := Nat.le_mul_of_pos_right _ hApos
  refine ⟨?_, ?_⟩
  · refine bdd_faE (σ := σ) (vq := vq) (vA := vA) (x1 := x1) (v0 := vei) (vr := vK) (vk := vJ) (V := V)
      (by rw [hq]; omega) (by rw [hq]; exact hQQ) (by rw [hq]; exact hQV) hV2
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by rw [hAv]; exact hAV) (by rw [hei]; exact hEV)
      (by omega) (by omega) (le_trans hKJ hA3) (by rw [hei]; exact le_trans (Nat.mul_le_mul_left _ hKJ) hEA) ?_ ?_
    · intro i hi
      rw [hAv] at hi
      have e1 : Av * i * σ vJ ≤ Av * Av * Av := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hi.le) hJA.le
      have e0 : Av * i ≤ Av * Av * Av := le_trans (Nat.mul_le_mul le_rfl hi.le) hAA
      rw [hAv, hei]
      exact ⟨le_trans e0 hA3, le_trans e1 hA3, le_trans (Nat.mul_le_mul_left _ e1) hEA⟩
    · intro k₂ hk₂
      rw [hAv] at hk₂
      have h := bdd_midU (σ := σ) hq hAv hw hQ3 hQQ hV2 hAV hwV hA3 hwA hk₂ hvq hvA hvw h12 h23 h3I hIS hnFV hεFV hlFV
        hrFV hyFV hn hε hl hr hyl hyr
      exact ⟨h.1, by rw [hq]; exact h.2⟩
  · have hq0 : 0 < σ vq := by rw [hq]; omega
    have := lt_faE (σ := σ) (A := A) (vq := vq) (vA := vA) (x1 := x1) (v0 := vei) (vr := vK) (vk := vJ)
      (u := sumE vq x2 nE (mulE vq epsE (mulE vq (hatYE vq vA x3 vI vS (.var vw) (.var x1) lE yE)
        (hatYE vq vA x3 vI vS (.var vw) (.var x1) rE yE)))) hq0
    rwa [hq] at this

end body


section Y
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  [hF : ∀ i, Nonempty ((edgeNetM (w := w) φ F ok m).Free i)]
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

theorem card_msg_fa (c : Fin K) (i : ιc c) (s : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.fa i s))) = 2 ^ (NP N0 w c).M + 1 :=
  ZMod.card (2 ^ (NP N0 w c).M + 1)

variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

/-- the `Y` expression of a mid node: bounded, and `< Q = 2^M+1` -/
theorem bdd_midY {a : Fin g} {c : Fin K} {pfaE : Ex} {Q : ℕ} (hQ : Q = 2 ^ (NP N0 w c).M + 1)
    (hbp : Bdd V σ A pfaE)
    (hpg : ∃ (kf : Fin g) (i' : ιc c) (s' : Fin N0.A), Ex.eval σ A pfaE = kf ∧ e.symm kf = CG.gt c (Gate.fa i' s'))
    (hua : σ u = a) (hz : σ (u + 2) ≤ V) :
    Bdd V σ A (midY X pfaE) ∧ Ex.eval σ A (midY X pfaE) < Q := by
  obtain ⟨kf, i', s', hkf, hk⟩ := hpg
  have g1 : Ag B σ₀ (Function.update σ (u + 1) (Ex.eval σ A pfaE)) := hσ.upd (by omega) _
  have h1 : (Function.update σ (u + 1) (Ex.eval σ A pfaE)) (u + 1) = kf := by
    rw [Function.update_self]; exact hkf
  have h2 : (Function.update σ (u + 1) (Ex.eval σ A pfaE)) u = a := by
    rw [Function.update_of_ne (by omega)]; exact hua
  have h3 : (Function.update σ (u + 1) (Ex.eval σ A pfaE)) (u + 2) ≤ V := by
    rw [Function.update_of_ne (by omega)]; exact hz
  refine ⟨⟨hbp, bdd_digE X H hu hC g1 (fr := u) (tt := u + 1) (by omega) (by omega) h2 h1 h3⟩, ?_⟩
  have := digE_lt_nm X H hu hC g1 (fr := u) (tt := u + 1) (by omega) (by omega) h2 h1
  rw [hk, card_msg_fa (w := w) (φ := φ) (F := F) (ok := ok) (m := m) c i' s'] at this
  rw [hQ]; exact this

end Y


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
theorem mid_bout {vq vA vei vw vK vJ x1 x2 x3 vI vS : ℕ} (hvq : vq < u ∨ (u + 2 < vq ∧ vq < vK))
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
    (hXnf : Ex.FV (· < u + 10) X.nfE) (hXnm : Ex.FV (· < u + 10) X.nmE) (hXpar : Ex.FV (· < u + 10) X.parE)
    (hbk : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A kE)
    (hbj : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A j1E)
    (hkA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A kE < Av)
    (hjA : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Ex.eval σ' A j1E < Av)
    (hnB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → Bdd V σ' A nE)
    (hεB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE,
      Bdd V (Function.update σ' x2 t) A epsE ∧ Ex.eval (Function.update σ' x2 t) A epsE < Q)
    (hlB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Bdd V (Function.update σ' x2 t) A lE)
    (hrB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ t < Ex.eval σ' A nE, Bdd V (Function.update σ' x2 t) A rE)
    (hpB : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ (i s : ℕ), s < Av → σ' vI = i → σ' vS = s → Bdd V σ' A pfaE)
    (hpfa : ∀ σ' : ℕ → ℕ, Agr u vK σ σ' → ∀ (i s : ℕ) (hs : s < N0.A), σ' vI = i → σ' vS = s →
      Ex.eval σ' A pfaE = e (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)))
    (hz : σ (u + 7) ≤ V) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Bdd V σ A (midOutL X vq vA vei vw vK vJ x1 x2 x3 vI vS kE j1E nE epsE lE rE pfaE) ∧
      Ex.eval σ A (midOutL X vq vA vei vw vK vJ x1 x2 x3 vI vS kE j1E nE epsE lE rE pfaE) + 1 ≤ V := by
  have hQ3 : 3 ≤ Q := by
    have : 2 ^ 1 ≤ 2 ^ (NP N0 w c).M := Nat.pow_le_pow_right (by norm_num) hM
    omega
  have hQV : Q ≤ V := le_trans (Nat.le_mul_of_pos_left Q (by omega)) hQQ
  have hfvY : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) (midY X pfaE) := by
    refine ⟨hpfaFV, ?_⟩
    have := fv_digE X (t := x1) hx1 (Ex.FV_mono (fun y hy => by omega) _ hXnf)
      (Ex.FV_mono (fun y hy => by omega) _ hXnm) (Ex.FV_mono (fun y hy => by omega) _ hXpar)
      (fr := u) (tt := u + 1) (by omega) (by omega)
    exact Ex.FV_mono (fun y hy => Or.inl (Or.inl hy)) _ this
  have hall : ∀ σ4 : ℕ → ℕ, Ag B σ₀ σ4 → (∀ y, (y < u ∨ (u + 2 < y ∧ y < vK)) → σ4 y = σ y) → σ4 (u + 5) = a → σ4 u = a →
      σ4 (u + 2) ≤ V → σ4 vK < Av → σ4 vJ < Av →
      Bdd V σ4 A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE (midY X pfaE)) ∧
      Ex.eval σ4 A (midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw) (.var vK) (.var vJ) nE epsE lE rE (midY X pfaE)) < Q := by
    intro σ4 g4 h4 a4 u4 hz4 hk4 hj4
    have hq4 : σ4 vq = Q := by rw [h4 _ hvq]; exact hq'
    have hA4 : σ4 vA = Av := by rw [h4 _ hvA]; exact hA'
    have hei4 : σ4 vei = Ei := by rw [h4 _ hvei]; exact hei'
    have hw4 : σ4 vw = wv := by rw [h4 _ hvw]; exact hw'
    have hY : ∀ i s : ℕ, s < Av →
        Bdd V (Function.update (Function.update σ4 vI i) vS s) A (midY X pfaE) ∧
        Ex.eval (Function.update (Function.update σ4 vI i) vS s) A (midY X pfaE) < Q := by
      intro i s hs
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
      refine bdd_midY X H hu hC gS (a := a) hQ (hpB c0 hag0 i s hs hI0 hS0)
        ⟨e (CG.gt c (Gate.fa (dec i) ⟨s, hsN⟩)), dec i, ⟨s, hsN⟩, hpfa c0 hag0 i s hsN hI0 hS0, by simp⟩ ?_ ?_
      · rw [hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact u4
      · rw [hc0, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz4
    refine bdd_mid_body (σ := σ4) hq4 hA4 hw4 hei4 hk4 hj4 hQ3 hQQ hV2 hAV hwV hEV hA3 hwA hEA (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) h12 h23 h3I hIS hnFV hεFV hlFV hrFV hfvY (hnB σ4 h4)
      (hεB σ4 h4) (hlB σ4 h4) (hrB σ4 h4) (fun t ht s hs => hY _ s hs) (fun t ht s hs => hY _ s hs)
  obtain ⟨hB, σ4, he, g4, h4, a4, b4, u4, hz4, hk4, hj4⟩ := bdd_midIn X H hu hC hσ (body := midE vq vA x1 x2 x3 vI vS (.var vei) (.var vw)
    (.var vK) (.var vJ) nE epsE lE rE (midY X pfaE)) (Ad := Av) hK hJ hKJ hbk hbj hkA hjA hz ha hb
    (fun σ4 g4 h4 a4 u4 hz4 hk4 hj4 => (hall σ4 g4 h4 a4 u4 hz4 hk4 hj4).1)
  refine ⟨hB, ?_⟩
  unfold midOutL
  rw [he]
  have := (hall σ4 g4 h4 a4 u4 hz4 hk4 hj4).2
  have : Q ≤ Q * Q := Nat.le_mul_of_pos_left Q (by omega)
  omega

end Main

end ECDLP.L74
end
