import ECDLP.L75_Ib3
import ECDLP.L75_IbB

/-!
# L75 / IbB: value bounds (`Bdd V`) of the `ib` gate expressions (the ib part of L69's `PExB.bout`, `PExB.bwt`)

* `bdd_ibE` (pure expression level): every value met in evaluating `ibE vq vA x1 e0 eT k u` is `≤ V`, assuming
  the ring modulus `q = σ vq` has `q*q ≤ V`, the body values are `< q` and bounded, and the exponent products are `≤ V`.
* `ib_bout`: for the full local expression `ibOutL` (node/code copies, `digE` reads) at ANY code `z ≤ V` (not only
  valid ones: `digE` ends with `% nm`, so the ring element read is `< q` for every code).
* `ib_bwt`: the weight expression `lit 1`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L68 (ibE hatE pwE sumE mulE eval_fv)

section expr
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {V : ℕ}

theorem bdd_ibE2 {vq vA x1 : ℕ} {e0 tE k u : Ex} (hvq : vq < x1) (hvA : vA < x1)
    (hq3 : 2 < σ vq) (hqq : σ vq * σ vq ≤ V) (hV2 : 2 ≤ V) (hAV : σ vA ≤ V) (hAA : σ vA * σ vA ≤ V)
    (hT : Bdd V σ A tE ∧ eval σ A tE < σ vq) (E0 K0 : ℕ) (hAAK : σ vA * σ vA * K0 ≤ V) (hexp : E0 * (σ vA * σ vA * K0) ≤ V)
    (he0 : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A e0 ∧ eval (Function.update σ x1 i) A e0 ≤ E0)
    (hk : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A k ∧ eval (Function.update σ x1 i) A k ≤ K0)
    (hu : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A u ∧ eval (Function.update σ x1 i) A u < σ vq) :
    Bdd V σ A (ibE2 vq vA x1 e0 tE k u) := by
  have hq0 : 0 < σ vq := by omega
  have hqV : σ vq ≤ V := le_trans (Nat.le_mul_of_pos_left _ hq0) hqq
  have hqq' : ∀ x y, x < σ vq → y < σ vq → x * y ≤ V := fun x y hx hy =>
    le_trans (Nat.mul_le_mul hx.le hy.le) hqq
  have h1V : 1 ≤ V := by omega
  have hbodyB : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A
      (mulE vq u (pwE vq x1 (.mul e0 (.mul (.mul (.var vA) (.var x1)) k)))) := by
    intro i hi
    have hσq : (Function.update σ x1 i) vq = σ vq := Function.update_of_ne (by omega) _ _
    have hσA : (Function.update σ x1 i) vA = σ vA := Function.update_of_ne (by omega) _ _
    obtain ⟨hb0, hv0⟩ := he0 i hi
    obtain ⟨hbk, hvk⟩ := hk i hi
    obtain ⟨hbu, hvu⟩ := hu i hi
    have hiA : i < σ vA := hi
    have hAi : σ vA * i ≤ V := le_trans (Nat.mul_le_mul_left _ hiA.le) hAA
    have hAik : σ vA * i * eval (Function.update σ x1 i) A k ≤ σ vA * σ vA * K0 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hiA.le) hvk
    have hexp' : eval (Function.update σ x1 i) A e0 *
        (σ vA * i * eval (Function.update σ x1 i) A k) ≤ V :=
      le_trans (Nat.mul_le_mul hv0 hAik) hexp
    have hBvA : Bdd V (Function.update σ x1 i) A (.var vA) := by
      show (Function.update σ x1 i) vA ≤ V; rw [hσA]; exact hAV
    have hBx : Bdd V (Function.update σ x1 i) A (.var x1) := by
      show (Function.update σ x1 i) x1 ≤ V; rw [Function.update_self]; exact le_trans hiA.le hAV
    have hex : Bdd V (Function.update σ x1 i) A (.mul e0 (.mul (.mul (.var vA) (.var x1)) k)) := by
      refine B_mul hb0 (B_mul (B_mul hBvA hBx ?_) hbk ?_) ?_
      · simp only [Ex.eval, hσA, Function.update_self]; exact hAi
      · simp only [Ex.eval, hσA, Function.update_self]
        exact le_trans hAik hAAK
      · simp only [Ex.eval, hσA, Function.update_self]; exact hexp'
    have hpw : Bdd V (Function.update σ x1 i) A (pwE vq x1 (.mul e0 (.mul (.mul (.var vA) (.var x1)) k))) :=
      B_zprod (by rw [hσq]; exact hq0) (by rw [hσq]; exact hqV) h1V hex (fun j _ => B_lit hV2)
    have hpwl : eval (Function.update σ x1 i) A (pwE vq x1 (.mul e0 (.mul (.mul (.var vA) (.var x1)) k))) <
        σ vq := by
      have := lt_zprod (σ := Function.update σ x1 i) (A := A) (vm := vq) (x := x1)
        (n := .mul e0 (.mul (.mul (.var vA) (.var x1)) k)) (b := .lit 2) (by rw [hσq]; omega)
      rw [hσq] at this; exact this
    exact B_zmul hbu hpw (by rw [hσq]; exact hqV) (hqq' _ _ hvu hpwl)
  have hhat : Bdd V σ A (hatE vq vA x1 e0 k u) :=
    B_zsum hq0 hqV (show Bdd V σ A (.var vA) from hAV) hbodyB
  have hhatl : eval σ A (hatE vq vA x1 e0 k u) < σ vq := lt_zsum hq0
  exact B_zmul hT.1 hhat hqV (hqq' _ _ hT.2 hhatl)

end expr

section node
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ}
variable (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

/-- **Value bounds for an `ib` node** (the `ib` branch of `PExB.bout`): for every code `z ≤ V` in slot `u+7` and every
child slot `u+6`, all values met in `ibOutL` are `≤ V` and the message code `+ 1 ≤ V`. -/
theorem ib_bout2 {vq vA x1 : ℕ} (hvq : u + 10 ≤ vq ∧ vq < x1) (hvA : u + 10 ≤ vA ∧ vA < x1) (hx1 : u + 10 ≤ x1)
    {a b : Fin g} {c : Fin K} {j1 : Fin N0.A} (hka : e.symm a = CG.gt c (Gate.ib j1))
    (hM : 1 ≤ (NP N0 w c).M)
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = N0.A)
    (hqq : (2 ^ (NP N0 w c).M + 1) * (2 ^ (NP N0 w c).M + 1) ≤ V) (hAV : N0.A ≤ V) (hAA : N0.A * N0.A ≤ V)
    (E0 K0 : ℕ) (hAAK : N0.A * N0.A * K0 ≤ V) (hexp : E0 * (N0.A * N0.A * K0) ≤ V)
    {e0 tE kE pmidE : Ex}
    (hB0 : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → Bdd V σ' A e0 ∧ eval σ' A e0 ≤ E0)
    (hBT : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → Bdd V σ' A tE ∧ eval σ' A tE < 2 ^ (NP N0 w c).M + 1)
    (hBk : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → Bdd V σ' A kE ∧ eval σ' A kE ≤ K0)
    (hpm : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → ∀ (i : ℕ) (hi : i < N0.A), σ' x1 = i →
      eval σ' A pmidE = e (CG.gt c (Gate.mid ⟨i, hi⟩)))
    (hBp : ∀ σ' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < x1 → σ' y = σ y) → ∀ (i : ℕ) (hi : i < N0.A), σ' x1 = i → Bdd V σ' A pmidE)
    (ha : σ (u + 5) = a) (hz0 : σ (u + 7) ≤ V) :
    Bdd V σ A (ibOutL2 X vq vA x1 e0 tE kE pmidE) ∧ eval σ A (ibOutL2 X vq vA x1 e0 tE kE pmidE) + 1 ≤ V := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have a2 : σ2 (u + 5) = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact ha
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  have hz2 : σ2 (u + 2) ≤ V := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]; exact hz0
  have low : ∀ y, u + 10 ≤ y → σ2 y = σ y := by
    intro y hy
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have hq2 : σ2 vq = 2 ^ (NP N0 w c).M + 1 := by rw [low vq hvq.1]; exact hq'
  have hA2 : σ2 vA = N0.A := by rw [low vA hvA.1]; exact hA'
  have hq3 : 2 < 2 ^ (NP N0 w c).M + 1 := by
    have : 2 ^ 1 ≤ 2 ^ (NP N0 w c).M := Nat.pow_le_pow_right (by norm_num) hM
    omega
  have hbody : ∀ i < σ2 vA, Bdd V (Function.update σ2 x1 i) A (ibBody X pmidE) ∧
      eval (Function.update σ2 x1 i) A (ibBody X pmidE) < σ2 vq := by
    intro i hi'
    have hi : i < N0.A := by rw [hA2] at hi'; exact hi'
    set σ3 := Function.update σ2 x1 i with hσ3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
    have hx3 : σ3 x1 = i := by rw [hσ3, Function.update_self]
    have hp := hpm σ3 (fun y hy1 hy2 => by rw [hσ3, Function.update_of_ne (by omega)]; exact low y hy1) i hi hx3
    set σ4 := Function.update σ3 (u + 1) (eval σ3 A pmidE) with hσ4
    have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
    have hu4 : σ4 u = a := by
      rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact u2
    have hk4 : σ4 (u + 1) = e (CG.gt c (Gate.mid ⟨i, hi⟩)) := by rw [hσ4, Function.update_self, hp]
    have hz4 : σ4 (u + 2) ≤ V := by
      rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact hz2
    refine ⟨⟨hBp σ3 (fun y hy1 hy2 => by rw [hσ3, Function.update_of_ne (by omega)]; exact low y hy1) i hi hx3, ?_⟩, ?_⟩
    · exact bdd_digE0 X H hu hC g4 (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
        (k := e (CG.gt c (Gate.mid ⟨i, hi⟩))) hu4 hk4 hz4
    · have hlt := digE_lt_nm0 X H hu hC g4 (fr := u) (tt := u + 1) (k := e (CG.gt c (Gate.mid ⟨i, hi⟩))) hk4
      rw [Equiv.symm_apply_apply, mid_nm (w := w) (φ := φ) (F := F) (ok := ok) (m := m) c ⟨i, hi⟩] at hlt
      rw [hq2]
      exact hlt
  have hBA : Bdd V σ A (.var (u + 5)) := by
    show σ (u + 5) ≤ V; rw [ha]; exact le_trans a.2.le H.hgV
  have hB7 : Bdd V σ1 A (.var (u + 7)) := by
    show σ1 (u + 7) ≤ V
    rw [hσ1, Function.update_of_ne (by omega)]; exact hz0
  have hibB := bdd_ibE2 (σ := σ2) (A := A) (V := V) (vq := vq) (vA := vA) (x1 := x1) (e0 := e0) (tE := tE) (k := kE)
    (u := ibBody X pmidE) (by omega) (by omega) (by rw [hq2]; exact hq3)
    (by rw [hq2]; exact hqq) (by have := H.hV; omega) (by rw [hA2]; exact hAV) (by rw [hA2]; exact hAA)
    (by
      have := hBT σ2 (fun y h1 h2 => low y h1)
      rw [hq2]; exact this) E0 K0 (by rw [hA2]; exact hAAK) (by rw [hA2]; exact hexp)
    (fun i hi => hB0 (Function.update σ2 x1 i) (fun y h1 h2 => by
        rw [Function.update_of_ne (by omega)]; exact low y h1))
    (fun i hi => hBk (Function.update σ2 x1 i) (fun y h1 h2 => by
        rw [Function.update_of_ne (by omega)]; exact low y h1))
    hbody
  have hlt : eval σ2 A (ibE2 vq vA x1 e0 tE kE (ibBody X pmidE)) < σ2 vq := lt_zmul (by rw [hq2]; omega)
  refine ⟨⟨hBA, hB7, hibB⟩, ?_⟩
  show eval σ2 A (ibE2 vq vA x1 e0 tE kE (ibBody X pmidE)) + 1 ≤ V
  rw [hq2] at hlt
  have : 2 ^ (NP N0 w c).M + 1 ≤ V := le_trans (Nat.le_mul_self _) hqq
  omega


end node
end ECDLP.L75
end
