import ECDLP.L79_IbC
import ECDLP.L75_Ib4

/-!
# L79 / IbCB: `ib_bout2` with a digit expression `D`
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L68 (ibE hatE pwE sumE mulE eval_fv)
open ECDLP.L75 (bdd_ibE2 ibE2 mid_nm PExB0)

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
theorem ib_bout2D (D : Ex) {vq vA x1 : ℕ} (hvq : u + 10 ≤ vq ∧ vq < x1) (hvA : u + 10 ≤ vA ∧ vA < x1) (hx1 : u + 10 ≤ x1)
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
    (hDb : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, u + 10 ≤ y → y < x1 → τ y = σ y) → ∀ (i : Fin N0.A), τ u = a →
      τ (u + 1) = e (CG.gt c (Gate.mid i)) → τ (u + 2) ≤ V → Bdd V τ A D ∧ eval τ A D < 2 ^ (NP N0 w c).M + 1)
    (ha : σ (u + 5) = a) (hz0 : σ (u + 7) ≤ V) :
    Bdd V σ A (ibOutL2D (u := u) D vq vA x1 e0 tE kE pmidE) ∧ eval σ A (ibOutL2D (u := u) D vq vA x1 e0 tE kE pmidE) + 1 ≤ V := by
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
  have hbody : ∀ i < σ2 vA, Bdd V (Function.update σ2 x1 i) A (ibBodyD (u := u) D pmidE) ∧
      eval (Function.update σ2 x1 i) A (ibBodyD (u := u) D pmidE) < σ2 vq := by
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
    have hDD := hDb σ4 g4 (fun y hy1 hy2 => by
        rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact low y hy1) ⟨i, hi⟩ hu4 hk4 hz4
    refine ⟨⟨hBp σ3 (fun y hy1 hy2 => by rw [hσ3, Function.update_of_ne (by omega)]; exact low y hy1) i hi hx3, hDD.1⟩, ?_⟩
    rw [hq2]; exact hDD.2
  have hBA : Bdd V σ A (.var (u + 5)) := by
    show σ (u + 5) ≤ V; rw [ha]; exact le_trans a.2.le H.hgV
  have hB7 : Bdd V σ1 A (.var (u + 7)) := by
    show σ1 (u + 7) ≤ V
    rw [hσ1, Function.update_of_ne (by omega)]; exact hz0
  have hibB := bdd_ibE2 (σ := σ2) (A := A) (V := V) (vq := vq) (vA := vA) (x1 := x1) (e0 := e0) (tE := tE) (k := kE)
    (u := ibBodyD (u := u) D pmidE) (by omega) (by omega) (by rw [hq2]; exact hq3)
    (by rw [hq2]; exact hqq) (by have := H.hV; omega) (by rw [hA2]; exact hAV) (by rw [hA2]; exact hAA)
    (by
      have := hBT σ2 (fun y h1 h2 => low y h1)
      rw [hq2]; exact this) E0 K0 (by rw [hA2]; exact hAAK) (by rw [hA2]; exact hexp)
    (fun i hi => hB0 (Function.update σ2 x1 i) (fun y h1 h2 => by
        rw [Function.update_of_ne (by omega)]; exact low y h1))
    (fun i hi => hBk (Function.update σ2 x1 i) (fun y h1 h2 => by
        rw [Function.update_of_ne (by omega)]; exact low y h1))
    hbody
  have hlt : eval σ2 A (ibE2 vq vA x1 e0 tE kE (ibBodyD (u := u) D pmidE)) < σ2 vq := lt_zmul (by rw [hq2]; omega)
  refine ⟨⟨hBA, hB7, hibB⟩, ?_⟩
  show eval σ2 A (ibE2 vq vA x1 e0 tE kE (ibBodyD (u := u) D pmidE)) + 1 ≤ V
  rw [hq2] at hlt
  have : 2 ^ (NP N0 w c).M + 1 ≤ V := le_trans (Nat.le_mul_self _) hqq
  omega



end node
end ECDLP.L79
end
