import ECDLP.L81_Cl

/-!
# L81 / SrcSlot: `SrcWt` for the concrete ECDLP network (slots `Slot n`, bit constraints `Cl (instOf ..) bW sg xc`)

`srcWtSlot`: for the real source/check gates (`ok = okC N0 (Cl I (N0.b * 2^N0.k) (sgOf ℓ π) (xcOf ℓ π))`), an expression `srcE u (badE u n)`
of the node weight, from L63/L76's read expressions over L72's frame layout `Reads72`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L81
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L51 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68
  ECDLP.L73 ECDLP.L76

/-- `Reads72` depends on the scalars only through `σ 0` -/
theorem reads72_congr {σ σ' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (h0 : σ' 0 = σ 0) :
    ECDLP.L72.Reads72 σ' A p a b X xR yR π ℓ bW where
  hp := by rw [h0]; exact h.hp
  ha := by rw [h0]; exact h.ha
  hb := by rw [h0]; exact h.hb
  hxR := by rw [h0]; exact h.hxR
  hyR := by rw [h0]; exact h.hyR
  hOp := by rw [h0]; exact h.hOp
  hX := by rw [h0]; exact h.hX
  hlen := by rw [h0]; exact h.hlen
  hl := by rw [h0]; exact h.hl
  hbW := by rw [h0]; exact h.hbW
  hpi := h.hpi
  h3 := h.h3

section
variable {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)]
  {n : ℕ} {L : Lay (Slot n) ιc} {u : ℕ} {φ : ∀ c, ιc c → Slot n} {F : ∀ c, Form (ιc c)} {m : ℕ}

/-- **`SrcWt` of the real network.** -/
def srcWtSlot {p a b X xR yR mm : ℕ} {π : List Bool} {ℓ bW : ℕ} (hm1 : 1 < m) (hB : 0 < B) (hu : B ≤ u)
    (hb0 : 0 < N0.b) (hbW : bW = N0.b * 2 ^ N0.k) (hI : SlotIdx n (fun i => (L.eι i : ℕ)))
    (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (hX : X = Bd p mm) (hodd : p % 2 = 1)
    (Xp : PEx0 (B := B) (Ctx := Ctx) (A := A)
      (edgeNetM (w := w) φ F (okC N0 (Cl (instOf p a b xR yR mm) (N0.b * 2 ^ N0.k)
        (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i))) m) (L.enum N0.A) u) :
    SrcWt (w := w) Xp :=
  srcWt (Cl (instOf p a b xR yR mm) (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
      (fun i : Fin (n + 1) => xcOf ℓ π i)) (badE u n) hm1 hu hb0 Xp
    (by
      intro σ₀ hC σ hσ i jj v h16 h32 h33 hv1
      have h0 : σ 0 = σ₀ 0 := hσ 0 hB
      have hR'' : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW := reads72_congr (hR σ₀ hC) h0
      have := eval_badE (σ := σ) (A := A) hI u hR'' hX hodd i jj v h16 h32 h33 hv1
      rw [this, hbW])

end
end ECDLP.L81
