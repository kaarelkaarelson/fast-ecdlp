import ECDLP.L79_Asm
import ECDLP.L79_MidB

/-!
# L79 / Phi: bounds for the wrapped slot expression `phiWrap` (the `hphiB` of `faKind_bout` from L73's `PhiEx`)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (PExB0)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ} (H : PExB0 X V)

theorem off_ge (hA1 : 1 ≤ N0.A) (c : ℕ) : c ≤ L.off N0.A c := by
  have h : ∀ s ∈ Finset.range c, 1 ≤ L.blkN N0.A s := fun s _ => by
    unfold Lay.blkN
    have : N0.A ≤ N0.A + (N0.A + N0.A * N0.A) := by omega
    nlinarith [Nat.zero_le (L.ncN s * N0.A)]
  have := Finset.card_nsmul_le_sum (Finset.range c) (L.blkN N0.A) 1 h
  simpa [Lay.off] using this

include H in
theorem id_le_V (hA1 : 1 ≤ N0.A) (c : Fin K) : c.val ≤ V := by
  have h := (L.enum N0.A (CG.gt c (Gate.mid ⟨0, hA1⟩))).2
  have h2 := lt_of_lt_of_le h H.hgV
  rw [Lay.enum_gt, Lay.gateE_mid] at h2
  have := off_ge L hA1 c.val
  omega

include H in
/-- `hphiB` of `faKind_bout` for the wrapped expression, from the bound of `phiE` itself at the states with `u+22 = c`, `u+23 = ecc` -/
theorem hphiB_of_PhiEx (hu : B ≤ u) (hA1 : 1 ≤ N0.A) (phiE : Ex)
    (hB : ∀ σ₀, Ctx σ₀ → ∀ (τ : ℕ → ℕ), Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A phiE) :
    ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K) (j : ιc c), σ' (u + 15) = c.val →
      σ' (u + 16) = (L.ecc c j : ℕ) → Bdd V σ' A (phiWrap u phiE) := by
  intro σ₀ hC σ' hσ' c j h15 h16
  have g1 : Ag B σ₀ (Function.update σ' (u + 22) (σ' (u + 15))) := hσ'.upd (by omega) _
  have g2 := g1.upd (show B ≤ u + 23 by omega) (Ex.eval (Function.update σ' (u + 22) (σ' (u + 15))) A (.var (u + 16)))
  refine ⟨(show σ' (u + 15) ≤ V by rw [h15]; exact id_le_V L X H hA1 c), ?_, ?_⟩
  · show (Function.update σ' (u + 22) (σ' (u + 15))) (u + 16) ≤ V
    rw [Function.update_of_ne (by omega), h16]; exact ecc_le_V L X H hA1 c j
  · refine hB σ₀ hC _ g2 c j ?_ ?_
    · rw [Function.update_of_ne (by omega), Function.update_self]; exact h15
    · rw [Function.update_self]; simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h16]

end
end ECDLP.L79
end
