import ECDLP.L89_Dsp

/-!
# L89 / Wt: dispatch-level value bound of the node weight `wtEx` (`PExB.bwt`)

`bdd_wtEx`: for every node `a` (slot `u+4`) and state with `u+7 <= V`, L73's `wtEx` is bounded by `V`, from the bound of the source
weight expression (state-level hypothesis in the form of `SrcWt.hsrc`'s premises; for the real network this is L81's `bdd_srcSlot`)
and the bound of the car weight expression `carWX` (hypothesis).  fa, mid, ib have weight `lit 1`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L89
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L84

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ}

theorem bdd_wtEx (hu : B ≤ u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V) (hAA : N0.A * N0.A ≤ V)
    (Sw : SrcWt (w := w) X)
    (hsrc : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (i : ι) (s : Fin N0.A),
      (L.enum N0.A).symm a = CG.src i s → σ (u + 4) = a → σ (u + 7) ≤ V →
      σ (u + 10) = 2 ^ N0.b → σ (u + 12) = N0.A → σ (u + 13) = N0.h → σ (u + 14) = N0.b →
      σ (u + 16) = L.eι i → σ (u + 17) = s → Bdd V σ A Sw.srcE)
    (hcar : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 4) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 28) = N0.A * N0.A → σ (u + 7) ≤ V → Bdd V σ A (carWX I X)) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a : Fin (L.gTot N0.A), σ (u + 4) = a → σ (u + 7) ≤ V →
      Bdd V σ A (wtEx I X Sw) := by
  intro σ₀ hC σ hσ a ha hz
  unfold wtEx
  refine bdd_node4 I IB DN h8 hu hC hσ a ha (fun σ' hD => ?_)
  obtain ⟨g', agr, k21, j16, s17, hp, hg⟩ := hD
  have hz' : σ' (u + 7) ≤ V := by rw [agr _ (Or.inl (by omega))]; exact hz
  have a' : σ' (u + 4) = a := by rw [agr _ (Or.inl (by omega))]; exact ha
  have k4 := kc_le_four ((L.enum N0.A).symm a)
  obtain ⟨q, hq⟩ : ∃ q, (L.enum N0.A).symm a = q := ⟨_, rfl⟩
  rw [hq] at k21 j16 s17 hp
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    simp only [coordOf] at j16 s17
    have hS := hsrc σ₀ hC σ' g' a i s' hq a' hz' hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 j16 s17
    simp only [wtChain, Bdd, Ex.eval, k21]
    generalize Bdd V σ' A Sw.srcE = P at hS ⊢
    simp
    exact ⟨by omega, hS⟩
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g' with
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      set σ3 := Function.update σ' (u + 28) (σ' (u + 12) * σ' (u + 12)) with h3
      have g3 : Ag B σ₀ σ3 := g'.upd (by omega) _
      have e3 : ∀ y, y ≠ u + 28 → σ3 y = σ' y := fun y hy => by simp [h3, Function.update_apply, hy]
      have hB := hcar σ₀ hC σ3 g3 a c j hka (by rw [e3 _ (by omega)]; exact a')
        (by rw [e3 _ (by omega)]; exact p10) (by rw [e3 _ (by omega)]; exact p11)
        (by simp [h3, p12]) (by rw [e3 _ (by omega)]; exact hz')
      simp only [wtChain, Bdd, Ex.eval, k1]
      generalize Bdd V σ3 A (carWX I X) = P at hB ⊢
      simp [h3] at hB ⊢
      exact ⟨by omega, by omega, by omega, ⟨by rw [p12]; exact le_trans (Nat.le_mul_self _) hAA, by rw [p12]; exact hAA⟩, hB⟩
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      simp only [wtChain, Bdd, Ex.eval, k1]; simp; omega
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      simp only [wtChain, Bdd, Ex.eval, k1]; simp; omega
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      simp only [wtChain, Bdd, Ex.eval, k1]; simp; omega

end
end ECDLP.L89
end
