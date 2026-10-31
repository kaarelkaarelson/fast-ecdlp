import FactoringAux.EngineCoarsenEx

/-!
# L64 / Rep: the expression-level representation (`NRep`) of a gate network

For a gate network `G : GNet (ZMod m) ι` and an enumeration `e : ι ≃ Fin g`, `G.toNet e` has pair
factors `Fac.numTest`, i.e. `l z q = [v a b z = q mod 2^c]`.  So an `NRep` of `G.toNet e` follows from
CODE-LEVEL expressions: size, weight, width and the two message functions.
`nrep_gnet` is generic: it removes the `Fac`/bit-string layer from every gate network.
-/
namespace ECDLP.L64
open Factoring.Aux Finset Ex

theorem bnum_bdec_mod (c q : ℕ) : bnum (bdec c q) = q % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bnum, Nat.testBit_mod_two_pow]
  by_cases h : i < c <;> simp [h, bdec]

theorem ZR_ite01 {m : ℕ} (hm : 1 < m) (p : Prop) [Decidable p] :
    ZR m (if p then 1 else 0) (if p then (1 : ZMod m) else 0) := by
  have : Fact (1 < m) := ⟨hm⟩
  by_cases h : p <;> simp [h, ZR, hm, Nat.zero_lt_of_lt hm]

variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {ι : Type}

/-- The factor expressions of a message test. -/
def msgTest (mE cE : Ex) (vq x : ℕ) : Ex := ifEq mE (.mod (.var vq) (pow2 x cE)) (.lit 1) (.lit 0)

/-- **`NRep` of a gate network from code-level expressions.** -/
theorem nrep_gnet {vm : ℕ} (v : NVars) (x : ℕ) (G : GNet (ZMod m) ι) (e : ι ≃ Fin g)
    (κ : Coding (G.toNet e)) (hm : σ₀ vm = m) (hm1 : 1 < m)
    (hW01 : ∀ i z, G.W i z = 0 ∨ G.W i z = 1)
    (szE WE cE mL mR : Ex)
    (hsz : ∀ σ, Ag B σ₀ σ → ∀ a : Fin g, σ v.a = a → Ex.eval σ A szE = κ.s a)
    (hW : ∀ σ, Ag B σ₀ σ → ∀ (a : Fin g) (z : G.S (e.symm a)), σ v.a = a → σ v.z = κ.e a z →
      Ex.eval σ A WE = if G.W (e.symm a) z = 1 then 1 else 0)
    (hc : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → σ v.a = a → σ v.b = b →
      Ex.eval σ A cE = G.c (e.symm a) (e.symm b))
    (hl : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → ∀ (z : G.S (e.symm a)), σ v.a = a → σ v.b = b →
      σ v.z = κ.e a z → Ex.eval σ A mL = G.v (e.symm a) (e.symm b) z)
    (hr : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → ∀ (z : G.S (e.symm b)), σ v.a = a → σ v.b = b →
      σ v.z = κ.e b z → Ex.eval σ A mR = G.v (e.symm b) (e.symm a) z) :
    NRep m vm B σ₀ A v ⟨szE, WE, cE, msgTest mL cE v.q x, msgTest mR cE v.q x⟩ (G.toNet e) κ where
  hm := hm
  sz := hsz
  W σ hσ a z ha hz := by
    rw [hW σ hσ a z ha hz]
    show ZR m _ (G.W (e.symm a) z)
    haveI : Fact (1 < m) := ⟨hm1⟩
    have h2 : (if G.W (e.symm a) z = 1 then (1 : ZMod m) else 0) = G.W (e.symm a) z := by
      rcases hW01 (e.symm a) z with h | h
      · rw [h]; simp
      · rw [h]; simp
    have h3 := ZR_ite01 hm1 (G.W (e.symm a) z = 1)
    rwa [h2] at h3
  c σ hσ a b hab ha hb := hc σ hσ a b hab ha hb
  l σ hσ a b hab z q ha hb hz hq := by
    have h1 := hl σ hσ a b hab z ha hb hz
    have : (Ex.eval σ A (msgTest mL cE v.q x)) =
        if G.v (e.symm a) (e.symm b) z = q % 2 ^ (G.c (e.symm a) (e.symm b)) then 1 else 0 := by
      simp only [msgTest, eval_ifEq, Ex.eval, eval_pow2, h1, hq, hc σ hσ a b hab ha hb]
    rw [this]
    have h2 : ((G.toNet e).F a b).l z (bdec _ q) =
        if G.v (e.symm a) (e.symm b) z = q % 2 ^ (G.c (e.symm a) (e.symm b)) then 1 else 0 := by
      show (if G.v (e.symm a) (e.symm b) z = bnum (bdec _ q) then (1 : ZMod m) else 0) = _
      rw [bnum_bdec_mod]
    rw [h2]
    exact ZR_ite01 hm1 _
  r σ hσ a b hab z q ha hb hz hq := by
    have h1 := hr σ hσ a b hab z ha hb hz
    have : (Ex.eval σ A (msgTest mR cE v.q x)) =
        if G.v (e.symm b) (e.symm a) z = q % 2 ^ (G.c (e.symm a) (e.symm b)) then 1 else 0 := by
      simp only [msgTest, eval_ifEq, Ex.eval, eval_pow2, h1, hq, hc σ hσ a b hab ha hb]
    rw [this]
    have h2 : ((G.toNet e).F a b).r z (bdec _ q) =
        if G.v (e.symm b) (e.symm a) z = q % 2 ^ (G.c (e.symm a) (e.symm b)) then 1 else 0 := by
      show (if G.v (e.symm b) (e.symm a) z = bnum (bdec _ q) then (1 : ZMod m) else 0) = _
      rw [bnum_bdec_mod]
    rw [h2]
    exact ZR_ite01 hm1 _

end ECDLP.L64
