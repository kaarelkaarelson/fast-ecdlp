import ECDLP.L95_Real

/-!
# L95 / Bdd2: `InstBdd`, oracle bounds, `midReal_bout`, `NoRd` dispatch for the REPAIRED real instance (`instEx2`, `epsEx2`)

Numeric hypotheses: `hbn : forall s0, Ctx s0 -> BN V s0 A n`, `hn : 40 n + 40 <= V`, `N : LNum2 V (size p)`.
NO hypothesis `2^(s0 0) <= V` (L90's `hs`) and no `2^(size p) <= V` (L90's `LNum.hL2`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 Slot Cst
open ECDLP.L83 ECDLP.L90
open ECDLP.L79 (MidNum guardE midKindEC)
open ECDLP.L74 (PExB0)

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ}
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (N : LNum2 V (Nat.size p))
include hbn hn N

/-- **`InstBdd` of the repaired real instance**: discharges L84's `InstBdd V (instEx2 u hB hR)`; no `2^(sigma0 0) <= V`. -/
theorem instBdd_real2 : ECDLP.L84.InstBdd V (instEx2 (n := n) (ℓ := ℓ) (π := π) u hB hR) where
  nI σ₀ hC σ hσ := by show 24 * n + 23 ≤ V; omega
  K' σ₀ hC σ hσ := by show 18 * n + 12 ≤ V; omega
  A' σ₀ hC σ hσ := bdd_AEx2 u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) N
  h' σ₀ hC σ hσ := bdd_hEx2 u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) N
  pb σ₀ hC σ hσ := bdd_pbEx2 u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) N
  b' σ₀ hC σ hσ := bdd_bEx2 u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) N
  nc σ₀ hC σ hσ c hc :=
    bdd_ncEx (u + 22) (BN_ag hB hσ (hbn σ₀ hC)) hn (by rw [hc]; exact c.2) u rfl
  Me σ₀ hC σ hσ c hc := bdd_MEx2 u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) N

variable (hu : B ≤ u)
include hu hB hR

/-- `bε` of `midKindC_bout`, for `epsEx2` -/
theorem bddEps_real2 : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (epsEx2 u n (u + 15) (u + 43)) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  exact bdd_epsEx2 (u + 15) (u + 43) u (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (by rw [h43]; have := N.h40; omega)
    (reads_ag hB hR hC gτ) N

theorem bddN_real2 : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    Bdd V σ' A (nEx n (u + 15)) := fun σ₀ hC σ' hσ' c hc =>
  bdd_nEx (u + 15) (BN_ag hB hσ' (hbn σ₀ hC)) hn (by rw [hc]; exact c.2)

theorem bddL_real2 : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (lEx n (u + 15) (u + 43)) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  exact bdd_lEx (u + 15) (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (u + 43) (by rw [h43]; have := N.h40; omega)

theorem bddR_real2 : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (rEx n (u + 15) (u + 43)) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  exact bdd_rEx (u + 15) (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (u + 43) (by rw [h43]; have := N.h40; omega)

end

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ}
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (N : LNum2 V (Nat.size p)) (hu : B ≤ u)
include hbn hn N

/-- **the `bout` of the mid kind of the repaired real network, for every prefix** (L90's `midReal_bout`, without `2^sigma0 <= V`, `2^L <= V`) -/
theorem midReal_bout2 {m : ℕ} {ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop}
  (H : PExB0 (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu) V)
  (hN : MidNum (K := 18 * n + 12) V (NParE (Nat.size p)) (fun _ => wP (Nat.size p))) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A),
      kindOf (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a) = ECDLP.L73.GKind.mid →
      KSt (w := fun _ => wP (Nat.size p)) (layOf (sgR n ℓ π)) σ u a b
        (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a) (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm b) →
      σ (u + 7) ≤ V →
      Bdd V σ A (guardE u (midKindEC (u := u) (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43))
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43)))) ∧
        Ex.eval σ A (guardE u (midKindEC (u := u) (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43))
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43)))) + 1 ≤ V :=
  midKindC'_bout (m := m) (φ := phiR n ℓ π) (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (layOf (sgR n ℓ π)) _ H hu hN
    (hne_real (sgR n ℓ π)) (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43)) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx2 n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real2 hB hR hu)  (hl_real hB hR hu) (hr_real hB hR hu)
    (bddN_real2 hB hR hbn hn N hu) (bddEps_real2 hB hR hbn hn N hu) (bddL_real2 hB hR hbn hn N hu) (bddR_real2 hB hR hbn hn N hu)

end
end ECDLP.L95
end
