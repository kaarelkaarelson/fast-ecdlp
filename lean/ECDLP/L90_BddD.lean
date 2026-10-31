import ECDLP.L90_BddC
import ECDLP.L84_BddDec
import ECDLP.L84_BddNode

/-!
# L90 / BddD: `InstBdd`, the `phiE` bound, and the oracle bounds for the REAL instance

Numeric hypotheses (the only ones; V is the engine's global bound):
* `hbn : forall s0, Ctx s0 -> BN V s0 A n` (L81's bound bundle: `2 <= V`, memory cells `<= 1`, `2 sigma0 + 2 <= V`, ...), same `n` as the network,
* `hn : 40 n + 40 <= V`,
* `hs : forall s0, Ctx s0 -> 2 ^ (s0 0) <= V` (and `2 sigma0 + 4 <= V` inside `LNum`-free form `hq4`),
* `N : LNum V (Nat.size p)`: `40 <= V`, `2 L + 4 <= V`, `2^L <= V`, `2^(bP L) <= V`, `2^(2^(kP L) * wP L) <= V`  (`L = Nat.size p`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83

theorem formL_len_le {n : ℕ} (sg : Fin (n + 1) → Sg) (x : Cn n) : (formL sg x).length ≤ 6 := by
  cases x <;> simp [formL, tailT] <;> (try split) <;> simp

theorem slotList_len_le {n : ℕ} (sg : Fin (n + 1) → Sg) (x : Cn n) : (slotList sg x).length ≤ 9 := by
  cases x <;> simp [slotList] <;> (try split) <;> simp

theorem BN_ag {V : ℕ} {B : ℕ} {σ₀ σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ} (hB : 0 < B) (hσ : Ag B σ₀ σ) (H : BN V σ₀ A n) :
    BN V σ A n := by
  have e : σ 0 = σ₀ 0 := hσ 0 hB
  exact ⟨H.h2, H.hA, by rw [e]; exact H.h0, by rw [e]; exact H.hpi, by rw [e]; exact H.hl, by rw [e]; exact H.hbW,
    by rw [e]; exact H.hn, H.hq⟩

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ}
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (hs : ∀ σ₀, Ctx σ₀ → 2 ^ σ₀ 0 ≤ V)
  (N : LNum V (Nat.size p))
include hbn hn hs N

/-- **`InstBdd` of the real instance**: discharges L84's `InstBdd V (instEx u hB hR)`. -/
theorem instBdd_real : ECDLP.L84.InstBdd V (instEx (n := n) (ℓ := ℓ) (π := π) u hB hR) where
  nI σ₀ hC σ hσ := by show 24 * n + 23 ≤ V; omega
  K' σ₀ hC σ hσ := by show 18 * n + 12 ≤ V; omega
  A' σ₀ hC σ hσ := bdd_AEx u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) (by rw [hσ 0 hB]; exact hs σ₀ hC) N
  h' σ₀ hC σ hσ := bdd_hEx u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) (by rw [hσ 0 hB]; exact hs σ₀ hC) N
  pb σ₀ hC σ hσ := bdd_pbEx u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) (by rw [hσ 0 hB]; exact hs σ₀ hC) N
  b' σ₀ hC σ hσ := bdd_bEx u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) (by rw [hσ 0 hB]; exact hs σ₀ hC) N
  nc σ₀ hC σ hσ c hc :=
    bdd_ncEx (u + 22) (BN_ag hB hσ (hbn σ₀ hC)) hn (by rw [hc]; exact c.2) u rfl
  Me σ₀ hC σ hσ c hc := bdd_MEx u (BN_ag hB hσ (hbn σ₀ hC)) (reads_ag hB hR hC hσ) (by rw [hσ 0 hB]; exact hs σ₀ hC) N

/-- **the `hphiB` hypothesis of L84's `bdd_parFa` / `bdd_parEx`, for the real `phiExInst`** -/
theorem phiBdd_real (σ₀ : ℕ → ℕ) (hC : Ctx σ₀) (τ : ℕ → ℕ) (hτ : Ag B σ₀ τ) (c : Fin (18 * n + 12))
    (j : UC (sgR n ℓ π) (cnEquiv n) c) (h22 : τ (u + 22) = c.val)
    (h23 : τ (u + 23) = (eccOf (sgR n ℓ π) c j : ℕ)) :
    Bdd V τ A (phiExInst (n := n) (ℓ := ℓ) (π := π) u hB hR).phiE := by
  have hlt : (eccOf (sgR n ℓ π) c j : ℕ) < 10 := by
    have h1 := (eccOf (sgR n ℓ π) c j).2
    have h2 := slotList_len_le (sgR n ℓ π) ((cnEquiv n).symm c)
    have : (lst (sgR n ℓ π) c).length ≤ 9 := h2
    omega
  exact bdd_phiEx (u + 22) (BN_ag hB hτ (hbn σ₀ hC)) hn (by rw [h22]; exact c.2) (u + 23)
    (by rw [h23]; have := N.h40; omega)


variable (hu : B ≤ u)
include hu hB hR

/-- `bn` of `midKindC_bout`, for the real oracle `nEx` -/
theorem bddN_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    Bdd V σ' A (nEx n (u + 15)) := fun σ₀ hC σ' hσ' c hc =>
  bdd_nEx (u + 15) (BN_ag hB hσ' (hbn σ₀ hC)) hn (by rw [hc]; exact c.2)

/-- `bε` of `midKindC_bout`, for `epsEx` -/
theorem bddEps_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (epsEx n (u + 15) (u + 43) u) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  exact bdd_epsEx (u + 15) (u + 43) u (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (by rw [h43]; have := N.h40; omega)
    (reads_ag hB hR hC gτ) (by rw [gτ 0 hB]; exact hs σ₀ hC) N

theorem bddL_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (lEx n (u + 15) (u + 43)) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  exact bdd_lEx (u + 15) (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (u + 43) (by rw [h43]; have := N.h40; omega)

theorem bddR_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Bdd V (Function.update σ' (u + 43) t) A (rEx n (u + 15) (u + 43)) := by
  intro σ₀ hC σ' hσ' c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ'.upd (by omega) _
  have ht6 : t < 7 := by
    have : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
    have := formL_len_le (sgR n ℓ π) ((cnEquiv n).symm c); omega
  have h15 : Function.update σ' (u + 43) t (u + 15) = c.val := by rw [Function.update_of_ne (by omega)]; exact hc
  have h43 : Function.update σ' (u + 43) t (u + 43) = t := Function.update_self ..
  exact bdd_rEx (u + 15) (BN_ag hB gτ (hbn σ₀ hC)) hn (by rw [h15]; exact c.2) (u + 43) (by rw [h43]; have := N.h40; omega)

end
end ECDLP.L90
end
