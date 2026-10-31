import ECDLP.L90_MidB
import ECDLP.L90_BddD
import ECDLP.L90_Real

/-!
# L90 / MidReal: `midKindC'_bout` instantiated for the REAL network (no `hne`)

Hypotheses: `H : PExB0 (pex0 ..) V` (L84's `pexB0_L74`), `hN : MidNum V (NParE (size p)) (fun _ => wP (size p))` (numeric), and the Bdd numerics of `L90_BddD`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 Slot Cst
open ECDLP.L83
open ECDLP.L79 (MidNum guardE midKindEC)
open ECDLP.L74 (PExB0)

section
/-- **the `bout` of the mid kind of the real network, for every prefix** -/
theorem midReal_bout {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ} (hu : B ≤ u)
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (hs : ∀ σ₀, Ctx σ₀ → 2 ^ σ₀ 0 ≤ V)
  (N : LNum V (Nat.size p))
  {m : ℕ} {ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop}
  (H : PExB0 (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu) V)
  (hN : MidNum (K := 18 * n + 12) V (NParE (Nat.size p)) (fun _ => wP (Nat.size p))) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A),
      kindOf (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a) = ECDLP.L73.GKind.mid →
      KSt (w := fun _ => wP (Nat.size p)) (layOf (sgR n ℓ π)) σ u a b
        (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a) (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm b) →
      σ (u + 7) ≤ V →
      Bdd V σ A (guardE u (midKindEC (u := u) (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u)
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43)))) ∧
        Ex.eval σ A (guardE u (midKindEC (u := u) (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u)
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43)))) + 1 ≤ V :=
  midKindC'_bout (m := m) (φ := phiR n ℓ π) (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (layOf (sgR n ℓ π)) _ H hu hN
    (hne_real (sgR n ℓ π)) (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)
    (bddN_real hB hR hbn hn hs N hu) (bddEps_real hB hR hbn hn hs N hu) (bddL_real hB hR hbn hn hs N hu) (bddR_real hB hR hbn hn hs N hu)

end
end ECDLP.L90
end
