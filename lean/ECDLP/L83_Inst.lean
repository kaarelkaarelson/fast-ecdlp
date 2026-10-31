import ECDLP.L83_Phi
import ECDLP.L83_Nc
import ECDLP.L73_Disp1

/-!
# L83 / Inst: `InstEx` and `PhiEx` for the real network (`Slot n`, `UC sg (cnEquiv n)`)

Context hypotheses (the same as L81's `srcWtSlot`): `0 < B` and `Reads72` of the instance `(p, a, b, X, xR, yR, pi, ell, bW)` in every context.
`sg = sgOf ell pi`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 Slot Cst

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

/-- the sign requirement of the real instance -/
abbrev sgR (n : ℕ) (ℓ : ℕ) (π : List Bool) : Fin (n + 1) → Sg := fun i => sgOf ℓ π i

/-- the slot map: a used slot is itself -/
def phiR (n : ℕ) (ℓ : ℕ) (π : List Bool) : ∀ c : Fin (18 * n + 12), UC (sgR n ℓ π) (cnEquiv n) c → Slot n := fun c j => j.1

theorem cn_symm (c : Fin (18 * n + 12)) : (c : ℕ) = cnNum ((cnEquiv n).symm c) :=
  calc (c : ℕ) = ((cnEquiv n ((cnEquiv n).symm c) : Fin _) : ℕ) := by rw [Equiv.apply_symm_apply]
    _ = cnNum ((cnEquiv n).symm c) := rfl

/-- `Reads72` at an `Ag`-state -/
theorem reads_ag (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {σ₀ σ : ℕ → ℕ}
    (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW :=
  reads72_congr (hR σ₀ hC) (hσ 0 hB)

/-- **`InstEx` of the real network** -/
def instEx (u : ℕ) (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) :
    InstEx (layOf (sgR n ℓ π)) (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) B Ctx A u where
  nIE := .lit (24 * n + 23)
  KE := .lit (18 * n + 12)
  AE := AEx u
  hE := hEx u
  pbE := pbEx u
  bE := bEx u
  ncE := ncEx n u
  MeE := MEx u
  hnI _ _ _ _ := rfl
  hK _ _ _ _ := rfl
  hA σ₀ hC σ hσ := eval_AEx u (reads_ag hB hR hC hσ)
  hh σ₀ hC σ hσ := eval_hEx u (reads_ag hB hR hC hσ)
  hpb σ₀ hC σ hσ := eval_pbEx u (reads_ag hB hR hC hσ)
  hbv σ₀ hC σ hσ := eval_bEx u (reads_ag hB hR hC hσ)
  hnc σ₀ hC σ hσ c hc := eval_ncEx (reads_ag hB hR hC hσ) ((cnEquiv n).symm c) (by rw [hc]; exact cn_symm c)
  hMe σ₀ hC σ hσ c hc := eval_MEx u (reads_ag hB hR hC hσ)

/-- the semantic content of `PhiEx`, for any pair of slots `(cv, ev)` holding the identity and the rank -/
theorem phiEx_hphi (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (cv ev : ℕ) :
    ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ (c : Fin (18 * n + 12)) (j : UC (sgR n ℓ π) (cnEquiv n) c), σ cv = c →
      σ ev = (eccOf (sgR n ℓ π) c j : ℕ) → Ex.eval σ A (phiEx n cv ev) = ((layOf (sgR n ℓ π)).eι (phiR n ℓ π c j) : ℕ) := by
  intro σ₀ hC σ hσ c j hc he
  refine phiEx_spec cv ev (reads_ag hB hR hC hσ) ((cnEquiv n).symm c) (by rw [hc]; exact cn_symm c) _ he j.1 ?_
  have := lst_ecc (sgR n ℓ π) c j
  show (lst (sgR n ℓ π) c)[(eccOf (sgR n ℓ π) c j : ℕ)]? = some j.1
  rw [List.getElem?_eq_getElem (eccOf (sgR n ℓ π) c j).2]
  exact congrArg some this

/-- **`PhiEx` of the real network** (slots `u+22`, `u+23`) -/
def phiExInst (u : ℕ) (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) :
    PhiEx (layOf (sgR n ℓ π)) (phiR n ℓ π) B Ctx A u where
  phiE := phiEx n (u + 22) (u + 23)
  hphi := phiEx_hphi hB hR (u + 22) (u + 23)

end
end ECDLP.L83
end
