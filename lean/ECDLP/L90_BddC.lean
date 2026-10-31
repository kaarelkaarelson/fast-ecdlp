import ECDLP.L90_BddB

/-!
# L90 / BddC: value bounds of `ncEx, nEx, lEx, rEx, negEx, epsEx, phiEx`

State hypotheses: `H : BN V sigma A n` (L81), `40 n + 40 <= V` (`hn`), the identity number `sigma cv = c < 18 n + 12`
(and for the term oracles `sigma tv <= 9`), `Reads72` + `LNum` for `epsEx` (it contains `2^M`).
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

section
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ} (cv : ℕ)

theorem bdd_tabLits {e : Ex} (he : Bdd V σ A e) (l : List ℕ) (hV : 12 ≤ V) (hl : l.length ≤ 10) (hx : ∀ x ∈ l, x ≤ V) :
    Bdd V σ A (tabX e 0 (lits l)) :=
  bdd_tabX he _ 0 (by simp [lits]; omega) (bdd_lits l hx)

theorem bdd_sgcEx (H : BN V σ A n) (hn : 40 * n + 40 ≤ V) (hc : σ cv < 18 * n + 12) : Bdd V σ A (sgcEx n cv) := by
  refine bdd_sgE H (i := .sub (.var cv) (.lit (17 * n + 11))) ⟨?_, ?_⟩ ?_
  · show σ cv ≤ V; omega
  · show 17 * n + 11 ≤ V; omega
  · simp only [Ex.eval]; omega

variable (H : BN V σ A n) (hn : 40 * n + 40 ≤ V) (hc : σ cv < 18 * n + 12)
include H hn hc

theorem bdd_ncEx (u : ℕ) (hcv : cv = u + 22) : Bdd V σ A (ncEx n u) := by
  subst hcv
  have hsg := bdd_sgcEx (u + 22) H hn hc
  refine bdd_famChain n (u + 22) (by omega) (by omega) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega))
    (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega))
    (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) ?_
  exact bdd_ifLt (bdd_lit (Nat.zero_le V)) hsg (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_nEx : Bdd V σ A (nEx n cv) := by
  have hsg := bdd_sgcEx cv H hn hc
  refine bdd_famChain n cv (by omega) (by omega) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega))
    (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega))
    (bdd_lit (by omega)) (bdd_lit (by omega)) (bdd_lit (by omega)) ?_
  exact bdd_ifLt (bdd_lit (Nat.zero_le V)) hsg (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (Nat.zero_le V))

variable (tv : ℕ) (ht : σ tv ≤ V)
include ht

theorem bdd_lEx : Bdd V σ A (lEx n cv tv) := by
  have he : Bdd V σ A (Ex.var tv) := ht
  have h12 : 12 ≤ V := by omega
  refine bdd_famChain n cv (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact bdd_tabLits he _ h12 (by simp) (by intro x hx; simp at hx; omega)

theorem bdd_rEx : Bdd V σ A (rEx n cv tv) := by
  have he : Bdd V σ A (Ex.var tv) := ht
  have h12 : 12 ≤ V := by omega
  refine bdd_famChain n cv (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact bdd_tabLits he _ h12 (by simp) (by intro x hx; simp at hx; omega)

theorem bdd_negEx : Bdd V σ A (negEx n cv tv) := by
  have he : Bdd V σ A (Ex.var tv) := ht
  have h12 : 12 ≤ V := by omega
  have hsg := bdd_sgcEx cv H hn hc
  refine bdd_famChain n cv (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
    | exact bdd_tabLits he _ h12 (by simp) (by intro x hx; simp at hx; omega)
    | exact bdd_ifLt hsg (bdd_lit (by omega)) (fun _ => bdd_tabLits he _ h12 (by simp) (by intro x hx; simp at hx; omega))
        (fun _ => bdd_tabLits he _ h12 (by simp) (by intro x hx; simp at hx; omega))

omit ht in
theorem bdd_bndE : Bdd V σ A (bndE n cv) := by
  have hc' : Bdd V σ A (Ex.var cv) := by show σ cv ≤ V; omega
  simp only [bndE]
  repeat' refine bdd_ifLt hc' (bdd_lit (by omega)) (fun _ => ?_) (fun _ => ?_)
  all_goals exact bdd_lit (by omega)

omit ht in
theorem bdd_phiEx (ev : ℕ) (he : σ ev ≤ V) : Bdd V σ A (phiEx n cv ev) := by
  have hv : Bdd V σ A (Ex.var ev) := he
  have hb := bdd_bndE cv H hn hc
  have hsg := bdd_sgcEx cv H hn hc
  have key : ∀ l : List Ex, l.length + 1 ≤ V → (∀ v ∈ l, Bdd V σ A v) → Bdd V σ A (tabX (Ex.var ev) 0 l) :=
    fun l hl hb' => bdd_tabX hv l 0 (by omega) hb'
  simp only [phiEx]
  refine bdd_famChain n cv (by omega) (by omega) (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_)
    (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_)
    (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_) (key _ (by simp; omega) ?_)
    (key _ (by simp; omega) ?_) (bdd_ifLt hsg (bdd_lit (by omega)) (fun _ => key _ (by simp; omega) ?_)
      (fun _ => key _ (by simp; omega) ?_)) <;>
    simp [List.forall_mem_cons, Bdd, aff, Ex.eval, hb] <;> omega

end

section eps
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ} (cv tv u : ℕ)
  {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem bdd_epsEx (H : BN V σ A n) (hn : 40 * n + 40 ≤ V) (hc : σ cv < 18 * n + 12) (ht : σ tv ≤ V)
    (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hs : 2 ^ σ 0 ≤ V) (N : LNum V (Nat.size p)) :
    Bdd V σ A (epsEx n cv tv u) := by
  have h2 : 2 ≤ V := by omega
  refine bdd_ifLt (bdd_negEx cv H hn hc tv ht) (bdd_lit (by omega)) (fun _ => bdd_lit (by omega)) (fun _ => ?_)
  refine bdd_pow2 (bdd_MEx u H hR hs N) h2 ?_
  rw [eval_MEx u hR]
  exact N.hM2

end eps

end ECDLP.L90
end
