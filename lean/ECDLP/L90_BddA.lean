import ECDLP.L90_NoRd
import ECDLP.L81_Bdd

/-!
# L90 / BddA: value bounds (`Bdd V`) -- generic helpers, `pE`, `szE`, `jm1E`, `prel`

Numeric side conditions are explicit arguments (nothing hidden): `BN V sigma A n` (L81), `2 ^ sigma 0 <= V`, etc.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83

section helpers
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_ifLt01 (e f : Ex) : Ex.eval σ A (.ifLt e f (.lit 0) (.lit 1)) ≤ 1 := by
  simp only [Ex.eval]
  by_cases h : Ex.eval σ A e < Ex.eval σ A f <;> simp [h]

theorem bdd_pow2 {x : ℕ} {e : Ex} (he : Bdd V σ A e) (h2 : 2 ≤ V) (hV : 2 ^ Ex.eval σ A e ≤ V) :
    Bdd V σ A (pow2 x e) :=
  bdd_nprod_const (b := .lit 2) (c := 2) he (fun _ => h2) (fun _ => rfl)
    (fun j hj => le_trans (Nat.pow_le_pow_right (by norm_num) hj) hV)

theorem bdd_nsum_le1 {x : ℕ} {n b : Ex} (hn : Bdd V σ A n) (hnV : Ex.eval σ A n ≤ V)
    (hb : ∀ j < Ex.eval σ A n, Bdd V (Function.update σ x j) A b)
    (h1 : ∀ j, Ex.eval (Function.update σ x j) A b ≤ 1) : Bdd V σ A (nsum x n b) := by
  refine ⟨hn, Nat.zero_le _, hb, fun j hj => ?_⟩
  show foldSum _ 0 j ≤ V
  rw [foldSum_zero]
  calc ∑ i ∈ range j, Ex.eval (Function.update σ x i) A b ≤ ∑ i ∈ range j, 1 := sum_le_sum (fun i _ => h1 i)
    _ = j := by simp
    _ ≤ V := by omega

theorem bdd_tabX {e : Ex} (he : Bdd V σ A e) : ∀ (vs : List Ex) (k : ℕ), k + vs.length + 1 ≤ V →
    (∀ v ∈ vs, Bdd V σ A v) → Bdd V σ A (tabX e k vs)
  | [], k, _, _ => by simp only [tabX]; exact Nat.zero_le V
  | y :: vs, k, hk, h => by
    simp only [tabX]
    refine bdd_ifLt he (bdd_lit (by simp at hk; omega)) (fun _ => h y (by simp)) (fun _ => ?_)
    exact bdd_tabX he vs (k + 1) (by simp at hk; omega) (fun v hv => h v (by simp [hv]))

theorem bdd_lits (l : List ℕ) (hl : ∀ x ∈ l, x ≤ V) : ∀ v ∈ lits l, Bdd V σ A v := by
  intro v hv; simp [lits] at hv; obtain ⟨x, hx, rfl⟩ := hv; exact bdd_lit (hl x hx)

theorem bdd_famChain (n cv : ℕ) (hc : σ cv ≤ V) (hn : 17 * n + 11 ≤ V) {rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn : Ex}
    (h1 : Bdd V σ A rg) (h2 : Bdd V σ A ue) (h3 : Bdd V σ A cu) (h4 : Bdd V σ A s0x) (h5 : Bdd V σ A s0y)
    (h6 : Bdd V σ A srx) (h7 : Bdd V σ A sry) (h8 : Bdd V σ A e0) (h9 : Bdd V σ A e1) (h10 : Bdd V σ A e2)
    (h11 : Bdd V σ A e3) (h12 : Bdd V σ A sn) : Bdd V σ A (famChain n cv rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn) := by
  simp only [famChain]
  have hc' : Bdd V σ A (Ex.var cv) := hc
  repeat' refine bdd_ifLt hc' (bdd_lit (by omega)) (fun _ => ?_) (fun _ => ?_)
  all_goals assumption

theorem bdd_aff (cv k m : ℕ) (hk : k ≤ V) (hm : m ≤ V) (hc : σ cv + k ≤ V) : Bdd V σ A (aff cv k m) := by
  simp only [aff, Bdd, Ex.eval]
  refine ⟨⟨?_, hk, hc⟩, hm⟩
  show σ cv ≤ V
  omega

end helpers

section par
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ} (u : ℕ)
  {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem bdd_pE (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hs : 2 ^ σ 0 ≤ V) : Bdd V σ A pE := by
  have hp : p < 2 ^ σ 0 := p_lt hR
  have h0 := H.h0
  exact bdd_valE 0 0 920 921 (by norm_num) (by norm_num) (by norm_num) H.hA H.h2 (by omega) (by rw [hR.hp]; omega)

theorem bdd_szE (H : BN V σ A n) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hs : 2 ^ σ 0 ≤ V) :
    Bdd V σ A (szE u) := by
  have hp : p < 2 ^ σ 0 := p_lt hR
  have h0 := H.h0
  have h2 := H.h2
  refine ⟨bdd_pE H hR hs, ?_⟩
  rw [eval_pE hR]
  refine bdd_nsum_le1 (n := .var 0) (by simp only [Bdd, Function.update_apply]; simp; omega) (by simp [Ex.eval, Function.update_apply]; omega) ?_ ?_
  · intro j hj
    simp only [Ex.eval, Function.update_apply] at hj
    simp at hj
    refine bdd_ifLt ?_ (bdd_pow2 (x := u + 61) ?_ h2 ?_) (fun _ => bdd_lit (Nat.zero_le V)) (fun _ => bdd_lit (by omega))
    · simp only [Bdd, Function.update_apply]; simp; omega
    · simp only [Bdd, Function.update_apply]; simp; omega
    · simp only [Ex.eval, Function.update_apply]; simp
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hj.le) hs
  · intro j
    exact eval_ifLt01 _ _

end par

end ECDLP.L90
end
