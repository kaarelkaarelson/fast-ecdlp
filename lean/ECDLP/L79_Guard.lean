import ECDLP.L74_Kind
import ECDLP.L75_IbKindB

/-!
# L79 / Guard: a total version of a gate-kind expression (child coordinate guard)

`PExB.bout` quantifies over ALL pairs of nodes `(a, b)`, not only edges.  For the kinds fa and mid the expressions read the child
coordinate `dq = u+20` as an index `< A` (fa: `k` of `mid k`; mid: `j1` of `ib j1`).  For a non-child `b`, `dq` can be any number `< A*A`.
`guardE E = if dq < A then E else 0` leaves the value on every edge unchanged (`guardKind`) and makes the bound total.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (fa_child mid_child)

/-- a state that agrees with an `Ag`-state off the written slots is an `Ag`-state -/
theorem ag_of_agr {B u vs : ℕ} {σ₀ σ σ' : ℕ → ℕ} (hu : B ≤ u) (hσ : Ag B σ₀ σ) (h : ECDLP.L74.Agr u vs σ σ') :
    Ag B σ₀ σ' := fun y hy => by rw [h y (Or.inl (by omega))]; exact hσ y hy

def guardE (u : ℕ) (E : Ex) : Ex := .ifLt (.var (u + 20)) (.var (u + 12)) E (.lit 0)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- on an edge out of a fa or mid node, the child coordinate is `< A` -/
theorem childCoord_lt_of_pa {qa qb : CG ι ιc N0.A} (hk : kindOf qa = GKind.fa ∨ kindOf qa = GKind.mid)
    (hpa : qa ∈ paC (w := w) φ qb) : childCoord qb < N0.A := by
  cases qa with
  | src i s => rcases hk with h | h <;> simp [kindOf] at h
  | gt c g =>
    cases g with
    | fa j s =>
      obtain ⟨kk, hkk⟩ := fa_child (w := w) φ c j s hpa
      subst hkk; simp only [childCoord]; exact kk.2
    | mid k =>
      obtain ⟨j1, hj⟩ := mid_child (w := w) φ c k hpa
      subst hj; simp only [childCoord]; exact j1.2
    | ib _ => rcases hk with h | h <;> simp [kindOf] at h
    | car _ => rcases hk with h | h <;> simp [kindOf] at h

/-- the guarded version of a fa / mid kind -/
def guardKind {kd : GKind} (hkd : kd = GKind.fa ∨ kd = GKind.mid)
    (K0 : GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L kd (L.enum N0.A) u X) :
    GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L kd (L.enum N0.A) u X where
  outE := guardE u K0.outE
  hout := by
    intro σ₀ hC σ hσ a b z hk hpa hKS hz
    have hlt : childCoord ((L.enum N0.A).symm b) < N0.A :=
      childCoord_lt_of_pa (φ := φ) (by rw [hk]; exact hkd) hpa
    obtain ⟨c, hid⟩ : ∃ c, idOf ((L.enum N0.A).symm a) = some c := by
      cases h : (L.enum N0.A).symm a with
      | src i s => rw [h] at hk; rcases hkd with h' | h' <;> subst h' <;> simp [kindOf] at hk
      | gt c g => exact ⟨c, rfl⟩
    have h12 := (hKS.hpar c hid).2.2.1
    have hq := hKS.hq
    have := K0.hout σ₀ hC σ hσ a b z hk hpa hKS hz
    simp only [guardE, Ex.eval, hq, h12]
    rw [if_pos hlt]
    exact this

end
end ECDLP.L79
end
