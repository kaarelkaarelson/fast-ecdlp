import ECDLP.L93_Main
import ECDLP.L90_Real
import ECDLP.L89_Rep
import ECDLP.L91_Real

/-!
# L96 / Glue: from `CtxM` + `FrameIn` memory to L83's instance hypotheses

* `odd_of_good`: `Good (r+1) x τ` forces `p % 2 = 1` (for `p = 2` the discriminant of `y^2 = x^3 + a x + b` vanishes).
* `zero3 A`: the memory with array `3` cleared; `reads72_zero3`: `Reads72n σ A ..` (no clause on array 3) gives `Reads72 σ (zero3 A) ..`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L80

theorem odd_of_prime_delta (p a b : ℕ) (hp : p.Prime) (hΔ : (ECDLP.L51.Wc p a b).Δ ≠ 0) : p % 2 = 1 := by
  by_contra h
  have h2 : p = 2 := by
    rcases hp.eq_one_or_self_of_dvd 2 (by omega) with h | h <;> omega
  subst h2
  apply hΔ
  simp only [ECDLP.L51.Wc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  have h2 : (2 : ZMod 2) = 0 := by decide
  generalize (a : ZMod 2) = x
  generalize (b : ZMod 2) = y
  revert x y; decide

theorem odd_of_good (r : ℕ) (x : Inst) (τ : List Bool) (h : Good (r + 1) x τ) : x.1 % 2 = 1 :=
  odd_of_prime_delta x.1 x.2.1 x.2.2.1 h.1 h.2.1

/-- clear array 3 -/
def zero3 (A : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ := fun a => if a = 3 then fun _ => 0 else A a

theorem zero3_off (A : ℕ → ℕ → ℕ) : ∀ b, ¬ (b = 3 ∨ 12 ≤ b) → zero3 A b = A b := by
  intro b hb
  have : b ≠ 3 := fun h => hb (Or.inl h)
  simp [zero3, this]

theorem reads72_zero3 {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : Reads72n σ A p a b X xR yR π ℓ bW) : ECDLP.L72.Reads72 σ (zero3 A) p a b X xR yR π ℓ bW where
  hp := by simpa [zero3] using h.hp
  ha := by simpa [zero3] using h.ha
  hb := by simpa [zero3] using h.hb
  hxR := by simpa [zero3] using h.hxR
  hyR := by simpa [zero3] using h.hyR
  hOp := by simpa [zero3] using h.hOp
  hX := by simpa [zero3] using h.hX
  hlen := by simpa [zero3] using h.hlen
  hl := by simpa [zero3] using h.hl
  hbW := by simpa [zero3] using h.hbW
  hpi := by intro q hq; simpa [zero3] using h.hpi q hq
  h3 := by intro j; simp [zero3]

end ECDLP.L96
end
