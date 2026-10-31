import ECDLP.L61_Main
import ECDLP.L65_Rate

/-!
# L70 / Good: the instances on which the edge engine is asked, and the zero-count shortcut

`Good m x τ` : `p` prime, `Δ ≠ 0`, `R` nonsingular, `|τ| ≤ nlen` (no reducedness of `a, b, xR, yR`).
`Zc_pos_good` : a positive count forces `Good`.  So a guard that decides `Good` (flag `0` only if `¬ Good`)
is automatically sound: flag `0` implies count `0`, including the over-long prefixes of length `n + 1`.
-/
namespace ECDLP.L70
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65

/-- Instances on which the engine's contract is required. -/
def Good (m : ℕ) (x : Inst) (τ : List Bool) : Prop :=
  x.1.Prime ∧ (Wc x.1 x.2.1 x.2.2.1).Δ ≠ 0 ∧
    (Wc x.1 x.2.1 x.2.2.1).toAffine.Nonsingular ((x.2.2.2.1 : ℕ) : ZMod x.1) ((x.2.2.2.2.1 : ℕ) : ZMod x.1) ∧
    τ.length ≤ nlen m x

/-- A positive count forces `Good`. -/
theorem Zc_pos_good (m : ℕ) (x : Inst) (τ : List Bool) (h : 0 < Zc m x τ) : Good m x τ := by
  have hne : (strings m (withPre x τ)).Nonempty := Set.nonempty_of_ncard_ne_zero (by unfold Zc at h; omega)
  obtain ⟨s, hs⟩ := hne
  refine ⟨?_, ?_, ?_, Zc_pos_len m x τ h⟩
  · obtain ⟨p, a, b, xR, yR, π⟩ := x
    have hs' : s ∈ strings m (p, a, b, xR, yR, τ) := hs
    simp only [strings] at hs'
    split_ifs at hs' with hp
    · exact hp
    · exact absurd hs' (by simp)
  · obtain ⟨p, a, b, xR, yR, π⟩ := x
    have hs' : s ∈ strings m (p, a, b, xR, yR, τ) := hs
    simp only [strings] at hs'
    split_ifs at hs' with hp
    · exact hs'.1
    · exact absurd hs' (by simp)
  · obtain ⟨p, a, b, xR, yR, π⟩ := x
    have hs' : s ∈ strings m (p, a, b, xR, yR, τ) := hs
    simp only [strings] at hs'
    split_ifs at hs' with hp
    · obtain ⟨-, P, -, -, -, -, hsum, hxy⟩ := hs'
      haveI : Fact p.Prime := ⟨hp⟩
      revert hsum hxy
      generalize (List.ofFn P).sum = S
      intro hsum hxy
      cases S with
      | zero => exact absurd rfl hsum
      | some x' y' hn =>
          simp only at hxy
          obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
          have e1 : x' = (xR : ZMod p) := h1
          have e2 : y' = (yR : ZMod p) := h2
          rw [e1, e2] at hn
          exact hn
    · exact absurd hs' (by simp)

end ECDLP.L70
