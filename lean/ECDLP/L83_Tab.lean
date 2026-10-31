import ECDLP.L83_Par

/-!
# L83 / Tab: table lookup expressions `tabX` and affine expressions `aff`
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73

/-- `tabX e k [v0, v1, ...]`: the entry number `eval e - k` (default `0` past the end), nested `ifLt` -/
def tabX (e : Ex) : ℕ → List Ex → Ex
  | _, [] => .lit 0
  | k, y :: vs => .ifLt e (.lit (k + 1)) y (tabX e (k + 1) vs)

/-- `(c + k) - m` -/
def aff (cv : ℕ) (k m : ℕ) : Ex := .sub (.add (.var cv) (.lit k)) (.lit m)

/-- the 12 families of identities as a balanced `ifLt` tree on the identity number (depth 4):
`rng < 11n+5 <= uEq < 12n+6 <= curve < 13n+7 <= s0x < +8 <= s0y < +9 <= sRx < +10 <= sRy < 13n+11 <= e0 < 14n+11 <= e1 < 15n+11 <= e2 < 16n+11 <= e3 < 17n+11 <= sign` -/
def famChain (n cv : ℕ) (rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn : Ex) : Ex :=
  let c : Ex := .var cv
  .ifLt c (.lit (13 * n + 10))
    (.ifLt c (.lit (13 * n + 7)) (.ifLt c (.lit (11 * n + 5)) rg (.ifLt c (.lit (12 * n + 6)) ue cu))
      (.ifLt c (.lit (13 * n + 8)) s0x (.ifLt c (.lit (13 * n + 9)) s0y srx)))
    (.ifLt c (.lit (15 * n + 11))
      (.ifLt c (.lit (13 * n + 11)) sry (.ifLt c (.lit (14 * n + 11)) e0 e1))
      (.ifLt c (.lit (16 * n + 11)) e2 (.ifLt c (.lit (17 * n + 11)) e3 sn)))

def sgcEx (n cv : ℕ) : Ex := ECDLP.L76.sgE ECDLP.L76.lay72 (.sub (.var cv) (.lit (17 * n + 11)))

def lits (l : List ℕ) : List Ex := l.map Ex.lit

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_tabX (e : Ex) : ∀ (vs : List Ex) (k : ℕ), k ≤ Ex.eval σ A e →
    Ex.eval σ A (tabX e k vs) = (vs.map (Ex.eval σ A)).getD (Ex.eval σ A e - k) 0
  | [], k, h => by simp [tabX, Ex.eval]
  | y :: vs, k, h => by
    simp only [tabX, Ex.eval]
    split_ifs with hlt
    · have : Ex.eval σ A e - k = 0 := by omega
      simp [this]
      intro h2; omega
    · rw [eval_tabX e vs (k + 1) (by omega)]
      have : Ex.eval σ A e - k = (Ex.eval σ A e - (k + 1)) + 1 := by omega
      rw [this]; simp
      intro h2; omega

theorem eval_aff (cv k m : ℕ) : Ex.eval σ A (aff cv k m) = σ cv + k - m := by simp [aff, Ex.eval]

theorem eval_tabX0 (e : Ex) (vs : List Ex) : Ex.eval σ A (tabX e 0 vs) = (vs.map (Ex.eval σ A)).getD (Ex.eval σ A e) 0 := by
  simpa using eval_tabX e vs 0 (Nat.zero_le _)

end ECDLP.L83
end
