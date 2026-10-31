import ECDLP.L65_Spec
import ECDLP.L65_Bridge2

/-!
# L65 / Rate: the final rate theorem for the ECDLP edge family

`EdgeInp` is the input `(p, a, b, xR, yR, π)` (modulus, curve, target point, prefix); `len` is its length
(`≥ Nat.size p + 1`); `adm r` the admissibility conditions of L59's `search_computes_lexLeast_explicit`
(`p` prime, data below `p`, `Δ ≠ 0`, `R` nonsingular, prefix length bound).  `edge_rate r cost τ`: for the zero
test (any `cost : EdgeInp → ℕ`) satisfying the evaluation-cost bound `τ` (polynomial in a value bound `V`
meeting `(edgeFamily r).UniReq V (len i)`), `cost i ≤ C_k · 2^(len i / k)` for every `k ≥ 1`.
`τ` is the only hypothesis (besides the numbers `r`, `k`).
-/
noncomputable section
namespace ECDLP.L65
open ECDLP.L30 ECDLP.L51 ECDLP.L59 ECDLP.L35

/-- inputs of the bounded point-decomposition problem -/
structure EdgeInp where
  p : ℕ
  a : ℕ
  b : ℕ
  xR : ℕ
  yR : ℕ
  π : List Bool

namespace EdgeInp

/-- input length (bit lengths of the five numbers, the prefix length, and a unit) -/
def len (i : EdgeInp) : ℕ :=
  Nat.size i.p + Nat.size i.a + Nat.size i.b + Nat.size i.xR + Nat.size i.yR + i.π.length + 1

/-- admissibility (the hypotheses of `search_computes_lexLeast_explicit` and of the prefix counts) -/
def adm (r : ℕ) (i : EdgeInp) : Prop :=
  i.p.Prime ∧ i.a < i.p ∧ i.b < i.p ∧ i.xR < i.p ∧ i.yR < i.p ∧ (Wc i.p i.a i.b).Δ ≠ 0 ∧
    (Wc i.p i.a i.b).toAffine.Nonsingular (i.xR : ZMod i.p) (i.yR : ZMod i.p) ∧
    i.π.length ≤ (r + 1) * (ell i.p r + 1)

theorem size_p_add_four_le (i : EdgeInp) : Nat.size i.p + 4 ≤ 4 * i.len := by
  unfold len; omega

end EdgeInp

/-- **The rate theorem for the ECDLP edge family** (conditional on the evaluation-cost bound `τ`).
`cost i` is the number of steps of the uniform engine's zero test of `edgeNet` on input `i`. -/
theorem edge_rate (r : ℕ) (cost : EdgeInp → ℕ)
    (τ : ∃ c E : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len → cost i ≤ c * (V + 1) ^ E) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ i : EdgeInp, i.adm r → cost i ≤ C * 2 ^ (i.len / k) := by
  let CF : ECDLP.L60.CostedFamily :=
    { toNetFamily := edgeFamily r
      Inp := EdgeInp
      len := EdgeInp.len
      adm := EdgeInp.adm r
      cost := cost
      τ := τ }
  exact ECDLP.L60.rate_gen CF (edgeFamily_spec r)

end ECDLP.L65
end
