import ECDLP.L104_Final

/-!
# A fast algorithm for elliptic-curve discrete logarithms: the proof

The declarations of `Challenge.lean`, with the same names and types, proved.

* `Inst`, `enc`, `strings`, `lexLeast`, `lexLeast_isSome`, `encOut`: from `ECDLP/L35_Challenge.lean`,
  a verbatim copy of the Challenge's definitions, imported through the proof.
* `subexponentialRate`: proved by one line naming `ECDLP.L104R.subexponentialRate_all`
  (`ECDLP/L104_Final.lean`).
-/

namespace ECDLP
open Turing Computability

/-- **The result.** For every fixed `m`, one machine with finite alphabets outputs `lexLeast m` within
`C_k · 2^{L/k}` steps (`L` = input length) for every `k ≥ 1`, i.e. time `p ^ o(1)`. -/
theorem subexponentialRate (m : ℕ) :
    ∃ M : TM2ComputableInTime enc encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) :=
  L104R.subexponentialRate_all m

end ECDLP

#print axioms ECDLP.subexponentialRate
