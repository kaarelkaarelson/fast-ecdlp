import ECDLP.L35_Challenge

/-!
# L61 / Challenge: the audit statement over the `Bool` alphabet

`L35_Challenge.enc` feeds the machine `Option Bool` symbols (a `none` separator).  Rudich's simulation
(`FactoringAux/Simulate/IO.lean`, `SProg/Machine.lean`) is built for machines whose input stack has the `Bool`
alphabet.  We therefore restate the input code over `Bool`, with a self-delimiting block code:

* `block l` = each bit `b` of `l` written as the two bits `true, b`, then the terminator `false`;
* `encB (p,a,b,x,y,π)` = `block π`, then `block (encodeNat n)` for `n = p, a, b, x, y`.

`encB` is injective (`encB_injective`) and is `L35.enc` followed by a letter-to-two-bits recoding
(`some b ↦ true b`, `none ↦ false`, with the prefix moved to the front).  The recoding doubles the length and
adds `O(1)`, which changes the bound `C_k · 2^(L/k)` only by `k ↦ 2k` (the statement quantifies over all `k`).
`Inst`, `strings`, `lexLeast`, `encOut` are L35's, unchanged.
-/
namespace ECDLP.L61
open ECDLP Computability Turing

/-- The self-delimiting block code of a bit string. -/
def block (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

/-- The `Bool`-alphabet input code: the prefix first, then the five numbers. -/
def encB : Inst → List Bool
  | (p, a, b, x, y, π) => block π ++ [p, a, b, x, y].flatMap (fun n => block (encodeNat n))

/-- **The audit claim, over the `Bool` alphabet** (the `Bool` restatement of `ECDLP.subexponentialRate`): for the
fixed `m`, one machine with finite stack alphabets outputs `lexLeast m` (output code `encOut`, as in L35) on the code
`encB` within `C_k · 2^(L/k)` steps for every `k ≥ 1`, `L` the input length. -/
def SubexpRate (m : ℕ) : Prop :=
  ∃ M : TM2ComputableInTime encB encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k)

theorem block_cons (b : Bool) (l : List Bool) : block (b :: l) = true :: b :: block l := by
  simp [block]

theorem block_inj : ∀ (l l' r r' : List Bool), block l ++ r = block l' ++ r' → l = l' ∧ r = r'
  | [], [], r, r', h => by simpa [block] using h
  | [], b :: l', r, r', h => by simp [block] at h
  | b :: l, [], r, r', h => by simp [block] at h
  | b :: l, b' :: l', r, r', h => by
      simp only [block_cons, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2⟩ := block_inj l l' r r' h
      exact ⟨by rw [h1], h2⟩

theorem encodeNat_inj {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have := congrArg decodeNat h
  simpa using this

/-- The input code determines the instance. -/
theorem encB_injective : Function.Injective encB := by
  rintro ⟨p, a, b, x, y, π⟩ ⟨p', a', b', x', y', π'⟩ h
  simp only [encB, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at h
  obtain ⟨hπ, h⟩ := block_inj _ _ _ _ h
  obtain ⟨h1, h⟩ := block_inj _ _ _ _ h
  obtain ⟨h2, h⟩ := block_inj _ _ _ _ h
  obtain ⟨h3, h⟩ := block_inj _ _ _ _ h
  obtain ⟨h4, h5⟩ := block_inj _ _ _ _ h
  obtain ⟨h5, -⟩ := block_inj _ _ _ _ (by simpa using h5 : block (encodeNat y) ++ [] = block (encodeNat y') ++ [])
  simp [hπ, encodeNat_inj h1, encodeNat_inj h2, encodeNat_inj h3, encodeNat_inj h4, encodeNat_inj h5]

end ECDLP.L61

#print axioms ECDLP.L61.encB_injective
