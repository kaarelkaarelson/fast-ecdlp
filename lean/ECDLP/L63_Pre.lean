import ECDLP.L63_Cv

/-!
# L63 / Pre: the prefix constraints `xcOf`, `sgOf` computed from the prefix array
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51

/-- index of bit `q` of point `i` in the string -/
def pidx (i q : Ex) : Ex := .add (.mul i (.add (.var 2) (.lit 1))) q
/-- `[k < |π|]` -/
def pfDef (k : Ex) : Ex := .ifLt k (.var 1) (.lit 1) (.lit 0)
/-- the prefix bit `k` (cell `k+1` of array 6) -/
def pfBit (k : Ex) : Ex := bitRd 6 (.add k (.lit 1))
/-- string position of the bit `jj` of `x_i` (`jj = ℓ-1-q`) -/
def qOf (jj : Ex) : Ex := .sub (.var 2) (.add jj (.lit 1))
/-- `jj < ℓ` and the prefix constrains bit `jj` of `x_i` -/
def xcDefE (i jj : Ex) : Ex := .ifLt jj (.var 2) (pfDef (pidx i (qOf jj))) (.lit 0)
/-- the value the prefix prescribes for bit `jj` of `x_i` -/
def xcBitE (i jj : Ex) : Ex := pfBit (pidx i (qOf jj))
/-- sign code of point `i`: `0` none, `1` pos (`y > (p-1)/2`), `2` neg -/
def sgE (i : Ex) : Ex :=
  .ifLt (pidx i (.var 2)) (.var 1) (.ifLt (.lit 0) (.rd 6 (.add (pidx i (.var 2)) (.lit 1))) (.lit 1) (.lit 2)) (.lit 0)

def sgCode : Sg → ℕ | .none => 0 | .pos => 1 | .neg => 2
def sgDec : ℕ → Sg | 0 => .none | 1 => .pos | _ => .neg

theorem sgDec_code (s : Sg) : sgDec (sgCode s) = s := by cases s <;> rfl

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_pidx (i q : Ex) :
    eval σ A (pidx i q) = eval σ A i * (σ 2 + 1) + eval σ A q := rfl

theorem pf_bit {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    {k : ℕ} (hk : k < π.length) : (if A 6 (k + 1) = 0 then 0 else 1) = (π[k]).toNat := by
  have := hr.hpi k hk
  cases hb : π[k]
  · rw [hb] at this; simp at this; simp [this]
  · rw [hb] at this; simp at this; simp [this]

theorem getElem?_eq_some {π : List Bool} {k : ℕ} {β : Bool} :
    π[k]? = some β ↔ ∃ h : k < π.length, π[k] = β := by
  rw [List.getElem?_eq_some_iff]

/-- `(jj, β) ∈ xcOf ℓ π i` iff the expressions say so -/
theorem xc_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (i jj : Ex) (β : Bool) :
    (eval σ A jj, β) ∈ xcOf ℓ π (eval σ A i) ↔
      eval σ A (xcDefE i jj) = 1 ∧ eval σ A (xcBitE i jj) = β.toNat := by
  have hl := hr.hl
  have hlen := hr.hlen
  simp only [xcDefE, xcBitE, pfDef, pfBit, qOf, eval_ifLt', eval_bitRd, eval_pidx, xcOf, List.mem_filterMap,
    List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq, eval, hl, hlen]
  by_cases hj : eval σ A jj < ℓ
  · rw [if_pos hj]
    set q := ℓ - (eval σ A jj + 1) with hq
    have hq' : q < ℓ := by omega
    have hjq : ℓ - 1 - q = eval σ A jj := by omega
    constructor
    · rintro ⟨q', hq'', γ, hγ, h1, h2⟩
      have : q' = q := by omega
      subst this
      obtain ⟨hlt, hget⟩ := getElem?_eq_some.1 hγ
      subst h2
      refine ⟨if_pos hlt, ?_⟩
      rw [pf_bit hr hlt, hget]
    · rintro ⟨h1, h2⟩
      have hlt : eval σ A i * (ℓ + 1) + q < π.length := by
        by_contra hc; rw [if_neg hc] at h1; omega
      rw [pf_bit hr hlt] at h2
      have h3 : π[eval σ A i * (ℓ + 1) + q] = β := by
        cases hx : π[eval σ A i * (ℓ + 1) + q] <;> cases β <;> simp_all
      exact ⟨q, hq', π[eval σ A i * (ℓ + 1) + q], getElem?_eq_some.2 ⟨hlt, rfl⟩, hjq, h3⟩
  · rw [if_neg hj]
    constructor
    · rintro ⟨q', hq'', γ, -, h1, -⟩; omega
    · rintro ⟨h1, -⟩; omega

theorem eval_sgE {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (i : Ex) : eval σ A (sgE i) = sgCode (sgOf ℓ π (eval σ A i)) := by
  have hl := hr.hl
  have hlen := hr.hlen
  simp only [sgE, eval_ifLt', eval_pidx, sgOf, eval, hl, hlen]
  by_cases hlt : eval σ A i * (ℓ + 1) + ℓ < π.length
  · rw [if_pos hlt, List.getElem?_eq_getElem hlt]
    have := hr.hpi _ hlt
    cases hb : π[eval σ A i * (ℓ + 1) + ℓ] <;> rw [hb] at this <;> simp at this <;> simp [sgCode, this]
  · rw [if_neg hlt, List.getElem?_eq_none (by omega)]
    rfl

end ECDLP.L63
end
