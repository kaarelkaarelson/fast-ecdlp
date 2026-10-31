import ECDLP.L83_Inst

/-!
# L83 / Mid: the four form oracles of the mid kind (`nE, epsE, lE, rE`) for the real identities

Identity number in slot `cv` (= `u+15`), term index in slot `tv` (= `u+43`).  The term tables are index-independent per family
(positions of the slots in `slotList`); only `sign` depends on the sign requirement (`sgE lay72`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 Slot Cst

section
variable (n cv tv : ℕ)

/-- number of terms `(F c).n` -/
def nEx : Ex :=
  famChain n cv (.lit 4) (.lit 2) (.lit 6) (.lit 2) (.lit 2) (.lit 2) (.lit 2) (.lit 5) (.lit 6) (.lit 6) (.lit 6)
    (.ifLt (.lit 0) (sgcEx n cv) (.lit 3) (.lit 0))

/-- position (rank) of the left slot of term `t` -/
def lEx : Ex :=
  let t : Ex := .var tv
  famChain n cv (tabX t 0 (lits [0, 1, 2, 3])) (tabX t 0 (lits [0, 2])) (tabX t 0 (lits [0, 1, 3, 4, 6, 7])) (tabX t 0 (lits [0, 2]))
    (tabX t 0 (lits [0, 2])) (tabX t 0 (lits [0, 2])) (tabX t 0 (lits [0, 2])) (tabX t 0 (lits [0, 0, 3, 4, 5]))
    (tabX t 0 (lits [0, 0, 3, 5, 6, 7])) (tabX t 0 (lits [0, 2, 3, 4, 5, 6])) (tabX t 0 (lits [0, 0, 3, 5, 6, 7]))
    (tabX t 0 (lits [0, 2, 3]))

/-- position (rank) of the right slot of term `t` -/
def rEx : Ex :=
  let t : Ex := .var tv
  famChain n cv (tabX t 0 (lits [2, 2, 2, 2])) (tabX t 0 (lits [1, 2])) (tabX t 0 (lits [0, 2, 2, 5, 5, 8])) (tabX t 0 (lits [1, 1]))
    (tabX t 0 (lits [1, 1])) (tabX t 0 (lits [1, 1])) (tabX t 0 (lits [1, 1])) (tabX t 0 (lits [1, 2, 3, 3, 6]))
    (tabX t 0 (lits [1, 2, 4, 4, 4, 8])) (tabX t 0 (lits [0, 1, 1, 1, 1, 7])) (tabX t 0 (lits [1, 2, 4, 4, 4, 8]))
    (tabX t 0 (lits [1, 1, 1]))

/-- `1` if the sign of term `t` is negative -/
def negEx : Ex :=
  let t : Ex := .var tv
  famChain n cv (tabX t 0 (lits [0, 0, 0, 1])) (tabX t 0 (lits [0, 1])) (tabX t 0 (lits [0, 1, 1, 1, 0, 1])) (tabX t 0 (lits [0, 1]))
    (tabX t 0 (lits [0, 1])) (tabX t 0 (lits [0, 1])) (tabX t 0 (lits [0, 1])) (tabX t 0 (lits [0, 1, 1, 0, 1]))
    (tabX t 0 (lits [0, 1, 1, 0, 0, 1])) (tabX t 0 (lits [0, 1, 1, 1, 0, 1])) (tabX t 0 (lits [0, 1, 1, 1, 0, 1]))
    (.ifLt (sgcEx n cv) (.lit 2) (tabX t 0 (lits [0, 1, 1])) (tabX t 0 (lits [0, 0, 1])))

/-- the coefficient `eps = +-1` of term `t` in `Z/(2^M+1)`: `1` or `2^M` (`= -1`); `u` is the base slot (binders `u+60 ..`) -/
def epsEx (u : ℕ) : Ex := .ifLt (negEx n cv tv) (.lit 1) (.lit 1) (pow2 (u + 60) (MEx u))

end

variable {n : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem eval_nEx (cv : ℕ) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (x : Cn n) (hc : σ cv = cnNum x) :
    Ex.eval σ A (nEx n cv) = (formL (sgR n ℓ π) x).length := by
  have hs := eval_sgE lay72 (reads_of_reads72 hR) (.sub (.var cv) (.lit (17 * n + 11))) (σ := σ) (A := A)
  obtain ⟨c0, hcn⟩ : ∃ c0, c0 = cnNum x := ⟨_, rfl⟩
  rw [← hcn] at hc
  simp only [nEx, famChain, sgcEx, Ex.eval, hc] at hs ⊢
  cases x with
  | sign i =>
    simp only [cnNum] at hcn
    have h1 : c0 - (17 * n + 11) = i := by omega
    rw [h1] at hs
    simp (disch := omega) only [if_pos, if_neg]
    rw [hs]
    cases hsg : sgOf ℓ π i <;> simp [formL, sgR, hsg, sgCode]
  | rng a =>
    simp only [cnNum] at hcn
    have := varIdx_lt a
    simp (disch := omega) only [if_pos, if_neg]
    simp [formL]
  | _ =>
    simp only [cnNum] at hcn
    simp (disch := omega) only [if_pos, if_neg]
    simp [formL, tailT]

theorem term_spec (cv tv : ℕ) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (x : Cn n) (hc : σ cv = cnNum x)
    (t : ℕ) (ht : σ tv = t) (e : ℤ) (s1 s2 : Slot n) (h : (formL (sgR n ℓ π) x)[t]? = some (e, s1, s2)) :
    Ex.eval σ A (lEx n cv tv) = (slotList (sgR n ℓ π) x).idxOf s1 ∧
    Ex.eval σ A (rEx n cv tv) = (slotList (sgR n ℓ π) x).idxOf s2 ∧
    ((e = 1 ∧ Ex.eval σ A (negEx n cv tv) = 0) ∨ (e = -1 ∧ Ex.eval σ A (negEx n cv tv) = 1)) := by
  have hs := eval_sgE lay72 (reads_of_reads72 hR) (.sub (.var cv) (.lit (17 * n + 11))) (σ := σ) (A := A)
  obtain ⟨c0, hcn⟩ : ∃ c0, c0 = cnNum x := ⟨_, rfl⟩
  rw [← hcn] at hc
  simp only [lEx, rEx, negEx, famChain, sgcEx, Ex.eval, hc, ht, eval_tabX0, lits, List.map_cons, List.map_nil] at hs ⊢
  have hk7 : t < 7 := by
    by_contra hh
    have : (formL (sgR n ℓ π) x).length ≤ 6 := by
      have := mass_le (sgR n ℓ π) x
      cases x <;> simp [formL, tailT, sgR] <;> (try split) <;> simp
    rw [List.getElem?_eq_none (by omega)] at h; simp at h
  cases x with
  | sign i =>
    simp only [cnNum] at hcn
    have h1 : c0 - (17 * n + 11) = i := by omega
    rw [h1] at hs
    simp (disch := omega) only [if_pos, if_neg]
    rw [hs]
    cases hsg : sgOf ℓ π i
    · simp [formL, sgR, hsg] at h
    · rw [if_pos (show sgCode Sg.pos < 2 by decide)]
      simp only [formL, sgR, hsg] at h
      interval_cases t <;> simp at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [slotList, sgR, hsg, List.idxOf_cons]
    · rw [if_neg (show ¬ sgCode Sg.neg < 2 by decide)]
      simp only [formL, sgR, hsg] at h
      interval_cases t <;> simp at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [slotList, sgR, hsg, List.idxOf_cons]
  | rng a =>
    simp only [cnNum] at hcn
    have := varIdx_lt a
    simp (disch := omega) only [if_pos, if_neg]
    simp only [formL] at h
    interval_cases t <;> simp at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> cases a <;>
      simp [slotList, List.idxOf_cons, bnd]
  | _ =>
    simp only [cnNum] at hcn
    simp (disch := omega) only [if_pos, if_neg]
    simp only [formL, tailT, List.cons_append, List.nil_append] at h
    interval_cases t <;> simp at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [slotList, List.idxOf_cons, Fin.ext_iff]

end ECDLP.L83
end
