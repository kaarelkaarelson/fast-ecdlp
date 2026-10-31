import ECDLP.L83_Tab

/-!
# L83 / Phi: the slot map `phi c j` as an expression (`phiEx`): slot number of the `e`-th used slot of identity `c`

Variables: the identity number `c` in slot `cv`, the rank `e` in slot `ev` (L73's `PhiEx`: `u+22, u+23`; L79's fa kind: `u+15, u+16`).
`vNum a = 12 + n + varIdx a`, so every table entry is affine in `c`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 Slot Cst

theorem vNum_eq {n : ℕ} (a : Var n) : vNum a = 12 + n + varIdx a := by
  cases a <;> simp only [vNum, varIdx] <;> omega

section
variable (n cv ev : ℕ)

/-- the constant bounding the variable with index `c` (`cX = 5`, `cp = 1`, `cN = 6`) -/
def bndE : Ex :=
  .ifLt (.var cv) (.lit (n + 1)) (.lit 5) <| .ifLt (.var cv) (.lit (4 * n + 4)) (.lit 1) <|
  .ifLt (.var cv) (.lit (5 * n + 5)) (.lit 6) <| .ifLt (.var cv) (.lit (7 * n + 5)) (.lit 1) (.lit 6)

def phiEx : Ex :=
  let e : Ex := .var ev
  famChain n cv (tabX e 0 [aff cv (n + 12) 0, aff cv (12 * n + 17) 0, .lit 0, bndE n cv])
    (tabX e 0 [aff cv (12 * n + 17) 0, .lit 0, aff cv 7 (10 * n)])
    (tabX e 0 [aff cv 7 (10 * n), aff cv (11 * n + 16) 0, aff cv 6 (11 * n), .lit 2, .lit 3, .lit 0, .lit 4,
      aff cv 10 (7 * n), .lit 1])
    (tabX e 0 [.lit (3 * n + 14), .lit 0, .lit (n + 12)])
    (tabX e 0 [.lit (4 * n + 15), .lit 0, .lit (2 * n + 13)])
    (tabX e 0 [.lit (4 * n + 14), .lit 0, .lit 7])
    (tabX e 0 [.lit (5 * n + 15), .lit 0, .lit 8])
    (tabX e 0 [aff cv 6 (7 * n), aff cv 2 (12 * n), aff cv 3 (10 * n), .lit 0, .lit 4, aff cv 6 (5 * n), .lit 1])
    (tabX e 0 [aff cv 6 (7 * n), aff cv 2 (13 * n), aff cv 3 (11 * n), aff cv 3 (12 * n), .lit 0,
      aff cv 4 (10 * n), .lit 4, aff cv 6 (5 * n), .lit 1])
    (tabX e 0 [aff cv 6 (8 * n), .lit 0, aff cv 3 (12 * n), aff cv 2 (14 * n), aff cv 4 (12 * n), .lit 4,
      aff cv 6 (5 * n), .lit 1])
    (tabX e 0 [aff cv 6 (9 * n), aff cv 3 (13 * n), aff cv 4 (13 * n), aff cv 5 (12 * n), .lit 0,
      aff cv 4 (12 * n), .lit 4, aff cv 6 (5 * n), .lit 1])
    (.ifLt (sgcEx n cv) (.lit 2) (tabX e 0 [aff cv 2 (15 * n), .lit 0, .lit 10, aff cv 0 (17 * n)])
      (tabX e 0 [aff cv 2 (15 * n), .lit 0, aff cv 0 (17 * n), .lit 9]))

end

variable {n : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem phiEx_spec (cv ev : ℕ) (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (x : Cn n) (hc : σ cv = cnNum x) (k : ℕ)
    (hk : σ ev = k) (s : Slot n) (hks : (slotList (fun i : Fin (n + 1) => sgOf ℓ π i) x)[k]? = some s) :
    Ex.eval σ A (phiEx n cv ev) = slotNum s := by
  have hs := eval_sgE lay72 (reads_of_reads72 hR) (.sub (.var cv) (.lit (17 * n + 11))) (σ := σ) (A := A)
  obtain ⟨c0, hcn⟩ : ∃ c0, c0 = cnNum x := ⟨_, rfl⟩
  rw [← hcn] at hc
  simp only [phiEx, famChain, sgcEx, Ex.eval, hc, hk, bndE, eval_tabX0, eval_aff, List.map_cons, List.map_nil] at hs ⊢
  cases x with
  | sign i =>
    simp only [cnNum] at hcn
    have h1 : c0 - (17 * n + 11) = i := by omega
    rw [h1] at hs
    simp (disch := omega) only [if_pos, if_neg]
    rw [hs]
    cases hsg : sgOf ℓ π i
    · simp [slotList, hsg] at hks
    · rw [if_pos (show sgCode Sg.pos < 2 by decide)]
      simp only [slotList, hsg] at hks
      have hk4 : k < 4 := by
        by_contra hh; rw [List.getElem?_eq_none (by simp; omega)] at hks; simp at hks
      interval_cases k <;> simp at hks <;> subst hks <;> simp [slotNum, vNum_eq, varIdx, cIdx] <;> omega
    · rw [if_neg (show ¬ sgCode Sg.neg < 2 by decide)]
      simp only [slotList, hsg] at hks
      have hk4 : k < 4 := by
        by_contra hh; rw [List.getElem?_eq_none (by simp; omega)] at hks; simp at hks
      interval_cases k <;> simp at hks <;> subst hks <;> simp [slotNum, vNum_eq, varIdx, cIdx] <;> omega
  | rng a =>
    simp only [cnNum] at hcn
    simp only [slotList] at hks
    have := varIdx_lt a
    simp (disch := omega) only [if_pos, if_neg]
    have hk4 : k < 4 := by
      by_contra hh; rw [List.getElem?_eq_none (by simp; omega)] at hks; simp at hks
    interval_cases k <;> simp at hks <;> subst hks <;>
      cases a <;> simp [slotNum, vNum_eq, varIdx, cIdx, bnd] at hcn ⊢ <;> (try split_ifs) <;> omega
  | _ =>
    simp only [cnNum] at hcn
    simp only [slotList] at hks
    simp (disch := omega) only [if_pos, if_neg]
    have hk4 : k < 10 := by
      by_contra hh; rw [List.getElem?_eq_none (by simp; omega)] at hks; simp at hks
    interval_cases k <;> simp at hks <;> subst hks <;> simp [slotNum, vNum_eq, varIdx, cIdx] <;> omega

end ECDLP.L83
end
