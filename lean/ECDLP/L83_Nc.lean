import ECDLP.L83_Tab

/-!
# L83 / Nc: `nc c` (number of used slots of identity `c`) as an expression of `c = sigma (u+22)` and the prefix
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 Slot Cst

section
variable (n u : ℕ)

/-- `nc c`: 4 (`rng`), 3 (`uEq`), 9 (`curve`), 3 (`s0x..sRy`), 7, 9, 8, 9 (`e0..e3`), and `0` or `4` (`sign`, by the sign requirement) -/
def ncEx : Ex :=
  famChain n (u + 22) (.lit 4) (.lit 3) (.lit 9) (.lit 3) (.lit 3) (.lit 3) (.lit 3) (.lit 7) (.lit 9) (.lit 8) (.lit 9)
    (.ifLt (.lit 0) (sgcEx n (u + 22)) (.lit 4) (.lit 0))

variable {n u} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem eval_ncEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (x : Cn n) (hc : σ (u + 22) = cnNum x) :
    Ex.eval σ A (ncEx n u) = (slotList (fun i : Fin (n + 1) => sgOf ℓ π i) x).length := by
  have hs := eval_sgE lay72 (reads_of_reads72 hR) (.sub (.var (u + 22)) (.lit (17 * n + 11))) (σ := σ) (A := A)
  obtain ⟨c0, hcn⟩ : ∃ c0, c0 = cnNum x := ⟨_, rfl⟩
  rw [← hcn] at hc
  simp only [ncEx, famChain, sgcEx, Ex.eval, hc] at hs ⊢
  cases x with
  | sign i =>
    simp only [cnNum] at hcn
    have h1 : c0 - (17 * n + 11) = i := by omega
    rw [h1] at hs
    have := i.2
    simp (disch := omega) only [if_pos, if_neg]
    rw [hs]
    simp only [slotList]
    cases hsg : sgOf ℓ π i <;> simp [sgCode]
  | rng a =>
    simp only [cnNum] at hcn
    simp only [slotList, List.length_cons, List.length_nil]
    have := varIdx_lt a
    simp (disch := omega) only [if_pos, if_neg]
  | uEq i =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := i.2; simp (disch := omega) only [if_pos, if_neg]
  | curve i =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := i.2; simp (disch := omega) only [if_pos, if_neg]
  | s0x => simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]; simp (disch := omega) only [if_pos, if_neg]
  | s0y => simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]; simp (disch := omega) only [if_pos, if_neg]
  | sRx => simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]; simp (disch := omega) only [if_pos, if_neg]
  | sRy => simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]; simp (disch := omega) only [if_pos, if_neg]
  | e0 k =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := k.2; simp (disch := omega) only [if_pos, if_neg]
  | e1 k =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := k.2; simp (disch := omega) only [if_pos, if_neg]
  | e2 k =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := k.2; simp (disch := omega) only [if_pos, if_neg]
  | e3 k =>
    simp only [cnNum] at hcn; simp only [slotList, List.length_cons, List.length_nil]
    have := k.2; simp (disch := omega) only [if_pos, if_neg]

end
end ECDLP.L83
end
