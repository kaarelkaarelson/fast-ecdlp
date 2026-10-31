import ECDLP.L79_Phi
import ECDLP.L73_Par

/-!
# L79 / Dig: closed forms of the digit expression `digE` for nodes whose parents form an interval of equal radix

`digE X fr tt` re-runs the decode of `nfE`, `nmE`, `parE` (depth 35).  For the gate kinds fa, mid, ib the parents of the node are an interval of global indices,
all with the same message count `Q`, and the node has one free value, so
`digE = (z / Q^(k - d0)) % Q` (`k` the index of the parent read, `d0` the first parent).  `eval_digE_interval` is the general statement;
`digC` is the shallow expression (depth 5) and `eval_digC_eq_digE` shows it equals `digE` in the same states.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L56 ECDLP.L68

section general
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : ECDLP.L56.PForced (ZMod m) ι} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u)

/-- the product of the radices `nA a j`, `j < d0 + t`, when the parents of `a` are the interval `[d0, d0 + n)` of equal radix `Q` -/
theorem pp_nA_interval (a : Fin g) {d0 n Q : ℕ} (hg : d0 + n ≤ g)
    (hpar : ∀ j : Fin g, e.symm j ∈ P.pa (e.symm a) ↔ (d0 ≤ j.val ∧ j.val < d0 + n))
    (hQ : ∀ j : Fin g, e.symm j ∈ P.pa (e.symm a) → Fintype.card (P.Msg (e.symm j)) = Q) :
    ∀ t ≤ n, pp (ECDLP.L64.nA P e a) (d0 + t) = Q ^ t := by
  have h1 : ∀ j < d0, ECDLP.L64.nA P e a j = 1 := by
    intro j hj
    by_cases hjg : j < g
    · have := ECDLP.L64.nA_npar P e (a := a) (k := ⟨j, hjg⟩) (by
        intro h; have := (hpar ⟨j, hjg⟩).1 h; simp at this; omega)
      simpa using this
    · simp [ECDLP.L64.nA, hjg]
  have h0 : ∀ d ≤ d0, pp (ECDLP.L64.nA P e a) d = 1 := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih => intro hd; simp only [pp]; rw [ih (by omega), h1 d (by omega)]
  intro t
  induction t with
  | zero => intro _; simpa using h0 d0 le_rfl
  | succ t ih =>
    intro ht
    have hj : d0 + t < g := by omega
    have := ECDLP.L64.nA_par P e (a := a) (k := ⟨d0 + t, hj⟩) ((hpar ⟨d0 + t, hj⟩).2 ⟨by simp, by simp; omega⟩)
    rw [show d0 + (t + 1) = (d0 + t) + 1 from rfl]
    simp only [pp]
    rw [ih (by omega)]
    have h2 := hQ ⟨d0 + t, hj⟩ ((hpar ⟨d0 + t, hj⟩).2 ⟨by simp, by simp; omega⟩)
    simp only at this
    rw [this, h2, pow_succ]

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

/-- `digE` evaluates to the arithmetic digit formula -/
theorem eval_digE_eq {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k) :
    Ex.eval σ A (digE X fr tt) =
      σ (u + 2) / Fintype.card (P.Free (e.symm a)) / pp (ECDLP.L64.nA P e a) k % Fintype.card (P.Msg (e.symm k)) := by
  simp only [digE, Ex.eval, eval_nf X hu hC hσ ha, eval_ppE X hu hC hσ hfr htt ha hk, eval_nm X hu hC hσ hk]

/-- **closed form of the digit** for a node with one free value whose parents are the interval `[d0, d0+n)` of equal radix `Q` -/
theorem eval_digE_interval {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k)
    {d0 n Q : ℕ} (hg : d0 + n ≤ g) (hnf : Fintype.card (P.Free (e.symm a)) = 1)
    (hpar : ∀ j : Fin g, e.symm j ∈ P.pa (e.symm a) ↔ (d0 ≤ j.val ∧ j.val < d0 + n))
    (hQ : ∀ j : Fin g, e.symm j ∈ P.pa (e.symm a) → Fintype.card (P.Msg (e.symm j)) = Q)
    (hk1 : d0 ≤ k.val) (hk2 : k.val < d0 + n) :
    Ex.eval σ A (digE X fr tt) = σ (u + 2) / Q ^ (k.val - d0) % Q := by
  rw [eval_digE_eq X hu hC hσ hfr htt ha hk, hnf, Nat.div_one,
    hQ k ((hpar k).2 ⟨hk1, hk2⟩)]
  have := pp_nA_interval (e := e) (P := P) a hg hpar hQ (k.val - d0) (by omega)
  rw [show d0 + (k.val - d0) = k.val by omega] at this
  rw [this]

end general

end ECDLP.L79
end
