import ECDLP.L79_Dig2

/-!
# L86 / Pp: closed forms of the digit of a node with TWO parents (the car gate)

`eval_digE_first`: the digit of the first parent (smaller global index) is `z % Q1`.
`eval_digE_second`: the digit of the second parent is `(z / Q1) % Q2`.
(`digE = z / nf / pp(nA a, k) % card Msg k`, with `pp` the product of the radices of the parents with smaller index.)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L56 ECDLP.L68 ECDLP.L79

theorem pp_one_of {n : ℕ → ℕ} : ∀ {k : ℕ}, (∀ j < k, n j = 1) → pp n k = 1
  | 0, _ => rfl
  | k + 1, h => by
    simp only [pp]
    rw [pp_one_of (fun j hj => h j (by omega)), h k (by omega)]

theorem pp_after {n : ℕ → ℕ} {i1 : ℕ} : ∀ t : ℕ, (∀ j < i1 + 1 + t, j ≠ i1 → n j = 1) → pp n (i1 + 1 + t) = n i1
  | 0, h => by
    simp only [Nat.add_zero, pp]
    rw [pp_one_of (fun j hj => h j (by omega) (by omega))]
    ring
  | t + 1, h => by
    rw [show i1 + 1 + (t + 1) = (i1 + 1 + t) + 1 by omega]
    simp only [pp]
    rw [pp_after t (fun j hj hne => h j (by omega) hne), h (i1 + 1 + t) (by omega) (by omega)]
    ring

section general
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : ECDLP.L56.PForced (ZMod m) ι} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u)

theorem nA_one_of (a : Fin g) {i1 i2 : ℕ}
    (hpar : ∀ x : Fin g, e.symm x ∈ P.pa (e.symm a) → x.val = i1 ∨ x.val = i2) (j : ℕ) (h1 : j ≠ i1) (h2 : j ≠ i2) :
    ECDLP.L64.nA P e a j = 1 := by
  by_cases hj : j < g
  · have : e.symm ⟨j, hj⟩ ∉ P.pa (e.symm a) := fun h => by
      rcases hpar _ h with h | h <;> simp at h <;> omega
    exact ECDLP.L64.nA_npar P e this
  · simp [ECDLP.L64.nA, hj]

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem eval_digE_first {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k)
    {i1 i2 Q1 : ℕ} (h12 : i1 < i2) (hnf : Fintype.card (P.Free (e.symm a)) = 1)
    (hpar : ∀ x : Fin g, e.symm x ∈ P.pa (e.symm a) → x.val = i1 ∨ x.val = i2)
    (hk1 : k.val = i1) (hQ : Fintype.card (P.Msg (e.symm k)) = Q1) :
    Ex.eval σ A (ECDLP.L68.digE X fr tt) = σ (u + 2) % Q1 := by
  rw [eval_digE_eq X hu hC hσ hfr htt ha hk, hnf, Nat.div_one, hQ, hk1,
    pp_one_of (fun j hj => nA_one_of a hpar j (by omega) (by omega)), Nat.div_one]

theorem eval_digE_second {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k)
    {i1 i2 Q1 Q2 : ℕ} (h12 : i1 < i2) (hnf : Fintype.card (P.Free (e.symm a)) = 1)
    (hpar : ∀ x : Fin g, e.symm x ∈ P.pa (e.symm a) → x.val = i1 ∨ x.val = i2)
    (hi1 : ∀ x : Fin g, x.val = i1 → e.symm x ∈ P.pa (e.symm a) ∧ Fintype.card (P.Msg (e.symm x)) = Q1)
    (hk2 : k.val = i2) (hQ : Fintype.card (P.Msg (e.symm k)) = Q2) :
    Ex.eval σ A (ECDLP.L68.digE X fr tt) = σ (u + 2) / Q1 % Q2 := by
  rw [eval_digE_eq X hu hC hσ hfr htt ha hk, hnf, Nat.div_one, hQ, hk2]
  have hg1 : i1 < g := by have := k.2; omega
  obtain ⟨hp1, hq1⟩ := hi1 ⟨i1, hg1⟩ rfl
  have hn1 : ECDLP.L64.nA P e a i1 = Q1 := by
    have := ECDLP.L64.nA_par P e (a := a) (k := ⟨i1, hg1⟩) hp1
    simp only at this
    rw [this, hq1]
  obtain ⟨t, ht⟩ : ∃ t, i2 = i1 + 1 + t := ⟨i2 - i1 - 1, by omega⟩
  rw [ht, pp_after t (fun j hj hne => nA_one_of a hpar j hne (by omega)), hn1]

end general
end ECDLP.L86
end
