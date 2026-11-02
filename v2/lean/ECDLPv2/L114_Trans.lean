import Mathlib

/-!
# L114 / Trans: the oracle learns nothing about the planted shift `ν` (paper Lemma P1)

Draw `t` is `R_t = ev (a_t) + c(h_{t-1})`, where `a_t ∈ A` is fresh uniform, `ev : A →+ G` is onto,
`h_{t-1}` the list of previous oracle answers, and `c` an arbitrary history-dependent shift (the planted
`ν • F_{i(t)}`, the index `i(t)` being a function of the history).  The oracle `Orc` may be stateful
(sees the history).  Then the number of tag sequences producing a given answer transcript does not depend
on `c` (hence not on `ν`).  Consequently any event about the transcript has the same probability for every `ν`.
-/
namespace ECDLP.L114

open Finset

section trans
variable {A G O : Type*} [AddCommGroup A] [AddCommGroup G]

/-- answer transcript of `n` draws starting from history `h`. -/
def trans (ev : A →+ G) (Orc : List O → G → O) (c : List O → G) : List O → (n : ℕ) → (Fin n → A) → List O
  | _, 0, _ => []
  | h, n + 1, a =>
      Orc h (ev (a 0) + c h) :: trans ev Orc c (h ++ [Orc h (ev (a 0) + c h)]) n (Fin.tail a)

/-- number of preimages of a point under `a ↦ ev a + s` is independent of the shift (onto `ev`). -/
theorem shift_count [Fintype A] (ev : A →+ G) (hsurj : Function.Surjective ev)
    (P : G → Prop) [DecidablePred P] (s s' : G) :
    (univ.filter (fun a : A => P (ev a + s))).card = (univ.filter (fun a : A => P (ev a + s'))).card := by
  obtain ⟨t, ht⟩ := hsurj (s - s')
  refine Finset.card_bij (fun a _ => a + t) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [map_add, ht, show ev a + (s - s') + s' = ev a + s by abel]; exact ha
  · intro a _ b _ h; exact add_right_cancel h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    refine ⟨b - t, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, map_sub, ht]
    rw [show ev b - (s - s') + s = ev b + s' by abel]; exact hb

open Classical in
/-- one-step recurrence for the transcript count -/
theorem trans_count_succ [Fintype A] [DecidableEq O] (ev : A →+ G)
    (Orc : List O → G → O) (cc : List O → G) (n : ℕ) (h : List O) (w0 : O) (w' : List O) :
    (univ.filter (fun a : Fin (n + 1) → A => trans ev Orc cc h (n + 1) a = w0 :: w')).card =
      (univ.filter (fun a0 : A => Orc h (ev a0 + cc h) = w0)).card *
      (univ.filter (fun r : Fin n → A => trans ev Orc cc (h ++ [w0]) n r = w')).card := by
  simp only [Finset.card_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => A), Fintype.sum_prod_type,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  by_cases ho : Orc h (ev a0 + cc h) = w0
  · subst ho
    simp [trans, Fin.consEquiv, Fin.tail_cons, Fin.cons_zero]
  · simp [trans, Fin.consEquiv, Fin.tail_cons, Fin.cons_zero, ho]

open Classical in
/-- **P1 (counting form).** -/
theorem trans_count_indep [Fintype A] [DecidableEq O] (ev : A →+ G) (hsurj : Function.Surjective ev)
    (Orc : List O → G → O) (c c' : List O → G) :
    ∀ (n : ℕ) (h w : List O),
      (univ.filter (fun a : Fin n → A => trans ev Orc c h n a = w)).card =
      (univ.filter (fun a : Fin n → A => trans ev Orc c' h n a = w)).card := by
  intro n
  induction n with
  | zero => intro h w; simp [trans]
  | succ n ih =>
    intro h w
    cases w with
    | nil => simp [trans]
    | cons w0 w' =>
      rw [trans_count_succ ev Orc c n h w0 w', trans_count_succ ev Orc c' n h w0 w', ih (h ++ [w0]) w']
      congr 1
      exact shift_count ev hsurj (fun x => Orc h x = w0) (c h) (c' h)

end trans
end ECDLP.L114
