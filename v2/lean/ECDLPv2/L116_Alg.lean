import Mathlib
import ECDLPv2.L116_Row

/-!
# L116 / Alg: the concrete row-collection rule satisfies the structural hypotheses of `mkSpec`

The algorithm: draw `Nd` points; while fewer than `f` rows are collected the next presented point is planted
(`ν • FB (#collected)`); a draw is *accepted* when the oracle's answer carries a decomposition; the matrix
rows are the first `f` accepted draws (planted rows `inl i`) and the next `s` accepted draws (ordinary rows `inr j`),
in order.  `Acc` = at least `f + s` of the `Nd` draws were accepted.  All structural hypotheses of `mkSpec` are proved.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L116

open ECDLP.L114 Finset

section alg
variable {G : Type*} [AddCommGroup G] {N f s Nd m : ℕ} [NeZero N] {O : Type*}

/-- draw `d` of the transcript `w` was accepted. -/
def accD (dec : O → Option (Fin m → Fin f)) (w : List O) (d : ℕ) : Prop :=
  (((w[d]?).bind dec).isSome = true)

instance (dec : O → Option (Fin m → Fin f)) (w : List O) : DecidablePred (accD dec w) :=
  fun d => by unfold accD; infer_instance

/-- number of collected rows in a history. -/
def nColl (dec : O → Option (Fin m → Fin f)) (h : List O) : ℕ := h.countP (fun o => (dec o).isSome)

theorem nColl_take (dec : O → Option (Fin m → Fin f)) (w : List O) :
    ∀ d, d ≤ w.length → nColl dec (w.take d) = Nat.count (accD dec w) d := by
  intro d
  induction d with
  | zero => intro _; simp [nColl]
  | succ d ih =>
    intro hd
    have hlt : d < w.length := hd
    rw [Nat.count_succ, ← ih (Nat.le_of_succ_le hd)]
    have : w.take (d + 1) = w.take d ++ [w[d]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl
    rw [nColl, this, List.countP_append]
    simp [nColl, accD, List.getElem?_eq_getElem hlt]

variable [NeZero Nd]

/-- row `r` is the `k`-th accepted draw, `k = i` for `inl i`, `k = f + j` for `inr j`. -/
def rowIdx : Fin f ⊕ Fin s → ℕ
  | Sum.inl i => (i : ℕ)
  | Sum.inr j => f + (j : ℕ)

theorem rowIdx_lt (r : Fin f ⊕ Fin s) : rowIdx r < f + s := by
  cases r with
  | inl i => have := i.2; simp only [rowIdx]; omega
  | inr j => have := j.2; simp only [rowIdx]; omega

theorem rowIdx_inj : Function.Injective (rowIdx (f := f) (s := s)) := by
  intro r r' h
  cases r with
  | inl i =>
    cases r' with
    | inl i' => simp [rowIdx] at h; exact congrArg _ (Fin.ext h)
    | inr j' => simp [rowIdx] at h; have := i.2; omega
  | inr j =>
    cases r' with
    | inl i' => simp [rowIdx] at h; have := i'.2; omega
    | inr j' => simp [rowIdx] at h; exact congrArg _ (Fin.ext h)

/-- the draw index of row `r`. -/
noncomputable def posAlg (dec : O → Option (Fin m → Fin f)) (w : List O) (r : Fin f ⊕ Fin s) : Fin Nd :=
  if h : Nat.nth (accD dec w) (rowIdx r) < Nd then ⟨_, h⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne Nd)⟩

/-- acceptance: the transcript has length `Nd` and at least `f + s` accepted draws. -/
def AccAlg (dec : O → Option (Fin m → Fin f)) (w : List O) : Prop :=
  w.length = Nd ∧ f + s ≤ Nat.count (accD dec w) Nd

theorem accD_finite (dec : O → Option (Fin m → Fin f)) (w : List O) (hw : w.length = Nd) :
    (Set.ofPred (accD dec w)).Finite := by
  refine (Set.finite_Iio Nd).subset ?_
  intro d hd
  have : accD dec w d := hd
  unfold accD at this
  by_contra hnd
  have hge : w.length ≤ d := by rw [hw]; exact not_lt.1 hnd
  rw [List.getElem?_eq_none hge] at this
  simp at this

theorem nth_lt_card (dec : O → Option (Fin m → Fin f)) (w : List O) (hA : AccAlg (Nd := Nd) (f := f) (s := s) dec w)
    (r : Fin f ⊕ Fin s) (hf : (Set.ofPred (accD dec w)).Finite) : rowIdx r < hf.toFinset.card :=
  lt_of_lt_of_le (lt_of_lt_of_le (rowIdx_lt r) hA.2) (Nat.count_le_card hf Nd)

theorem posAlg_val (dec : O → Option (Fin m → Fin f)) (w : List O) (hA : AccAlg (Nd := Nd) (f := f) (s := s) dec w)
    (r : Fin f ⊕ Fin s) : ((posAlg (Nd := Nd) dec w r : Fin Nd) : ℕ) = Nat.nth (accD dec w) (rowIdx r) := by
  have hlt : Nat.nth (accD dec w) (rowIdx r) < Nd :=
    Nat.nth_lt_of_lt_count (lt_of_lt_of_le (rowIdx_lt r) hA.2)
  simp [posAlg, hlt]

theorem posAlg_acc (dec : O → Option (Fin m → Fin f)) (w : List O) (hA : AccAlg (Nd := Nd) (f := f) (s := s) dec w)
    (r : Fin f ⊕ Fin s) : accD dec w ((posAlg (Nd := Nd) dec w r : Fin Nd) : ℕ) := by
  have hf := accD_finite dec w hA.1
  rw [posAlg_val dec w hA r]
  exact Nat.nth_mem _ (fun hf' => nth_lt_card dec w hA r hf')

theorem nColl_pos (dec : O → Option (Fin m → Fin f)) (w : List O) (hA : AccAlg (Nd := Nd) (f := f) (s := s) dec w)
    (r : Fin f ⊕ Fin s) : nColl dec (w.take (posAlg (Nd := Nd) dec w r)) = rowIdx r := by
  have hf := accD_finite dec w hA.1
  rw [nColl_take dec w _ (by have := (posAlg (Nd := Nd) dec w r).2; rw [hA.1]; omega), posAlg_val dec w hA r]
  exact Nat.count_nth_of_lt_card_finite hf (nth_lt_card dec w hA r hf)

theorem posAlg_inj (dec : O → Option (Fin m → Fin f)) (w : List O) (hA : AccAlg (Nd := Nd) (f := f) (s := s) dec w) :
    Function.Injective (posAlg (s := s) (Nd := Nd) dec w) := by
  have hf := accD_finite dec w hA.1
  intro r r' h
  have h1 := posAlg_val dec w hA r
  have h2 := posAlg_val dec w hA r'
  rw [h] at h1
  have := Nat.nth_injOn hf (nth_lt_card dec w hA r hf) (nth_lt_card dec w hA r' hf) (h1.symm.trans h2)
  exact rowIdx_inj this

/-- **The algorithm's round**, a `RoundSpec` whose row relations are proved. -/
noncomputable def algSpec (V : Fin 4 → G) (hN : ∀ g : G, N • g = 0) (FB : Fin f → G)
    (Orc : List O → G → O) (dec : O → Option (Fin m → Fin f)) (t0 : Fin m → Fin f)
    (hOrc : ∀ (h : List O) (R : G) (t : Fin m → Fin f), dec (Orc h R) = some t → ∑ j, FB (t j) = R) :
    RoundSpec V hN f s Nd O :=
  mkSpec V hN FB (nColl dec) Orc dec t0 hOrc (AccAlg dec) (posAlg dec)
    (fun w hA r => by
      have := posAlg_acc dec w hA r
      unfold accD at this
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 this
      exact ⟨t, ht⟩)
    (fun w hA i => nColl_pos dec w hA (Sum.inl i))
    (fun w hA j => by rw [nColl_pos dec w hA (Sum.inr j)]; simp [rowIdx])
    (fun w hA => posAlg_inj (s := s) dec w hA)

/-- **Row relations of the algorithm, proved** (this was the field `row_rel`, assumed in L114). -/
theorem algSpec_row_rel (V : Fin 4 → G) (hN : ∀ g : G, N • g = 0) (FB : Fin f → G)
    (Orc : List O → G → O) (dec : O → Option (Fin m → Fin f)) (t0 : Fin m → Fin f)
    (hOrc : ∀ (h : List O) (R : G) (t : Fin m → Fin f), dec (Orc h R) = some t → ∑ j, FB (t j) = R) :
    ∀ (ν : ℤ) (a : Fin Nd → (Fin 4 → ZMod N)),
      (algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).Acc
        (trans (evG V hN) Orc ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).shift ν) [] Nd a) →
      ∀ i, ∑ F, relMat ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).Ttop
          (trans (evG V hN) Orc ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).shift ν) [] Nd a))
        ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).Rint
          (trans (evG V hN) Orc ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).shift ν) [] Nd a)) ν i F •
          (algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).FB F =
        evG V hN (a ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).pos
          (trans (evG V hN) Orc ((algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).shift ν) [] Nd a) i)) :=
  (algSpec (s := s) (Nd := Nd) V hN FB Orc dec t0 hOrc).row_rel

end alg
end ECDLP.L116
