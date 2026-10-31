import ECDLP.L30_Step

/-!
# L30 / Chain: chained generic additions

For points `P 0, …, P n` (ℕ-indexed, nonsingular) and partial-sum witnesses `S`, `w`, `l`,
`Chain` is the conjunction of: `S 0 = P 0` and one `StepC` per addition `S k + P (k+1) = S (k+1)`.
We prove: the chain holds with `S n = R` iff every partial addition is generic (the partial sum is
affine and its x-coordinate differs from that of the next point) and the sum equals `R`;
witnesses are unique.
-/

set_option linter.unusedSectionVars false

namespace ECDLP.L30

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Affine coordinates of a point (the point at infinity is sent to `(0,0)`; only used on affine
points). -/
def coord : W.Point → F × F
  | .zero => (0, 0)
  | .some x y _ => (x, y)

open Classical in
/-- The point with the given coordinates if it is nonsingular, and `0` otherwise. -/
noncomputable def ptOf (q : F × F) : W.Point :=
  if h : W.Nonsingular q.1 q.2 then Point.some q.1 q.2 h else Point.zero

variable {W}

theorem ptOf_of_ns {q : F × F} (h : W.Nonsingular q.1 q.2) :
    ptOf W q = Point.some q.1 q.2 h := by
  unfold ptOf; rw [dif_pos h]

theorem ptOf_ne_zero {q : F × F} (h : W.Nonsingular q.1 q.2) : ptOf W q ≠ 0 := by
  rw [ptOf_of_ns h]; exact Point.some_ne_zero h

theorem coord_ptOf {q : F × F} (h : W.Nonsingular q.1 q.2) : coord W (ptOf W q) = q := by
  rw [ptOf_of_ns h]; rfl

/-- One step, soundness at the level of points. -/
theorem coord_step_sound {A B : W.Point} (hA : A ≠ 0) (hB : B ≠ 0) {w l : F} {S : F × F}
    (h : StepC W (coord W A).1 (coord W A).2 (coord W B).1 (coord W B).2 w l S.1 S.2) :
    A + B ≠ 0 ∧ coord W (A + B) = S ∧ (coord W A).1 ≠ (coord W B).1 := by
  cases A with
  | zero => exact absurd rfl hA
  | some xa ya ha =>
    cases B with
    | zero => exact absurd rfl hB
    | some xb yb hb =>
      obtain ⟨hne, -, -, hS, hEq⟩ := (stepC_iff W ha hb w l S.1 S.2).1 h
      refine ⟨?_, ?_, hne⟩
      · rw [← hEq]; exact Point.some_ne_zero hS
      · rw [← hEq]; rfl

/-- One step, completeness at the level of points. -/
theorem coord_step_complete {A B : W.Point} (hA : A ≠ 0) (hB : B ≠ 0)
    (hx : (coord W A).1 ≠ (coord W B).1) :
    A + B ≠ 0 ∧
      StepC W (coord W A).1 (coord W A).2 (coord W B).1 (coord W B).2
        (((coord W B).1 - (coord W A).1)⁻¹)
        (W.slope (coord W A).1 (coord W B).1 (coord W A).2 (coord W B).2)
        (coord W (A + B)).1 (coord W (A + B)).2 := by
  cases A with
  | zero => exact absurd rfl hA
  | some xa ya ha =>
    cases B with
    | zero => exact absurd rfl hB
    | some xb yb hb =>
      have hx' : xa ≠ xb := hx
      have hsum := Point.add_of_X_ne (h₁ := ha) (h₂ := hb) hx'
      refine ⟨?_, ?_⟩
      · rw [hsum]; exact Point.some_ne_zero _
      · simp only [coord]
        rw [stepC_iff W ha hb]
        refine ⟨hx', rfl, rfl, ?_⟩
        rw [hsum]
        exact ⟨_, rfl⟩

/-! ### The ℕ-indexed chain -/

/-- Points `Q i = ptOf (P i)`. -/
noncomputable def QP (W : WeierstrassCurve.Affine F) (P : ℕ → F × F) : ℕ → W.Point :=
  fun i => ptOf W (P i)

/-- Partial sums `Q 0 + … + Q k` in `W.Point`. -/
def psum (Q : ℕ → W.Point) (k : ℕ) : W.Point := ∑ i ∈ Finset.range (k + 1), Q i

theorem psum_zero (Q : ℕ → W.Point) : psum Q 0 = Q 0 := by simp [psum]

theorem psum_succ (Q : ℕ → W.Point) (k : ℕ) : psum Q (k + 1) = psum Q k + Q (k + 1) := by
  unfold psum; rw [Finset.sum_range_succ _ (k + 1)]

variable (W)

/-- The constraint chain: `S 0 = P 0` and, for each `k < n`, a generic addition
`S k + P (k+1) = S (k+1)` with witnesses `w k`, `l k`. -/
def Chain (P S : ℕ → F × F) (w l : ℕ → F) (n : ℕ) : Prop :=
  S 0 = P 0 ∧ ∀ k < n, StepC W (S k).1 (S k).2 (P (k + 1)).1 (P (k + 1)).2 (w k) (l k)
    (S (k + 1)).1 (S (k + 1)).2

/-- Genericity of all partial additions: the partial sum is affine and its x-coordinate differs
from the x-coordinate of the next point. -/
def Generic (P : ℕ → F × F) (n : ℕ) : Prop :=
  ∀ k < n, psum (QP W P) k ≠ 0 ∧ (coord W (psum (QP W P) k)).1 ≠ (P (k + 1)).1

variable {W}

theorem chain_sound {P S : ℕ → F × F} {w l : ℕ → F} {n : ℕ}
    (hP : ∀ i ≤ n, W.Nonsingular (P i).1 (P i).2) (h : Chain W P S w l n) :
    ∀ k ≤ n, psum (QP W P) k ≠ 0 ∧ coord W (psum (QP W P) k) = S k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [psum_zero]
    exact ⟨ptOf_ne_zero (hP 0 (Nat.zero_le _)), by
      rw [h.1]; exact coord_ptOf (hP 0 (Nat.zero_le _))⟩
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep := h.2 k (by omega)
    rw [psum_succ]
    have hB : QP W P (k + 1) ≠ 0 := ptOf_ne_zero (hP (k + 1) hk)
    have hcB : coord W (QP W P (k + 1)) = P (k + 1) := coord_ptOf (hP (k + 1) hk)
    rw [← ih2, ← hcB] at hstep
    obtain ⟨a1, a2, -⟩ := coord_step_sound ih1 hB hstep
    exact ⟨a1, a2⟩

theorem chain_generic {P S : ℕ → F × F} {w l : ℕ → F} {n : ℕ}
    (hP : ∀ i ≤ n, W.Nonsingular (P i).1 (P i).2) (h : Chain W P S w l n) :
    Generic W P n := by
  intro k hk
  obtain ⟨ih1, ih2⟩ := chain_sound hP h k (by omega)
  have hstep := h.2 k hk
  have hB : QP W P (k + 1) ≠ 0 := ptOf_ne_zero (hP (k + 1) (by omega))
  have hcB : coord W (QP W P (k + 1)) = P (k + 1) := coord_ptOf (hP (k + 1) (by omega))
  rw [← ih2, ← hcB] at hstep
  obtain ⟨-, -, a3⟩ := coord_step_sound ih1 hB hstep
  refine ⟨ih1, ?_⟩
  rw [hcB] at a3
  exact a3

/-- Canonical witnesses. -/
noncomputable def canS (W : WeierstrassCurve.Affine F) (P : ℕ → F × F) : ℕ → F × F :=
  fun k => coord W (psum (QP W P) k)

noncomputable def canW (W : WeierstrassCurve.Affine F) (P : ℕ → F × F) : ℕ → F :=
  fun k => ((P (k + 1)).1 - (canS W P k).1)⁻¹

noncomputable def canL (W : WeierstrassCurve.Affine F) (P : ℕ → F × F) : ℕ → F :=
  fun k => W.slope (canS W P k).1 (P (k + 1)).1 (canS W P k).2 (P (k + 1)).2

theorem chain_complete {P : ℕ → F × F} {n : ℕ}
    (hP : ∀ i ≤ n, W.Nonsingular (P i).1 (P i).2) (hG : Generic W P n) :
    Chain W P (canS W P) (canW W P) (canL W P) n := by
  refine ⟨?_, ?_⟩
  · simp only [canS]
    rw [psum_zero]
    exact coord_ptOf (hP 0 (Nat.zero_le _))
  · intro k hk
    obtain ⟨g1, g2⟩ := hG k hk
    have hB : QP W P (k + 1) ≠ 0 := ptOf_ne_zero (hP (k + 1) (by omega))
    have hcB : coord W (QP W P (k + 1)) = P (k + 1) := coord_ptOf (hP (k + 1) (by omega))
    have := (coord_step_complete g1 hB (by rw [hcB]; exact g2)).2
    rw [hcB] at this
    have hs : canS W P (k + 1) = coord W (psum (QP W P) k + QP W P (k + 1)) := by
      simp only [canS]; rw [psum_succ]
    rw [hs]
    exact this

/-- Uniqueness of witnesses. -/
theorem chain_unique {P S S' : ℕ → F × F} {w l w' l' : ℕ → F} {n : ℕ}
    (hP : ∀ i ≤ n, W.Nonsingular (P i).1 (P i).2) (h : Chain W P S w l n)
    (h' : Chain W P S' w' l' n) :
    (∀ k ≤ n, S k = S' k) ∧ (∀ k < n, w k = w' k ∧ l k = l' k) := by
  have hS : ∀ k ≤ n, S k = S' k := fun k hk => by
    rw [← (chain_sound hP h k hk).2, (chain_sound hP h' k hk).2]
  refine ⟨hS, fun k hk => ?_⟩
  have a := h.2 k hk
  have b := h'.2 k hk
  rw [← hS k hk.le, ← hS (k + 1) hk] at b
  obtain ⟨e1, e2, -, -⟩ := stepC_unique W a b
  exact ⟨e1, e2⟩

/-- **chained generic additions = sum of the points**.**
The chain constraints with final partial sum `R` are satisfiable iff every partial addition is
generic and the sum of the points is `R`; and then the witnesses are the canonical ones. -/
theorem chain_iff {P : ℕ → F × F} {n : ℕ} {R : F × F}
    (hP : ∀ i ≤ n, W.Nonsingular (P i).1 (P i).2) (hR : W.Nonsingular R.1 R.2) :
    (∃ S w l, Chain W P S w l n ∧ S n = R) ↔
      (Generic W P n ∧ psum (QP W P) n = ptOf W R) := by
  constructor
  · rintro ⟨S, w, l, h, hn⟩
    refine ⟨chain_generic hP h, ?_⟩
    obtain ⟨hne, h2⟩ := chain_sound hP h n le_rfl
    have h2' : coord W (psum (QP W P) n) = R := h2.trans hn
    revert hne h2'
    generalize psum (QP W P) n = T
    intro hne h2'
    cases T with
    | zero => exact absurd rfl hne
    | some x y hs =>
      simp only [coord] at h2'
      subst h2'
      rw [ptOf_of_ns hs]
  · rintro ⟨hG, hsum⟩
    refine ⟨canS W P, canW W P, canL W P, chain_complete hP hG, ?_⟩
    simp only [canS]
    rw [hsum]
    exact coord_ptOf hR

end ECDLP.L30
