import Mathlib
import ECDLP.L35_Challenge
import ECDLP.L46_Cover

/-!
# L46 (1b): L35's oracle set `strings` = L40/L43's `Dec` (hence L30's `GenSet`)

`strings (n+1) (p,a,b,xR,yR,[])` is nonempty iff `Δ ≠ 0` and there is an affine point `R = (xR,yR)`
of `y² = x³ + a x + b` over `ZMod p` having an ordered generic decomposition into `n+1` factor-base
points (`x.val < B`), `B = sInf {B | p ≤ B^(n+1)}` in the sense of `Dec`.
-/
namespace ECDLP.L46

open Finset ECDLP.L40 ECDLP.L43

variable {p : ℕ} [Fact p.Prime]

theorem take_sum_eq {n : ℕ} {W : WeierstrassCurve.Affine (ZMod p)} (P : Fin (n + 1) → W.Point)
    (j : Fin n) : ((List.ofFn P).take j.succ.val).sum = ECDLP.L40.psum j.succ P := by
  rw [List.sum_take_ofFn]
  unfold ECDLP.L40.psum
  congr 1

theorem xc_ne_iff {W : WeierstrassCurve.Affine (ZMod p)} {S Q : W.Point} (hS : S ≠ 0) (hQ : Q ≠ 0) :
    xc W S ≠ xc W Q ↔ (ECDLP.L30.coord W S).1 ≠ (ECDLP.L30.coord W Q).1 := by
  cases S with
  | zero => exact absurd rfl hS
  | some x y h =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x' y' h' => simp [xc, ECDLP.L30.coord]

theorem xco_eq_coord {W : WeierstrassCurve.Affine (ZMod p)} (Q : W.Point) :
    xco W Q = (ECDLP.L30.coord W Q).1 := by
  cases Q <;> rfl

theorem mem_Dec {W : WeierstrassCurve.Affine (ZMod p)} (FB : ZMod p → Prop) (n : ℕ)
    (R : W.Point) (t : Fin (n + 1) → W.Point) :
    t ∈ Dec W FB n R ↔ (∀ i, t i ≠ 0 ∧ FB (xco W (t i))) ∧
      ECDLP.L40.Generic (xc W) t ∧ ∑ i, t i = R := by
  simp [Dec, fbase, Fintype.mem_piFinset]

/-- the generic-decomposition conditions of `strings`, in terms of `Dec` -/
theorem cond_iff {n : ℕ} (W : WeierstrassCurve.Affine (ZMod p)) (Bd : ℕ) (xR yR : ZMod p)
    (P : Fin (n + 1) → W.Point) :
    ((∀ i, P i ≠ 0 ∧ (ECDLP.L30.coord _ (P i)).1.val < Bd) ∧
      (∀ k : Fin (n + 1), 0 < k.val → (((List.ofFn P).take k).sum ≠ 0 ∧
        (ECDLP.L30.coord _ (((List.ofFn P).take k).sum)).1 ≠ (ECDLP.L30.coord _ (P k)).1)) ∧
      (List.ofFn P).sum ≠ 0 ∧ ECDLP.L30.coord _ ((List.ofFn P).sum) = (xR, yR)) ↔
    ((∃ R : W.Point, R ≠ 0 ∧ ECDLP.L30.coord _ R = (xR, yR) ∧
        P ∈ Dec W (fun x => x.val < Bd) n R)) := by
  have hs : (List.ofFn P).sum = ∑ i, P i := List.sum_ofFn
  rw [hs]
  have hk : ∀ k : Fin (n + 1), 0 < k.val → ∃ j : Fin n, j.succ = k := by
    intro k hk
    cases k using Fin.cases with
    | zero => simp at hk
    | succ j => exact ⟨j, rfl⟩
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨∑ i, P i, h3, h4, ?_⟩
    rw [mem_Dec]
    refine ⟨fun i => ⟨(h1 i).1, by rw [xco_eq_coord]; exact (h1 i).2⟩, ?_, rfl⟩
    intro j
    have := h2 j.succ (by simp)
    rw [take_sum_eq] at this
    refine ⟨this.1, ?_⟩
    rw [xc_ne_iff this.1 (h1 _).1]
    exact this.2
  · rintro ⟨R, hR0, hRc, hmem⟩
    rw [mem_Dec] at hmem
    obtain ⟨h1, h2, h3⟩ := hmem
    subst h3
    refine ⟨fun i => ⟨(h1 i).1, by rw [← xco_eq_coord]; exact (h1 i).2⟩, ?_, hR0, hRc⟩
    intro k hk0
    obtain ⟨j, rfl⟩ := hk k hk0
    have := h2 j
    rw [take_sum_eq]
    refine ⟨this.1, ?_⟩
    rw [← xc_ne_iff this.1 (h1 _).1]
    exact this.2


/-- **The oracle's set is the covered set.**  For the input `(p,a,b,xR,yR,[])` of L35's audit
statement, `strings (n+1)` is nonempty iff `Δ ≠ 0` and some affine `R = (xR,yR)` has an element of
`Dec` (ordered generic decompositions into `n+1` points with `x.val < B`, `B = sInf {B | p ≤ B^(n+1)}`),
i.e. (by `card_dec_eq_card_genSet`) iff L30's `GenSet` at `R` is nonempty. -/
theorem strings_nonempty_iff (n a b xR yR : ℕ) :
    (ECDLP.strings (n + 1) (p, a, b, xR, yR, [])).Nonempty ↔
      (⟨0, 0, 0, (a : ZMod p), (b : ZMod p)⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0 ∧
      ∃ R : (⟨0, 0, 0, (a : ZMod p), (b : ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine.Point,
        R ≠ 0 ∧ ECDLP.L30.coord _ R = ((xR : ZMod p), (yR : ZMod p)) ∧
        (Dec (⟨0, 0, 0, (a : ZMod p), (b : ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine
          (fun x => x.val < sInf {B | p ≤ B ^ (n + 1)}) n R).Nonempty := by
  have hp : p.Prime := Fact.out
  simp only [ECDLP.strings, dif_pos hp]
  constructor
  · rintro ⟨s, hΔ, P, hs, -, hP0, hgen, hsum0, hxy⟩
    refine ⟨hΔ, ∑ i, P i, ?_⟩
    have key := (cond_iff (n := n) _ (sInf {B | p ≤ B ^ (n + 1)})
      (xR : ZMod p) (yR : ZMod p) P).1 ⟨fun i => ?_, fun k hk => ?_, hsum0, ?_⟩
    · obtain ⟨R, hR0, hRc, hmem⟩ := key
      have : R = ∑ i, P i := ((mem_Dec _ n R P).1 hmem).2.2.symm
      subst this
      exact ⟨hR0, hRc, P, hmem⟩
    · have h := hP0 i
      revert h; generalize P i = Q; cases Q <;> exact id
    · have h := hgen k hk
      revert h
      generalize (List.take (↑k) (List.ofFn P)).sum = S
      generalize P k = Q
      cases S <;> cases Q <;> exact id
    · have h := hxy
      revert h
      generalize (List.ofFn P).sum = S
      cases S <;> exact id
  · rintro ⟨hΔ, R, hR0, hRc, t, ht⟩
    refine ⟨_, hΔ, t, rfl, List.nil_prefix, ?_⟩
    have := (cond_iff (n := n) _ (sInf {B | p ≤ B ^ (n + 1)})
      (xR : ZMod p) (yR : ZMod p) t).2 ⟨R, hR0, hRc, ht⟩
    refine ⟨fun i => ?_, fun k hk => ?_, this.2.2.1, ?_⟩
    · have h := this.1 i
      revert h; generalize t i = Q; cases Q <;> exact id
    · have h := this.2.1 k hk
      revert h
      generalize (List.take (↑k) (List.ofFn t)).sum = S
      generalize t k = Q
      cases S <;> cases Q <;> exact id
    · have h := this.2.2.2
      revert h
      generalize (List.ofFn t).sum = S
      cases S <;> exact id

end ECDLP.L46
