import Mathlib
import ECDLP.L46_Rel
import ECDLP.L46_Util

/-!
# L46 (2b): `SemaevNondeg` ⟹ the average-energy bound (`AvgEnergyBound`) via L40's skeleton
-/
namespace ECDLP.L46

open Finset ECDLP.L40 ECDLP.L43

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem xco_ptOf {W : WeierstrassCurve.Affine K} {q : K × K} (h : W.Nonsingular q.1 q.2) :
    xco W (ECDLP.L30.ptOf W q) = q.1 := by
  rw [ECDLP.L30.ptOf_of_ns h]; rfl

/-- Semaev vanishing transports to L40's `hsem` for our `Rel`. -/
theorem hsem_of {m : ℕ} {T : Finset K} (f : (Fin (2 * m) → K) → MvPolynomial (Fin 2) K)
    (hvan : ∀ A B : K, disc A B ≠ 0 → ∀ P : Fin (2 * m) → (shortW A B).Point,
      (∀ i, P i ≠ 0 ∧ xco _ (P i) ∈ T) → ∑ i, P i = 0 →
        MvPolynomial.eval ![A, B] (f (fun i => xco _ (P i))) = 0)
    (θ : Fin 2 → K) (u : Fin (2 * m) → K × K) (hu : ∀ i, u i ∈ curvePts θ T) (hR : Rel m θ u) :
    MvPolynomial.eval θ (f (fun i => (u i).1)) = 0 := by
  obtain ⟨hd, hns, hsum⟩ := hR
  set W := shortW (θ 0) (θ 1) with hW
  let P' : Fin (2 * m) → W.Point := fun i =>
    if (i : ℕ) < m then ECDLP.L30.ptOf W (u i) else -ECDLP.L30.ptOf W (u i)
  have hne : ∀ i, P' i ≠ 0 := by
    intro i
    have := ECDLP.L30.ptOf_ne_zero (hns i)
    simp only [P']; split_ifs
    · exact this
    · exact neg_ne_zero.2 this
  have hx : ∀ i, xco _ (P' i) = (u i).1 := by
    intro i
    simp only [P']; split_ifs
    · exact xco_ptOf (hns i)
    · rw [xco_neg]; exact xco_ptOf (hns i)
  have hT : ∀ i, (u i).1 ∈ T := by
    intro i
    have := hu i
    simp only [curvePts, mem_filter, mem_product] at this
    exact this.1.1
  have hsum0 : ∑ i, P' i = 0 := by
    rw [sum_split]
    have h1 : ∀ j : Fin m, P' (lo m j) = ECDLP.L30.ptOf W (u (lo m j)) := by
      intro j; simp only [P', lo]; rw [if_pos j.isLt]
    have h2 : ∀ j : Fin m, P' (hi m j) = -ECDLP.L30.ptOf W (u (hi m j)) := by
      intro j; simp only [P', hi]; rw [if_neg (by omega)]
    simp only [h1, h2, sum_neg_distrib]
    rw [hsum]; exact add_neg_cancel _
  have := hvan (θ 0) (θ 1) hd P' (fun i => ⟨hne i, by rw [hx]; exact hT i⟩) hsum0
  have e : (fun i => xco _ (P' i)) = fun i => (u i).1 := funext hx
  rw [e] at this
  have eθ : (![θ 0, θ 1] : Fin 2 → K) = θ := by
    funext i; fin_cases i <;> rfl
  rwa [eθ] at this


/-- coordinates of a pair of `m`-tuples of points, as a `2m`-tuple -/
def mkU {W : WeierstrassCurve.Affine K} {m : ℕ} (P Q : Fin m → W.Point) : Fin (2 * m) → K × K :=
  fun i => if h : (i : ℕ) < m then ECDLP.L30.coord W (P ⟨i, h⟩)
    else ECDLP.L30.coord W (Q ⟨i - m, by omega⟩)

theorem mkU_lo {W : WeierstrassCurve.Affine K} {m : ℕ} (P Q : Fin m → W.Point) (j : Fin m) :
    mkU P Q (lo m j) = ECDLP.L30.coord W (P j) := by
  simp [mkU, lo, j.isLt]

theorem mkU_hi {W : WeierstrassCurve.Affine K} {m : ℕ} (P Q : Fin m → W.Point) (j : Fin m) :
    mkU P Q (hi m j) = ECDLP.L30.coord W (Q j) := by
  simp [mkU, hi]

theorem mkU_cases {W : WeierstrassCurve.Affine K} {m : ℕ} (P Q : Fin m → W.Point)
    (i : Fin (2 * m)) : (∃ j, mkU P Q i = ECDLP.L30.coord W (P j)) ∨
      ∃ j, mkU P Q i = ECDLP.L30.coord W (Q j) := by
  by_cases h : (i : ℕ) < m
  · exact Or.inl ⟨⟨i, h⟩, by simp [mkU, h]⟩
  · exact Or.inr ⟨⟨i - m, by omega⟩, by simp [mkU, h]⟩

open Classical in
/-- Each energy pair over a nonsingular curve gives a point of `badSet` over `θ = (A,B)`. -/
theorem eng_le_fiber (hK : ringChar K ≠ 2) (T : Finset K) (n : ℕ) (A B : K) (hd : disc A B ≠ 0) :
    Eng T n A B ≤ ((badSet (n + 1) T (Rel (n + 1))).filter
      (fun x => x.1 = ![A, B])).card := by
  unfold Eng energy
  refine card_le_card_of_injOn (fun pq : (Fin (n + 1) → (shortW A B).Point) × (Fin (n + 1) → (shortW A B).Point) =>
    (![A, B], mkU pq.1 pq.2)) ?_ ?_
  · intro pq hpq
    simp only [coe_filter, mem_product, Fintype.mem_piFinset, Set.mem_ofPred_eq] at hpq
    obtain ⟨⟨hP, hQ⟩, hsum⟩ := hpq
    have hfb : ∀ R ∈ fb A B T, R ≠ 0 ∧ xco _ R ∈ T := by
      intro R hR
      simp only [fb, mem_filter, mem_univ, true_and] at hR
      refine ⟨?_, hR.2⟩
      intro h0; rw [h0] at hR; simp [xc] at hR
    have hall : ∀ i, ∃ R ∈ fb A B T, mkU pq.1 pq.2 i = ECDLP.L30.coord _ R := by
      intro i
      rcases mkU_cases pq.1 pq.2 i with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨_, hP j, hj⟩
      · exact ⟨_, hQ j, hj⟩
    simp only [coe_filter, badSet, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · intro i
      obtain ⟨R, hR, hi⟩ := hall i
      obtain ⟨hR0, hRT⟩ := hfb R hR
      rw [hi]
      cases R with
      | zero => exact absurd rfl hR0
      | some x y h =>
        simp only [curvePts, mem_filter, mem_product, mem_univ, and_true]
        refine ⟨hRT, ?_⟩
        exact (shortW_equation A B x y).1 h.1
    · refine ⟨hd, ?_, ?_⟩
      · intro i
        obtain ⟨R, hR, hi⟩ := hall i
        rw [hi]
        exact ns_coord (hfb R hR).1
      · show ∑ j : Fin (n + 1), ECDLP.L30.ptOf (shortW A B) (mkU pq.1 pq.2 (lo (n + 1) j))
          = ∑ j : Fin (n + 1), ECDLP.L30.ptOf (shortW A B) (mkU pq.1 pq.2 (hi (n + 1) j))
        simp only [mkU_lo, mkU_hi]
        have h1 : ∀ j : Fin (n + 1), ECDLP.L30.ptOf (shortW A B) (ECDLP.L30.coord _ (pq.1 j)) = pq.1 j :=
          fun j => ptOf_coord (hfb _ (hP j)).1
        have h2 : ∀ j : Fin (n + 1), ECDLP.L30.ptOf (shortW A B) (ECDLP.L30.coord _ (pq.2 j)) = pq.2 j :=
          fun j => ptOf_coord (hfb _ (hQ j)).1
        simp only [h1, h2]
        exact hsum
  · intro pq hpq pq' hpq' h
    simp only [coe_filter, mem_product, Fintype.mem_piFinset, Set.mem_ofPred_eq] at hpq hpq'
    have hu : mkU pq.1 pq.2 = mkU pq'.1 pq'.2 := (Prod.mk.inj h).2
    have hne : ∀ R ∈ fb A B T, R ≠ 0 := by
      intro R hR h0
      simp only [fb, mem_filter, mem_univ, true_and] at hR
      rw [h0] at hR; simp [xc] at hR
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · have := congrFun hu (lo (n + 1) j)
      rw [mkU_lo, mkU_lo] at this
      exact coord_inj (hne _ (hpq.1.1 j)) (hne _ (hpq'.1.1 j)) this
    · have := congrFun hu (hi (n + 1) j)
      rw [mkU_hi, mkU_hi] at this
      exact coord_inj (hne _ (hpq.1.2 j)) (hne _ (hpq'.1.2 j)) this


/-- **`AvgEnergyBound n T M`** (the hypothesis `hT1` of L43, a statement about Mathlib's group law):
`∑_{(A,B), Δ ≠ 0} #{(P,Q) ∈ F_{A,B}^{n+1} × F_{A,B}^{n+1} | ∑ P = ∑ Q} ≤ M q²`, where
`F_{A,B}` = nonzero points of `(shortW A B).Point` with `x ∈ T`. -/
def AvgEnergyBound (n : ℕ) (T : Finset K) (M : ℝ) : Prop :=
  ∑ p : K × K, (if disc p.1 p.2 = 0 then (0 : ℝ) else (Eng T n p.1 p.2 : ℝ))
    ≤ M * (Fintype.card K : ℝ) ^ 2

/-- the constant `M` -/
noncomputable def Mconst (K : Type*) [Fintype K] (n : ℕ) (T : Finset K) (D : ℕ) : ℝ :=
  (dfac (n + 1) : ℝ) * 4 ^ (n + 1) * (T.card : ℝ) ^ (n + 1)
    + 4 ^ (n + 1) * D * (T.card : ℝ) ^ (2 * (n + 1)) / (Fintype.card K : ℝ)

theorem Mconst_pos (n : ℕ) (T : Finset K) (D : ℕ) (hX : 0 < T.card) : 0 < Mconst K n T D := by
  unfold Mconst
  have : (0 : ℝ) < dfac (n + 1) := by
    exact_mod_cast Finset.prod_pos (fun i _ => by omega)
  positivity

open Classical in
/-- **`SemaevNondeg` ⟹ `AvgEnergyBound`** (the average-energy bound for Mathlib's group law). -/
theorem avg_of_semaev (hK : ringChar K ≠ 2) (T : Finset K) (n D : ℕ)
    (h : SemaevNondeg (n + 1) T D) : AvgEnergyBound n T (Mconst K n T D) := by
  obtain ⟨f, hdeg, hvan, hN⟩ := h
  have hsk := avg_energy_skeleton (n + 1) T D (Rel (n + 1)) f
    (fun θ u hu hr => hsem_of f hvan θ u hu hr) hdeg hN
  unfold AvgEnergyBound
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have h1 : ∀ p : K × K, (if disc p.1 p.2 = 0 then (0 : ℝ) else (Eng T n p.1 p.2 : ℝ))
      ≤ (((badSet (n + 1) T (Rel (n + 1))).filter (fun x => x.1 = ![p.1, p.2])).card : ℝ) := by
    intro p
    split_ifs with hd
    · positivity
    · exact_mod_cast eng_le_fiber hK T n p.1 p.2 hd
  have h2 := sum_fiber_le (badSet (n + 1) T (Rel (n + 1)))
  calc _ ≤ ∑ p : K × K, (((badSet (n + 1) T (Rel (n + 1))).filter
          (fun x => x.1 = ![p.1, p.2])).card : ℝ) := sum_le_sum (fun p _ => h1 p)
    _ = ((∑ p : K × K, ((badSet (n + 1) T (Rel (n + 1))).filter
          (fun x => x.1 = ![p.1, p.2])).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((badSet (n + 1) T (Rel (n + 1))).card : ℝ) := by exact_mod_cast h2
    _ ≤ (dfac (n + 1) : ℝ) * 4 ^ (n + 1) * (T.card : ℝ) ^ (n + 1) * (Fintype.card K : ℝ) ^ 2
        + 4 ^ (n + 1) * D * (T.card : ℝ) ^ (2 * (n + 1)) * (Fintype.card K : ℝ) := by
      exact_mod_cast hsk
    _ = _ := by
      unfold Mconst
      field_simp

end ECDLP.L46
