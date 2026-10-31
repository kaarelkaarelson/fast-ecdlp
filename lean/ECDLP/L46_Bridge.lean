import Mathlib
import ECDLP.L30_Final
import ECDLP.L43_Main

/-!
# L46 (1): L40/L43 generic decompositions = L30 `GenSet`

`Dec W FB n R` : ordered `(n+1)`-tuples of affine points of Mathlib's `W.Point` with `FB (x P_i)`,
`L40.Generic (xc W)` (partial sums nonzero, x(partial sum) ≠ x(next point)) and `∑ P_i = R`.
`card_dec_eq_card_genSet` : its cardinality equals that of L30's `GenSet W FB (coord R) n`.
-/
namespace ECDLP.L46

open Finset WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

open Classical in
/-- affine points whose x-coordinate satisfies `FB` -/
noncomputable def fbase (FB : K → Prop) : Finset W.Point :=
  univ.filter (fun P => P ≠ 0 ∧ FB (ECDLP.L43.xco W P))

open Classical in
/-- ordered generic decompositions (L40/L43 notion) of `R` into `n+1` factor-base points -/
noncomputable def Dec (FB : K → Prop) (n : ℕ) (R : W.Point) : Finset (Fin (n + 1) → W.Point) :=
  (Fintype.piFinset (fun _ : Fin (n + 1) => fbase W FB)).filter
    (fun t => ECDLP.L40.Generic (ECDLP.L43.xc W) t ∧ ∑ i, t i = R)

variable {W}

theorem ptOf_coord {Q : W.Point} (hQ : Q ≠ 0) : ECDLP.L30.ptOf W (ECDLP.L30.coord W Q) = Q := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => exact ECDLP.L30.ptOf_of_ns (q := (x, y)) h

theorem ns_coord {Q : W.Point} (hQ : Q ≠ 0) :
    W.Nonsingular (ECDLP.L30.coord W Q).1 (ECDLP.L30.coord W Q).2 := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => exact h

theorem coord_inj {Q Q' : W.Point} (hQ : Q ≠ 0) (hQ' : Q' ≠ 0)
    (h : ECDLP.L30.coord W Q = ECDLP.L30.coord W Q') : Q = Q' := by
  rw [← ptOf_coord hQ, ← ptOf_coord hQ', h]

theorem psumF_coord {n : ℕ} (t : Fin (n + 1) → W.Point) (ht : ∀ i, t i ≠ 0) (k : Fin n) :
    ECDLP.L30.psumF W (fun i => ECDLP.L30.coord W (t i)) k.castSucc
      = ECDLP.L40.psum k.succ t := by
  unfold ECDLP.L30.psumF ECDLP.L40.psum
  have h1 : ∀ i : Fin (n + 1), (if i ≤ k.castSucc then
      ECDLP.L30.ptOf W (ECDLP.L30.coord W (t i)) else 0) = if i ≤ k.castSucc then t i else 0 := by
    intro i; split_ifs
    · exact ptOf_coord (ht i)
    · rfl
  simp only [h1]
  rw [← sum_filter]
  have : (univ.filter (fun i : Fin (n + 1) => i ≤ k.castSucc)) = univ.filter (· < k.succ) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Fin.le_def, Fin.lt_def, Fin.val_succ,
      Fin.coe_castSucc]
    omega
  rw [this]

theorem psumF_last {n : ℕ} (t : Fin (n + 1) → W.Point) (ht : ∀ i, t i ≠ 0) :
    ECDLP.L30.psumF W (fun i => ECDLP.L30.coord W (t i)) (Fin.last n) = ∑ i, t i := by
  unfold ECDLP.L30.psumF
  refine sum_congr rfl (fun i _ => ?_)
  rw [if_pos (Fin.le_last i)]
  exact ptOf_coord (ht i)

theorem generic_iff {n : ℕ} (t : Fin (n + 1) → W.Point) (ht : ∀ i, t i ≠ 0) :
    ECDLP.L30.GenericF W (fun i => ECDLP.L30.coord W (t i)) ↔
      ECDLP.L40.Generic (ECDLP.L43.xc W) t := by
  unfold ECDLP.L30.GenericF ECDLP.L40.Generic
  refine forall_congr' (fun k => ?_)
  rw [psumF_coord t ht k]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    beta_reduce at h1 ⊢
    generalize hS : ECDLP.L40.psum k.succ t = S at h0 h1
    have := ht k.succ
    cases S with
    | zero => exact absurd rfl h0
    | some x y h =>
      cases hT : t k.succ with
      | zero => exact absurd hT this
      | some x' y' h' =>
        rw [hT] at h1
        simp only [ECDLP.L30.coord, ECDLP.L43.xc] at h1 ⊢
        intro e; exact h1 (Option.some.inj e)
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    beta_reduce at h1 ⊢
    generalize hS : ECDLP.L40.psum k.succ t = S at h0 h1
    have := ht k.succ
    cases S with
    | zero => exact absurd rfl h0
    | some x y h =>
      cases hT : t k.succ with
      | zero => exact absurd hT this
      | some x' y' h' =>
        rw [hT] at h1
        simp only [ECDLP.L30.coord, ECDLP.L43.xc] at h1 ⊢
        intro e; exact h1 (congrArg some e)

/-- **Bridge.** For an affine target `R`, the number of ordered generic factor-base decompositions
(L40/L43's notion, in Mathlib's group `W.Point`) equals the cardinality of L30's `GenSet`. -/
theorem card_dec_eq_card_genSet (FB : K → Prop) (n : ℕ) {R : W.Point} (hR : R ≠ 0) :
    (Dec W FB n R).card = (ECDLP.L30.GenSet W FB (ECDLP.L30.coord W R) n).card := by
  classical
  have hRns := ns_coord hR
  have hRp := ptOf_coord hR
  have mem : ∀ t : Fin (n + 1) → W.Point, t ∈ Dec W FB n R ↔
      (∀ i, t i ≠ 0 ∧ FB (ECDLP.L43.xco W (t i))) ∧
        ECDLP.L40.Generic (ECDLP.L43.xc W) t ∧ ∑ i, t i = R := by
    intro t
    simp [Dec, fbase, Fintype.mem_piFinset, and_assoc]
  refine card_bij (fun t _ => fun i => ECDLP.L30.coord W (t i)) ?_ ?_ ?_
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := (mem t).1 ht
    have hne : ∀ i, t i ≠ 0 := fun i => (h1 i).1
    simp only [ECDLP.L30.GenSet, mem_filter, mem_univ, true_and]
    refine ⟨fun i => ⟨ns_coord (hne i), ?_⟩, (generic_iff t hne).2 h2, ?_⟩
    · have := (h1 i).2
      cases hT : t i with
      | zero => exact absurd hT (hne i)
      | some x y h => rw [hT] at this; exact this
    · rw [psumF_last t hne, hRp, h3]
  · intro t ht t' ht' h
    obtain ⟨h1, -⟩ := (mem t).1 ht
    obtain ⟨h1', -⟩ := (mem t').1 ht'
    funext i
    exact coord_inj (h1 i).1 (h1' i).1 (congrFun h i)
  · intro P hP
    simp only [ECDLP.L30.GenSet, mem_filter, mem_univ, true_and] at hP
    obtain ⟨hns, hg, hsum⟩ := hP
    have hne : ∀ i, ECDLP.L30.ptOf W (P i) ≠ 0 := fun i => ECDLP.L30.ptOf_ne_zero (hns i).1
    have hcP : (fun i => ECDLP.L30.coord W (ECDLP.L30.ptOf W (P i))) = P :=
      funext (fun i => ECDLP.L30.coord_ptOf (hns i).1)
    refine ⟨fun i => ECDLP.L30.ptOf W (P i), ?_, hcP⟩
    rw [mem]
    refine ⟨fun i => ⟨hne i, ?_⟩, ?_, ?_⟩
    · have := (hns i).2
      rw [← ECDLP.L30.coord_ptOf (hns i).1] at this
      cases hT : ECDLP.L30.ptOf W (P i) with
      | zero => exact absurd hT (hne i)
      | some x y h => rw [hT] at this; exact this
    · rw [← generic_iff _ hne, hcP]; exact hg
    · rw [← psumF_last _ hne, hcP, hsum, hRp]

end ECDLP.L46
