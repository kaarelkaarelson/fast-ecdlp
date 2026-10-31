import Mathlib
import ECDLP.L51_Inj
import ECDLP.L46_Oracle
import ECDLP.L44_Main

/-!
# L51 / Count: `ncard (strings …) = #{P ∈ GenSet | π <+: strOf P}`

(1) a filtered version of L46's bridge `card_dec_eq_card_genSet`;
(2) `strings (n+1) (p,a,b,xR,yR,π)` is the `strOf`-image of the filtered `Dec`;
(3) `strOf` is injective there (L51_Inj), hence the cardinalities agree.
-/
namespace ECDLP.L51

open Finset ECDLP.L46 ECDLP.L44 ECDLP.L30

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- **Filtered bridge.** Same bijection `t ↦ coord ∘ t` as `card_dec_eq_card_genSet`, with a filter. -/
theorem card_dec_filter_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {W : WeierstrassCurve.Affine K} (FB : K → Prop) (n : ℕ) {R : W.Point} (hR : R ≠ 0)
    (ψ : (Fin (n + 1) → K × K) → Prop) :
    ((Dec W FB n R).filter (fun t => ψ (fun i => ECDLP.L30.coord W (t i)))).card =
      ((ECDLP.L30.GenSet W FB (ECDLP.L30.coord W R) n).filter ψ).card := by
  have hRp := ptOf_coord hR
  have mem : ∀ t : Fin (n + 1) → W.Point, t ∈ Dec W FB n R ↔
      (∀ i, t i ≠ 0 ∧ FB (ECDLP.L43.xco W (t i))) ∧
        ECDLP.L40.Generic (ECDLP.L43.xc W) t ∧ ∑ i, t i = R := by
    intro t
    simp [Dec, fbase, Fintype.mem_piFinset, and_assoc]
  refine card_bij (fun t _ => fun i => ECDLP.L30.coord W (t i)) ?_ ?_ ?_
  · intro t ht
    rw [mem_filter] at ht
    obtain ⟨h1, h2, h3⟩ := (mem t).1 ht.1
    have hne : ∀ i, t i ≠ 0 := fun i => (h1 i).1
    simp only [ECDLP.L30.GenSet, mem_filter, mem_univ, true_and]
    refine ⟨⟨fun i => ⟨ns_coord (hne i), ?_⟩, (generic_iff t hne).2 h2, ?_⟩, ht.2⟩
    · have := (h1 i).2
      cases hT : t i with
      | zero => exact absurd hT (hne i)
      | some x y h => rw [hT] at this; exact this
    · rw [psumF_last t hne, hRp, h3]
  · intro t ht t' ht' h
    rw [mem_filter] at ht ht'
    obtain ⟨h1, -⟩ := (mem t).1 ht.1
    obtain ⟨h1', -⟩ := (mem t').1 ht'.1
    funext i
    exact coord_inj (h1 i).1 (h1' i).1 (congrFun h i)
  · intro P hP
    simp only [ECDLP.L30.GenSet, mem_filter, mem_univ, true_and] at hP
    obtain ⟨⟨hns, hg, hsum⟩, hψ⟩ := hP
    have hne : ∀ i, ECDLP.L30.ptOf W (P i) ≠ 0 := fun i => ECDLP.L30.ptOf_ne_zero (hns i).1
    have hcP : (fun i => ECDLP.L30.coord W (ECDLP.L30.ptOf W (P i))) = P :=
      funext (fun i => ECDLP.L30.coord_ptOf (hns i).1)
    have hmem : (fun i => ECDLP.L30.ptOf W (P i)) ∈ Dec W FB n R := by
      rw [mem]
      refine ⟨fun i => ⟨hne i, ?_⟩, ?_, ?_⟩
      · have := (hns i).2
        rw [← ECDLP.L30.coord_ptOf (hns i).1] at this
        cases hT : ECDLP.L30.ptOf W (P i) with
        | zero => exact absurd hT (hne i)
        | some x y h => rw [hT] at this; exact this
      · rw [← generic_iff _ hne, hcP]; exact hg
      · rw [← psumF_last _ hne, hcP, hsum, hRp]
    refine ⟨fun i => ECDLP.L30.ptOf W (P i), ?_, hcP⟩
    rw [mem_filter]
    exact ⟨hmem, by rw [hcP]; exact hψ⟩

end ECDLP.L51

#print axioms ECDLP.L51.card_dec_filter_eq
