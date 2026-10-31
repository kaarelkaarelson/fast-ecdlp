import Mathlib

namespace ECDLP.L46

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem fiber_univ {α β : Type*} [DecidableEq β] [Fintype β] (B : Finset α) (f : α → β) :
    B.card = ∑ b, (B.filter (fun x => f x = b)).card :=
  card_eq_sum_card_fiberwise (fun x _ => by simp)

set_option maxHeartbeats 1000000 in
/-- Sum over `(A,B)` of fibre sizes is at most the size of `badSet`. -/
theorem sum_fiber_le {m : ℕ} (B : Finset ((Fin 2 → K) × (Fin (2 * m) → K × K))) :
    ∑ p : K × K, (B.filter (fun x => x.1 = ![p.1, p.2])).card ≤ B.card := by
  have hinj : Function.Injective (fun p : K × K => (![p.1, p.2] : Fin 2 → K)) := by
    intro p p' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    exact Prod.ext h0 h1
  have e1 : ∑ p : K × K, (B.filter (fun x => x.1 = ![p.1, p.2])).card
      = ∑ θ ∈ (univ : Finset (K × K)).image (fun p : K × K => (![p.1, p.2] : Fin 2 → K)),
          (B.filter (fun x => x.1 = θ)).card :=
    (sum_image (f := fun θ : Fin 2 → K => (B.filter (fun x => x.1 = θ)).card)
      (s := (univ : Finset (K × K))) (g := fun p : K × K => (![p.1, p.2] : Fin 2 → K))
      (fun a _ b _ h => hinj h)).symm
  have e2 : ∑ θ ∈ (univ : Finset (K × K)).image (fun p : K × K => (![p.1, p.2] : Fin 2 → K)),
          (B.filter (fun x => x.1 = θ)).card ≤ ∑ θ : Fin 2 → K, (B.filter (fun x => x.1 = θ)).card :=
    sum_le_sum_of_subset (subset_univ _)
  have e3 : B.card = ∑ θ : Fin 2 → K, (B.filter (fun x => x.1 = θ)).card :=
    fiber_univ B (fun x => x.1)
  exact e1.le.trans (e2.trans e3.symm.le)

end ECDLP.L46
