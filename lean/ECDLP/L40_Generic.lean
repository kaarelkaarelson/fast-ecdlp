import Mathlib
import ECDLP.L40_Cover

/-!
# L40 (2): non-generic tuples are few; coverage of generic sums

`G` an additive abelian group, `F ⊆ G` finite with `f = |F|`, `x : G → β` with fibres of size
`≤ 2` on `F` (in the application `x` = x-coordinate, fibre = `{P, -P}`).  For `t : Fin (n+1) → G`
let `S k t = ∑_{l<k} t l` be the partial sums.  `t` is *generic* if for each `k = 1..n`,
`S k t ≠ 0` and `x (S k t) ≠ x (t k)` (the conditions the network checks).
Non-generic tuples in `F^{n+1}` number at most `3 n f^n`.
-/
namespace ECDLP.L40

open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {β : Type*} [DecidableEq β]

/-- partial sum of the first `i` coordinates -/
def psum {m : ℕ} (i : Fin m) (t : Fin m → G) : G := ∑ l ∈ univ.filter (· < i), t l

theorem psum_update_of_lt {m : ℕ} (i j : Fin m) (hj : j < i) (t : Fin m → G) (a : G) :
    psum i (Function.update t j a) + t j = psum i t + a := by
  unfold psum
  have hmem : j ∈ univ.filter (· < i) := by simp [hj]
  rw [← add_sum_erase _ _ hmem, ← add_sum_erase _ (fun l => t l) hmem]
  have : ∑ l ∈ (univ.filter (· < i)).erase j, Function.update t j a l
      = ∑ l ∈ (univ.filter (· < i)).erase j, t l :=
    sum_congr rfl (fun l hl => Function.update_of_ne (ne_of_mem_erase hl) _ _)
  rw [this]; simp; abel

theorem psum_update_self {m : ℕ} (i : Fin m) (t : Fin m → G) (a : G) :
    psum i (Function.update t i a) = psum i t := by
  unfold psum
  exact sum_congr rfl (fun l hl => Function.update_of_ne (ne_of_lt (by simpa using hl)) _ _)

/-- slicing lemma -/
theorem card_slice {n : ℕ} (F : Finset G) (W : Finset (Fin (n + 1) → G))
    (hW : W ⊆ Fintype.piFinset (fun _ => F)) (j : Fin (n + 1)) (c : ℕ)
    (h : ∀ t : Fin (n + 1) → G, (F.filter (fun a => Function.update t j a ∈ W)).card ≤ c) :
    W.card ≤ c * F.card ^ n := by
  rw [card_eq_sum_card_fiberwise (f := fun t : Fin (n + 1) → G => fun k : Fin n => t (j.succAbove k))
    (t := Fintype.piFinset (fun _ : Fin n => F)) (by
      intro t ht
      have := hW ht
      simp only [Fintype.mem_piFinset] at this
      simp only [mem_coe, Fintype.mem_piFinset]
      exact fun k => this _)]
  have : ∀ r ∈ (Fintype.piFinset (fun _ : Fin n => F)),
      (W.filter (fun t => (fun k : Fin n => t (j.succAbove k)) = r)).card ≤ c := by
    intro r _
    rcases (W.filter (fun t => (fun k : Fin n => t (j.succAbove k)) = r)).eq_empty_or_nonempty
      with he | ⟨t0, ht0⟩
    · rw [he]; simp
    · refine le_trans (card_le_card_of_injOn (fun t => t j)
        (t := F.filter (fun a => Function.update t0 j a ∈ W)) ?_ ?_) (h t0)
      · intro t ht
        simp only [coe_filter, Set.mem_ofPred_eq] at ht ⊢
        have htF := hW ht.1
        simp only [Fintype.mem_piFinset] at htF
        refine ⟨htF j, ?_⟩
        have : Function.update t0 j (t j) = t := by
          funext k
          by_cases hk : k = j
          · subst hk; simp
          · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
            rw [Function.update_of_ne hk]
            have h1 : t (j.succAbove k') = r k' := congrFun ht.2 k'
            have h2 : t0 (j.succAbove k') = r k' := congrFun (mem_filter.1 ht0).2 k'
            rw [h2, h1]
        rw [this]; exact ht.1
      · intro t ht u hu htu
        simp only [coe_filter, Set.mem_ofPred_eq] at ht hu
        funext k
        by_cases hk : k = j
        · subst hk; exact htu
        · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
          have h1 : t (j.succAbove k') = _ := congrFun ht.2 k'
          have h2 : u (j.succAbove k') = _ := congrFun hu.2 k'
          rw [h1, h2]
  calc _ ≤ ∑ r ∈ Fintype.piFinset (fun _ : Fin n => F), c := sum_le_sum this
    _ = c * F.card ^ n := by simp [Fintype.card_piFinset, mul_comm]

variable {F : Finset G}

/-- genericity of a tuple -/
def Generic {n : ℕ} (x : G → β) (t : Fin (n + 1) → G) : Prop :=
  ∀ k : Fin n, psum k.succ t ≠ 0 ∧ x (psum k.succ t) ≠ x (t k.succ)

instance {n : ℕ} (x : G → β) : DecidablePred (Generic (n := n) x) :=
  fun t => by unfold Generic; infer_instance

/-- **non-generic tuples are at most `3 n f^n`** -/
theorem card_nongeneric {n : ℕ} (F : Finset G) (x : G → β)
    (hx : ∀ a, (F.filter (fun P => x P = a)).card ≤ 2) :
    ((Fintype.piFinset (fun _ : Fin (n + 1) => F)).filter (fun t => ¬ Generic x t)).card
      ≤ 3 * n * F.card ^ n := by
  classical
  set U := Fintype.piFinset (fun _ : Fin (n + 1) => F) with hU
  have h1 : ∀ k : Fin n, (U.filter (fun t => psum k.succ t = 0)).card ≤ F.card ^ n := by
    intro k
    have := card_slice (n := n) F (U.filter (fun t => psum k.succ t = 0)) (filter_subset _ _)
      k.castSucc 1 (by
        intro t
        rw [card_le_one]
        intro a ha b hb
        simp only [mem_filter, hU] at ha hb
        have hlt : k.castSucc < k.succ := Fin.castSucc_lt_succ
        have e1 := psum_update_of_lt k.succ k.castSucc hlt t a
        have e2 := psum_update_of_lt k.succ k.castSucc hlt t b
        rw [ha.2.2] at e1; rw [hb.2.2] at e2
        have : a = b := by
          have : psum k.succ t + a = psum k.succ t + b := by rw [← e1, ← e2]
          exact add_left_cancel this
        exact this)
    simpa using this
  have h2 : ∀ k : Fin n, (U.filter (fun t => x (psum k.succ t) = x (t k.succ))).card
      ≤ 2 * F.card ^ n := by
    intro k
    refine card_slice (n := n) F _ (filter_subset _ _) k.succ 2 ?_
    intro t
    refine le_trans (card_le_card ?_) (hx (x (psum k.succ t)))
    intro a ha
    simp only [mem_filter] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have := ha.2.2
    rw [psum_update_self] at this
    simpa using this.symm
  have hsub : U.filter (fun t => ¬ Generic x t) ⊆
      univ.biUnion (fun k : Fin n => U.filter (fun t => psum k.succ t = 0) ∪
        U.filter (fun t => x (psum k.succ t) = x (t k.succ))) := by
    intro t ht
    simp only [mem_filter, Generic, not_forall, not_and_or, not_not] at ht
    obtain ⟨htU, k, hk⟩ := ht
    simp only [mem_biUnion, mem_univ, mem_union, mem_filter, true_and]
    exact ⟨k, hk.elim (fun h => Or.inl ⟨htU, h⟩) (fun h => Or.inr ⟨htU, h⟩)⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ k : Fin n, (_ ∪ _ : Finset _).card ≤ ∑ _k : Fin n, (3 * F.card ^ n) := by
        refine sum_le_sum (fun k _ => (card_union_le _ _).trans ?_)
        have := h1 k; have := h2 k; omega
    _ = 3 * n * F.card ^ n := by simp; ring

/-- **Coverage of generic sums.**  The set `G` of group elements having a generic decomposition
as a sum of `n+1` elements of `F` satisfies
`(f^{n+1} - 3 n f^n)² ≤ |G| · E_{n+1}(F)`. -/
theorem generic_coverage {n : ℕ} (F : Finset G) (x : G → β)
    (hx : ∀ a, (F.filter (fun P => x P = a)).card ≤ 2) :
    (F.card ^ (n + 1) - 3 * n * F.card ^ n) ^ 2 ≤
      (sums ((Fintype.piFinset (fun _ : Fin (n + 1) => F)).filter (fun t => Generic x t))).card
        * energy (n + 1) F := by
  classical
  set U := Fintype.piFinset (fun _ : Fin (n + 1) => F)
  have hsub : U.filter (fun t => Generic x t) ⊆ U := filter_subset _ _
  have hcard : F.card ^ (n + 1) - 3 * n * F.card ^ n ≤ (U.filter (fun t => Generic x t)).card := by
    have h : (U.filter (fun t => ¬ Generic x t)).card ≤ 3 * n * F.card ^ n :=
      card_nongeneric (n := n) F x hx
    have h2 := card_filter_add_card_filter_not (s := U) (fun t => Generic x t)
    have hUc : U.card = F.card ^ (n + 1) := by simp [U, Fintype.card_piFinset]
    generalize 3 * n * F.card ^ n = B at *
    generalize F.card ^ (n + 1) = C at *
    omega
  calc (F.card ^ (n + 1) - 3 * n * F.card ^ n) ^ 2
      ≤ (U.filter (fun t => Generic x t)).card ^ 2 := Nat.pow_le_pow_left hcard 2
    _ ≤ _ := sq_card_le_sums_mul_energy F _ hsub

end ECDLP.L40
