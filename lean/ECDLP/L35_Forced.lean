import FactoringAux.Gates

/-!
# L35 (a): forced-value contraction in Rudich's `Net` framework

A "forced network" is a directed acyclic family of gates `i : ι`.  Gate `i` has a local free
variable `x_i : Free i` (sources carry the genuinely free variables) and *receives* a message from
each parent `j ∈ pa i`; its setting is `(x_i, tuple of received messages)`.  It sends the message
`out i (setting)` (a number `< 2^(w i)`) to its children.  The pair factor `Ψ_{i,j}` is the equality
of the message sent by the parent and the message the child holds (a `GNet` message test).  The weight
`W i` is a `0/1` local check of the setting.

`forced_value`: `Net.value` of the network equals the number of assignments of the free variables
`x : ∀ i, Free i` for which every local check holds, the received messages being forced
(`inp x`, computed by recursion along the order).
-/
namespace ECDLP.L35
open Factoring.Aux Finset

/-- A forced network over the commutative ring `R`. -/
structure Forced (R : Type*) [CommRing R] (ι : Type) where
  /-- local free variables -/
  Free : ι → Type
  fFree : ∀ i, Fintype (Free i)
  dFree : ∀ i, DecidableEq (Free i)
  /-- parents (senders) of each gate -/
  pa : ι → Finset ι
  /-- message width in bits of gate `i`'s output -/
  w : ι → ℕ
  /-- a rank certifying acyclicity -/
  rk : ι → ℕ
  hrk : ∀ i j, j ∈ pa i → rk j < rk i
  /-- the local check, `0/1`, on the setting `(free variable, received messages)` -/
  W : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Fin (2 ^ w j.1)) → R
  /-- the message sent by gate `i` -/
  out : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Fin (2 ^ w j.1)) → Fin (2 ^ w i)

attribute [instance] Forced.fFree Forced.dFree

namespace Forced
variable {R : Type*} [CommRing R] {ι : Type} (F : Forced R ι)

/-- The setting type of gate `i`: free variable and received messages. -/
abbrev S (i : ι) : Type := F.Free i × (∀ j : {j // j ∈ F.pa i}, Fin (2 ^ F.w j.1))

/-- The message a gate holds from parent `j`, or the message it sends, as seen on the pair `(i, j)`. -/
def v [DecidableEq ι] (i j : ι) (z : F.S i) : ℕ :=
  if h : j ∈ F.pa i then (z.2 ⟨j, h⟩).val + 1
  else if i ∈ F.pa j then (F.out i z).val + 1 else 0

/-- The gate network: weights `W`, messages `v`, widths `2^wᵢ + 2^wⱼ`. -/
def toGNet [DecidableEq ι] : GNet R ι where
  S := F.S
  fS _ := inferInstance
  dS _ := inferInstance
  W := F.W
  c i j := (2 ^ F.w i + 2 ^ F.w j)
  v := F.v

theorem pa_asymm {i j : ι} (h : j ∈ F.pa i) : i ∉ F.pa j := fun h' =>
  absurd (F.hrk i j h) (not_lt.2 (le_of_lt (F.hrk j i h')))

/-- The free assignment forces the outputs of all gates (recursion along the rank). -/
def outv (x : ∀ i, F.Free i) (i : ι) : Fin (2 ^ F.w i) :=
  F.out i (x i, fun j => outv x j.1)
termination_by F.rk i
decreasing_by exact F.hrk _ _ j.2

/-- The forced setting of gate `i`. -/
def run (x : ∀ i, F.Free i) (i : ι) : F.S i := (x i, fun j => F.outv x j.1)

theorem outv_eq (x : ∀ i, F.Free i) (i : ι) : F.outv x i = F.out i (F.run x i) := by
  rw [outv]; rfl

/-- Consistency: every received message is the message the parent sends. -/
def Cons (z : ∀ i, F.S i) : Prop := ∀ i (j : {j // j ∈ F.pa i}), (z i).2 j = F.out j.1 (z j.1)

/-- Local checks all pass. -/
def Chk (z : ∀ i, F.S i) : Prop := ∀ i, F.W i (z i) = 1

theorem good_iff [DecidableEq ι] (z : ∀ i, F.S i) :
    (F.toGNet).Good z ↔ F.Chk z ∧ F.Cons z := by
  unfold GNet.Good Chk Cons
  show ((∀ i, F.W i (z i) = 1) ∧ ∀ i j, i ≠ j → F.v i j (z i) = F.v j i (z j)) ↔ _
  refine and_congr Iff.rfl ⟨fun h i j => ?_, fun h i j hij => ?_⟩
  · have hne : i ≠ j.1 := fun e => by
      have := F.hrk i j.1 j.2; rw [← e] at this; exact lt_irrefl _ this
    have := h i j.1 hne
    simp only [v, dif_pos j.2, dif_neg (F.pa_asymm j.2), if_pos j.2] at this
    exact Fin.ext (by simpa using this)
  · by_cases h1 : j ∈ F.pa i
    · have h2 := F.pa_asymm h1
      simp only [v, dif_pos h1, dif_neg h2, if_pos h1]
      rw [h i ⟨j, h1⟩]
    · by_cases h2 : i ∈ F.pa j
      · simp only [v, dif_neg h1, if_pos h2, dif_pos h2]
        rw [h j ⟨i, h2⟩]
      · simp [v, h1, h2]

theorem cons_run (x : ∀ i, F.Free i) : F.Cons (F.run x) := fun i j => by
  show F.outv x j.1 = _
  exact F.outv_eq x j.1

theorem run_of_cons (z : ∀ i, F.S i) (hz : F.Cons z) : F.run (fun i => (z i).1) = z := by
  have key : ∀ n i, F.rk i = n → F.outv (fun i => (z i).1) i = F.out i (z i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i h
      rw [outv]
      have : (fun j : {j // j ∈ F.pa i} => F.outv (fun i => (z i).1) j.1) = (z i).2 := by
        funext j
        rw [ih _ (h ▸ F.hrk i j.1 j.2) j.1 rfl, hz i j]
      rw [this]
  funext i
  refine Prod.ext rfl ?_
  funext j
  exact (key _ j.1 rfl).trans (hz i j).symm

open Classical in
/-- Forced-value contraction, count form: the good settings of the gate network are in bijection with the
free assignments passing every local check. -/
theorem card_good [Fintype ι] [DecidableEq ι] :
    (univ.filter (F.toGNet).Good).card =
      (univ.filter fun x : (∀ i, F.Free i) => F.Chk (F.run x)).card := by
  refine Finset.card_bij' (fun z _ i => (z i).1) (fun x _ => F.run x) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    have h := (F.good_iff z).1 hz
    rw [F.run_of_cons z h.2]; exact h.1
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact Finset.mem_filter.2 ⟨mem_univ _, (F.good_iff _).2 ⟨hx, F.cons_run x⟩⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    exact F.run_of_cons z ((F.good_iff z).1 hz).2
  · intro x _; rfl

theorem v_lt [DecidableEq ι] (i j : ι) (z : F.S i) : F.v i j z < 2 ^ (2 ^ F.w i + 2 ^ F.w j) := by
  refine lt_of_le_of_lt ?_ (Nat.lt_two_pow_self)
  unfold v
  split_ifs with h1 h2
  · have : (z.2 ⟨j, h1⟩).val < 2 ^ F.w j := (z.2 ⟨j, h1⟩).isLt
    have := Nat.two_pow_pos (F.w i); omega
  · have := (F.out i z).isLt
    have := Nat.two_pow_pos (F.w j); omega
  · exact Nat.zero_le _

open Classical in
/-- **Forced-value contraction.** For a forced network with `0/1` local checks, `Net.value` of the
corresponding `Net` (any enumeration `e` of the gates) is the number of assignments `x` of the free
variables such that every local check holds on the forced settings `run x`
(gate `i` has setting `(x i, messages received, all forced)`). -/
theorem forced_value [Fintype ι] [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g)
    (hW : ∀ i s, F.W i s = 0 ∨ F.W i s = 1) :
    ((F.toGNet).toNet e).value =
      ((univ.filter fun x : (∀ i, F.Free i) => ∀ i, F.W i (F.run x i) = 1).card : R) := by
  rw [GNet.value_toNet F.toGNet e hW (fun i j z => F.v_lt i j z)]
  congr 1
  have h := F.card_good
  unfold Chk at h
  convert h

end Forced
end ECDLP.L35

#print axioms ECDLP.L35.Forced.forced_value
