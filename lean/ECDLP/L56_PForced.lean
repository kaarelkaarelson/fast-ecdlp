import ECDLP.L54_Tight

/-!
# L56 / PForced: forced networks with CHILD-SPECIFIC messages

Like `TForced` (L38), but the message a gate sends is a function of the *receiving* gate:
gate `i` has a message type `Msg i` (the type of each message it sends, one per child) and
`out i z c : Msg i` is the message it sends to child `c`.  The setting of gate `i` is
`(free variable, the tuple of messages received from its parents)`; so a gate that sends a different ring element
to each of its children does not have to hold (or be sent) the whole vector.

`pforced_value`: `Net.value` of the associated network (tight widths `clog |Msg i| + 1` on edges, `0` elsewhere)
equals the number of free assignments such that every local check holds on the forced settings.
-/
noncomputable section
namespace ECDLP.L56
open Factoring.Aux Finset

structure PForced (R : Type*) [CommRing R] (ι : Type) where
  Free : ι → Type
  fFree : ∀ i, Fintype (Free i)
  Msg : ι → Type
  fMsg : ∀ i, Fintype (Msg i)
  iMsg : ∀ i, Inhabited (Msg i)
  pa : ι → Finset ι
  rk : ι → ℕ
  hrk : ∀ i j, j ∈ pa i → rk j < rk i
  W : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Msg j.1) → R
  out : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Msg j.1) → ι → Msg i

attribute [instance] PForced.fFree PForced.fMsg PForced.iMsg

namespace PForced
variable {R : Type*} [CommRing R] {ι : Type} (P : PForced R ι)

/-- message width in bits -/
def w (i : ι) : ℕ := Nat.clog 2 (Fintype.card (P.Msg i))

/-- numeric code of a message -/
def enc (i : ι) (m : P.Msg i) : ℕ := (Fintype.equivFin (P.Msg i) m).val

theorem enc_lt (i : ι) (m : P.Msg i) : P.enc i m < 2 ^ P.w i :=
  lt_of_lt_of_le (Fintype.equivFin (P.Msg i) m).isLt (Nat.le_pow_clog one_lt_two _)

theorem enc_inj (i : ι) {m m' : P.Msg i} (h : P.enc i m = P.enc i m') : m = m' :=
  (Fintype.equivFin (P.Msg i)).injective (Fin.ext h)

/-- setting of a gate -/
abbrev S (i : ι) : Type := P.Free i × (∀ j : {j // j ∈ P.pa i}, P.Msg j.1)

open Classical in
/-- the gate network, tight pair widths -/
def toGNet [DecidableEq ι] : GNet R ι where
  S := P.S
  fS _ := inferInstance
  dS _ := Classical.decEq _
  W := P.W
  c i j := if j ∈ P.pa i then P.w j + 1 else if i ∈ P.pa j then P.w i + 1 else 0
  v i j z := if h : j ∈ P.pa i then P.enc j (z.2 ⟨j, h⟩) + 1
    else if i ∈ P.pa j then P.enc i (P.out i z j) + 1 else 0

theorem pa_asymm {i j : ι} (h : j ∈ P.pa i) : i ∉ P.pa j := fun h' =>
  absurd (P.hrk i j h) (not_lt.2 (le_of_lt (P.hrk j i h')))

/-- forced message from `i` to `c` under the free assignment `x` -/
def tvc (x : ∀ i, P.Free i) (i c : ι) : P.Msg i :=
  P.out i (x i, fun j => tvc x j.1 i) c
termination_by P.rk i
decreasing_by exact P.hrk _ _ j.2

/-- forced setting -/
def run (x : ∀ i, P.Free i) (i : ι) : P.S i := (x i, fun j => P.tvc x j.1 i)

theorem tvc_eq (x : ∀ i, P.Free i) (i c : ι) : P.tvc x i c = P.out i (P.run x i) c := by
  rw [tvc]; rfl

def Cons (z : ∀ i, P.S i) : Prop := ∀ i (j : {j // j ∈ P.pa i}), (z i).2 j = P.out j.1 (z j.1) i

def Chk (z : ∀ i, P.S i) : Prop := ∀ i, P.W i (z i) = 1

theorem good_iff [DecidableEq ι] (z : ∀ i, P.S i) :
    (P.toGNet).Good z ↔ P.Chk z ∧ P.Cons z := by
  classical
  unfold GNet.Good Chk Cons
  show ((∀ i, P.W i (z i) = 1) ∧ ∀ i j, i ≠ j → _ = _) ↔ _
  refine and_congr Iff.rfl ⟨fun h i j => ?_, fun h i j hij => ?_⟩
  · have hne : i ≠ j.1 := fun e => by
      have := P.hrk i j.1 j.2; rw [← e] at this; exact lt_irrefl _ this
    have := h i j.1 hne
    simp only [toGNet, dif_pos j.2, dif_neg (P.pa_asymm j.2), if_pos j.2] at this
    exact P.enc_inj _ (by simpa using this)
  · by_cases h1 : j ∈ P.pa i
    · have h2 := P.pa_asymm h1
      simp only [toGNet, dif_pos h1, dif_neg h2, if_pos h1]
      rw [h i ⟨j, h1⟩]
    · by_cases h2 : i ∈ P.pa j
      · simp only [toGNet, dif_neg h1, if_pos h2, dif_pos h2]
        rw [h j ⟨i, h2⟩]
      · simp [toGNet, h1, h2]

theorem cons_run (x : ∀ i, P.Free i) : P.Cons (P.run x) := fun i j => by
  show P.tvc x j.1 i = _
  exact P.tvc_eq x j.1 i

theorem run_of_cons (z : ∀ i, P.S i) (hz : P.Cons z) : P.run (fun i => (z i).1) = z := by
  have key : ∀ n i, P.rk i = n → ∀ c, P.tvc (fun i => (z i).1) i c = P.out i (z i) c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i h c
      rw [tvc]
      have : (fun j : {j // j ∈ P.pa i} => P.tvc (fun i => (z i).1) j.1 i) = (z i).2 := by
        funext j
        rw [ih _ (h ▸ P.hrk i j.1 j.2) j.1 rfl, hz i j]
      rw [this]
  funext i
  refine Prod.ext rfl ?_
  funext j
  exact (key _ j.1 rfl i).trans (hz i j).symm

open Classical in
theorem card_good [Fintype ι] [DecidableEq ι] :
    (univ.filter (P.toGNet).Good).card =
      (univ.filter fun x : (∀ i, P.Free i) => P.Chk (P.run x)).card := by
  refine Finset.card_bij' (fun z _ i => (z i).1) (fun x _ => P.run x) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    have h := (P.good_iff z).1 hz
    rw [P.run_of_cons z h.2]; exact h.1
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact Finset.mem_filter.2 ⟨mem_univ _, (P.good_iff _).2 ⟨hx, P.cons_run x⟩⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    exact P.run_of_cons z ((P.good_iff z).1 hz).2
  · intro x _; rfl

theorem v_lt [DecidableEq ι] (i j : ι) (z : P.S i) :
    (P.toGNet).v i j z < 2 ^ (P.toGNet).c i j := by
  classical
  show (if h : j ∈ P.pa i then P.enc j (z.2 ⟨j, h⟩) + 1
    else if i ∈ P.pa j then P.enc i (P.out i z j) + 1 else 0) <
    2 ^ (if j ∈ P.pa i then P.w j + 1 else if i ∈ P.pa j then P.w i + 1 else 0)
  by_cases h1 : j ∈ P.pa i
  · simp only [dif_pos h1, if_pos h1]
    have := P.enc_lt j (z.2 ⟨j, h1⟩)
    rw [pow_succ]; omega
  · by_cases h2 : i ∈ P.pa j
    · simp only [dif_neg h1, if_neg h1, if_pos h2]
      have := P.enc_lt i (P.out i z j)
      rw [pow_succ]; omega
    · simp [h1, h2]

open Classical in
/-- **Forced-value contraction for child-specific messages.** -/
theorem pforced_value [Fintype ι] [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g)
    (hW : ∀ i s, P.W i s = 0 ∨ P.W i s = 1) :
    ((P.toGNet).toNet e).value =
      ((univ.filter fun x : (∀ i, P.Free i) => ∀ i, P.W i (P.run x i) = 1).card : R) := by
  rw [GNet.value_toNet P.toGNet e hW (fun i j z => P.v_lt i j z)]
  congr 1
  have h := P.card_good
  unfold Chk at h
  convert h

theorem tvc_unique (x : ∀ i, P.Free i) (u : ∀ i, ι → P.Msg i)
    (hu : ∀ i c, u i c = P.out i (x i, fun j => u j.1 i) c) : u = P.tvc x := by
  have key : ∀ n i, P.rk i = n → ∀ c, u i c = P.tvc x i c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i h c
      rw [hu i c, tvc]
      congr 2
      funext j
      exact ih _ (h ▸ P.hrk i j.1 j.2) j.1 rfl i
  funext i c; exact key _ i rfl c

end PForced
end ECDLP.L56
end

#print axioms ECDLP.L56.PForced.pforced_value
