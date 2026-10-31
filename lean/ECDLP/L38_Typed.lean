import ECDLP.L35_Forced
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin

/-!
# L38 / Typed: forced networks with arbitrary finite message types

`TForced`: like L35's `Forced`, but gate `i` sends a message of an arbitrary finite inhabited type `Msg i`
(coded into `Fin (2^w)` with `w = clog 2 |Msg i|`).  `tforced_value`: `Net.value` of the associated
`Net` is the number of free assignments `x` such that every local check holds on the forced settings
(`tv x`, the unique solution of the message recursion).
-/
noncomputable section
namespace ECDLP.L38
open Factoring.Aux Finset ECDLP.L35

structure TForced (R : Type*) [CommRing R] (ι : Type) where
  Free : ι → Type
  fFree : ∀ i, Fintype (Free i)
  dFree : ∀ i, DecidableEq (Free i)
  Msg : ι → Type
  fMsg : ∀ i, Fintype (Msg i)
  iMsg : ∀ i, Inhabited (Msg i)
  pa : ι → Finset ι
  rk : ι → ℕ
  hrk : ∀ i j, j ∈ pa i → rk j < rk i
  W : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Msg j.1) → R
  out : ∀ i, Free i × (∀ j : {j // j ∈ pa i}, Msg j.1) → Msg i

attribute [instance] TForced.fFree TForced.dFree TForced.fMsg TForced.iMsg

namespace TForced
variable {R : Type*} [CommRing R] {ι : Type} (T : TForced R ι)

def w (i : ι) : ℕ := Nat.clog 2 (Fintype.card (T.Msg i))

def enc (i : ι) (m : T.Msg i) : Fin (2 ^ T.w i) :=
  ⟨Fintype.equivFin (T.Msg i) m, lt_of_lt_of_le (Fintype.equivFin (T.Msg i) m).isLt
    (Nat.le_pow_clog one_lt_two _)⟩

def dec (i : ι) (n : Fin (2 ^ T.w i)) : T.Msg i :=
  if h : n.val < Fintype.card (T.Msg i) then (Fintype.equivFin (T.Msg i)).symm ⟨n.val, h⟩ else default

theorem dec_enc (i : ι) (m : T.Msg i) : T.dec i (T.enc i m) = m := by
  unfold dec enc
  rw [dif_pos (Fintype.equivFin (T.Msg i) m).isLt]
  simp

def toForced : Forced R ι where
  Free := T.Free
  fFree := T.fFree
  dFree := T.dFree
  pa := T.pa
  w := T.w
  rk := T.rk
  hrk := T.hrk
  W i z := T.W i (z.1, fun j => T.dec j.1 (z.2 j))
  out i z := T.enc i (T.out i (z.1, fun j => T.dec j.1 (z.2 j)))

/-- decoded forced messages -/
def tv (x : ∀ i, T.Free i) (i : ι) : T.Msg i := T.dec i (T.toForced.outv x i)

theorem tv_eq (x : ∀ i, T.Free i) (i : ι) :
    T.tv x i = T.out i (x i, fun j => T.tv x j.1) := by
  unfold tv
  rw [T.toForced.outv_eq x i]
  show T.dec i (T.enc i _) = _
  rw [T.dec_enc]
  rfl

theorem tv_unique (x : ∀ i, T.Free i) (u : ∀ i, T.Msg i)
    (hu : ∀ i, u i = T.out i (x i, fun j => u j.1)) : u = T.tv x := by
  have key : ∀ n i, T.rk i = n → u i = T.tv x i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i h
      rw [hu i, T.tv_eq]
      congr 1
      congr 1
      funext j
      exact ih _ (h ▸ T.hrk i j.1 j.2) j.1 rfl
  funext i; exact key _ i rfl

open Classical in
theorem tforced_value [Fintype ι] [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g)
    (hW : ∀ i s, T.W i s = 0 ∨ T.W i s = 1) :
    ((T.toForced.toGNet).toNet e).value =
      ((univ.filter fun x : (∀ i, T.Free i) => ∀ i, T.W i (x i, fun j => T.tv x j.1) = 1).card : R) := by
  have h := T.toForced.forced_value e (fun i s => by
    rcases hW i (s.1, fun j => T.dec j.1 (s.2 j)) with h | h
    · exact Or.inl h
    · exact Or.inr h)
  rw [h]
  rfl

end TForced
end ECDLP.L38
end

#print axioms ECDLP.L38.TForced.tforced_value
