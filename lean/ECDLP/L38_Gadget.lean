import ECDLP.L38_Typed
import ECDLP.L34_Final

/-!
# L38 / Gadget: L34's gadget as a (typed) forced network

Gates: `fa i s` (free variable: the digit slice `Fin h -> Fin (2^b)` of slot `i`), `mid k`, `ib j`, `car j`.
Messages: `fa`, `mid`, `ib` send a vector `Fin A -> Z/(2^M+1)`; `car j` sends the signed carry,
coded in `Fin (2^(M+3))` by `q + 2^(M+1)`.  Local checks: `car j` checks `2^b | cin + c` and, at the last
gate, that the outgoing carry is `0`; all other checks are `1`.
-/
noncomputable section
namespace ECDLP.L38
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35

inductive Gate (ι : Type) (A : ℕ) : Type
  | fa (i : ι) (s : Fin A)
  | mid (k : Fin A)
  | ib (j : Fin A)
  | car (j : Fin (A * A))
  deriving DecidableEq

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] (N : NPar)

open Gate

def gateEquiv (ι : Type) (A : ℕ) :
    Gate ι A ≃ (ι × Fin A) ⊕ (Fin A ⊕ (Fin A ⊕ Fin (A * A))) where
  toFun
    | .fa i s => .inl (i, s)
    | .mid k => .inr (.inl k)
    | .ib j => .inr (.inr (.inl j))
    | .car j => .inr (.inr (.inr j))
  invFun
    | .inl p => .fa p.1 p.2
    | .inr (.inl k) => .mid k
    | .inr (.inr (.inl j)) => .ib j
    | .inr (.inr (.inr j)) => .car j
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with p | k | j | j <;> rfl

instance (ι : Type) [Fintype ι] (A : ℕ) : Fintype (Gate ι A) := Fintype.ofEquiv _ (gateEquiv ι A).symm

def FreeT : Gate ι N.A → Type
  | .fa _ _ => Fin N.h → Fin (2 ^ N.b)
  | _ => Unit

instance instFreeF : ∀ g : Gate ι N.A, Fintype (FreeT N g)
  | .fa _ _ => inferInstanceAs (Fintype (Fin N.h → Fin (2 ^ N.b)))
  | .mid _ => inferInstanceAs (Fintype Unit)
  | .ib _ => inferInstanceAs (Fintype Unit)
  | .car _ => inferInstanceAs (Fintype Unit)

instance instFreeD : ∀ g : Gate ι N.A, DecidableEq (FreeT N g)
  | .fa _ _ => inferInstanceAs (DecidableEq (Fin N.h → Fin (2 ^ N.b)))
  | .mid _ => inferInstanceAs (DecidableEq Unit)
  | .ib _ => inferInstanceAs (DecidableEq Unit)
  | .car _ => inferInstanceAs (DecidableEq Unit)

def MsgT : Gate ι N.A → Type
  | .fa _ _ => Fin N.A → N.Rg
  | .mid _ => Fin N.A → N.Rg
  | .ib _ => Fin N.A → N.Rg
  | .car _ => Fin (2 ^ (N.M + 3))

instance instMsgF : ∀ g : Gate ι N.A, Fintype (MsgT N g)
  | .fa _ _ => inferInstanceAs (Fintype (Fin N.A → N.Rg))
  | .mid _ => inferInstanceAs (Fintype (Fin N.A → N.Rg))
  | .ib _ => inferInstanceAs (Fintype (Fin N.A → N.Rg))
  | .car _ => inferInstanceAs (Fintype (Fin (2 ^ (N.M + 3))))

instance instMsgI : ∀ g : Gate ι N.A, Inhabited (MsgT N g)
  | .fa _ _ => inferInstanceAs (Inhabited (Fin N.A → N.Rg))
  | .mid _ => inferInstanceAs (Inhabited (Fin N.A → N.Rg))
  | .ib _ => inferInstanceAs (Inhabited (Fin N.A → N.Rg))
  | .car _ => ⟨⟨0, by positivity⟩⟩

def paG : Gate ι N.A → Finset (Gate ι N.A)
  | .fa _ _ => ∅
  | .mid _ => univ.image (fun p : ι × Fin N.A => Gate.fa p.1 p.2)
  | .ib _ => univ.image (fun k : Fin N.A => Gate.mid k)
  | .car j => insert (Gate.ib ⟨j.val % N.A, Nat.mod_lt _ N.toPar.A_pos⟩)
      (if h : 0 < j.val then {Gate.car ⟨j.val - 1, by have := j.2; omega⟩} else ∅)

def rkG : Gate ι N.A → ℕ
  | .fa _ _ => 0
  | .mid _ => 1
  | .ib _ => 2
  | .car j => 3 + j.val

theorem hrkG : ∀ (g j : Gate ι N.A), j ∈ paG N g → rkG N j < rkG N g := by
  intro g j h
  cases g with
  | fa i s => simp [paG] at h
  | mid k => simp [paG] at h; obtain ⟨i, s, rfl⟩ := h; simp [rkG]
  | ib k => simp [paG] at h; obtain ⟨i, rfl⟩ := h; simp [rkG]
  | car c =>
    simp only [paG, mem_insert] at h
    rcases h with rfl | h
    · simp [rkG]; omega
    · split_ifs at h with h0
      · simp at h; subst h; simp [rkG]; omega
      · simp at h

/-- decode / encode the carry -/
def decC (q : Fin (2 ^ (N.M + 3))) : ℤ := (q.val : ℤ) - 2 ^ (N.M + 1)
def encC (q : ℤ) : Fin (2 ^ (N.M + 3)) := Fin.ofNat _ (q + 2 ^ (N.M + 1)).toNat

theorem decC_encC (q : ℤ) (h : |q| ≤ 2 ^ (N.M + 1)) : decC N (encC N q) = q := by
  unfold decC encC
  rw [Fin.val_ofNat]
  have h1 := abs_le.1 h
  have h2 : (0 : ℤ) ≤ q + 2 ^ (N.M + 1) := by linarith [h1.1]
  have h3 : (q + 2 ^ (N.M + 1)).toNat < 2 ^ (N.M + 3) := by
    have e : (2 : ℤ) ^ (N.M + 3) = 4 * 2 ^ (N.M + 1) := by ring
    have hp : (0 : ℤ) < 2 ^ (N.M + 1) := by positivity
    have : ((q + 2 ^ (N.M + 1)).toNat : ℤ) < ((2 ^ (N.M + 3) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h2]; push_cast; linarith [h1.2]
    exact_mod_cast this
  rw [Nat.mod_eq_of_lt h3]
  push_cast
  rw [Int.toNat_of_nonneg h2]; ring

end
end ECDLP.L38
end
