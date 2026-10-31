import ECDLP.L64_Edge
import ECDLP.L56_Edge

/-!
# L68 / Code: canonical (computable) codings of the message and free types of `edgeNet`

`E i : Msg i ≃ Fin (card (Msg i))` and `EF i : Free i ≃ Fin (card (Free i))` with no `Fintype.equivFin`:
* ring element (`ZMod q`): its `ZMod.val`;
* carry (`Fin (2^(M+3))`): the identity;
* slot digits (`Fin h → Fin (2^b)`): `finFunctionFinEquiv` (`code = Σ f i (2^b)^i`);
* `Unit`: `0`.
-/
noncomputable section
namespace ECDLP.L68
open Finset ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

/-- `ZMod q ≃ Fin q`, via `val` -/
def zEquiv (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := (i.val : ZMod q)
  left_inv x := by simp
  right_inv i := by
    apply Fin.ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]

def zCode (q : ℕ) [NeZero q] : ZMod q ≃ Fin (Fintype.card (ZMod q)) :=
  (zEquiv q).trans (finCongr (ZMod.card q).symm)

theorem zCode_val (q : ℕ) [NeZero q] (x : ZMod q) : (zCode q x : ℕ) = x.val := rfl

/-- `Fin n` coded by itself -/
def fCode (n : ℕ) : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin n).symm

theorem fCode_val (n : ℕ) (x : Fin n) : (fCode n x : ℕ) = x.val := rfl

/-- digit vectors: `code = Σ f i (2^b)^i` -/
def dCode (h b : ℕ) : (Fin h → Fin (2 ^ b)) ≃ Fin (Fintype.card (Fin h → Fin (2 ^ b))) :=
  finFunctionFinEquiv.trans (finCongr (by simp))

theorem dCode_digit (h b : ℕ) (c : Fin (Fintype.card (Fin h → Fin (2 ^ b))))
    (i : Fin h) : (((dCode h b).symm c) i : ℕ) = (c : ℕ) / (2 ^ b) ^ (i : ℕ) % 2 ^ b := rfl

def uCode : Unit ≃ Fin (Fintype.card Unit) where
  toFun _ := ⟨0, by simp⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by apply Fin.ext; have := i.2; simp at this ⊢; omega

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]

/-- the message coding of `edgeNet` -/
def edgeE : ∀ i : CG ι ιc N0.A, CM2 ι ιc N0 w i ≃ Fin (Fintype.card (CM2 ι ιc N0 w i))
  | .src _ _ => dCode N0.h N0.b
  | .gt c (Gate.fa _ _) => zCode (2 ^ (NP N0 w c).M + 1)
  | .gt c (Gate.mid _) => zCode (2 ^ (NP N0 w c).M + 1)
  | .gt c (Gate.ib _) => zCode (2 ^ (NP N0 w c).M + 1)
  | .gt c (Gate.car _) => fCode (2 ^ ((NP N0 w c).M + 3))

/-- the free-value coding of `edgeNet` -/
def edgeEF : ∀ i : CG ι ιc N0.A, CF ι ιc N0 i ≃ Fin (Fintype.card (CF ι ιc N0 i))
  | .src _ _ => dCode N0.h N0.b
  | .gt _ _ => uCode

end
end ECDLP.L68
end
