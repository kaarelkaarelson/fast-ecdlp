import ECDLP.L38_Net
import ECDLP.L34_Final

/-!
# L38 / Count: **the gadget's Net.value is the number of digit assignments satisfying the identity**
-/
noncomputable section
namespace ECDLP.L38
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 Gate

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : NPar} (F : Form ι)

/-- digits of the free variables of the `fa` gates -/
def dOf (x : ∀ g : Gate ι N.A, FreeT N g) : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) :=
  fun i s => (x (Gate.fa i s) : Fin N.h → Fin (2 ^ N.b))

/-- the honest messages -/
def honest (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) : ∀ g : Gate ι N.A, MsgT N g
  | .fa i s => fun k => N.faMsgS (d i s) s k
  | .mid k => fun j₁ => NPar.ibS F d j₁ k
  | .ib j₁ => fun j₂ => ibOut N.A N.ωi N.tInv
      (NPar.exA (fun k : Fin N.A => NPar.ibS F d j₁ k)) j₂
  | .car j => encC N (NPar.carS N.b (fun j' => (NPar.coefS F d j').valMinAbs) (j.val + 1))

theorem carS_bound (hM : 1 ≤ N.M) (hb : 1 ≤ N.b) (c : ℕ → ℤ) (hc : ∀ j, |c j| ≤ 2 ^ N.M) :
    ∀ j, |NPar.carS N.b c j| ≤ 2 ^ (N.M + 1) := by
  intro j
  induction j with
  | zero => simp [NPar.carS]
  | succ j ih =>
    show |(NPar.carS N.b c j + c j) / 2 ^ N.b| ≤ _
    set a := NPar.carS N.b c j + c j with ha
    have h1 := abs_le.1 ih
    have h2 := abs_le.1 (hc j)
    have hT : (2 : ℤ) ≤ 2 ^ N.M := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N.M := pow_le_pow_right₀ (by norm_num) hM
    have hm : (2 : ℤ) ≤ 2 ^ N.b := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N.b := pow_le_pow_right₀ (by norm_num) hb
    have hpos : (0 : ℤ) < 2 ^ N.b := by linarith
    have e1 := Int.ediv_mul_le a hpos.ne'
    have e2 := Int.lt_ediv_add_one_mul_self a hpos
    set q := a / 2 ^ N.b
    have hp : (2 : ℤ) ^ (N.M + 1) = 2 * 2 ^ N.M := by ring
    rw [abs_le, hp]
    constructor
    · by_contra hcon
      push_neg at hcon
      nlinarith
    · by_contra hcon
      push_neg at hcon
      nlinarith

theorem abs_valMinAbs_le (c : N.Rg) : |c.valMinAbs| ≤ 2 ^ N.M := by
  have h := ZMod.natAbs_valMinAbs_le c
  rw [Int.abs_eq_natAbs]
  have : (2 ^ N.M + 1) / 2 ≤ 2 ^ N.M := by
    have := Nat.one_le_two_pow (n := N.M); omega
  have h2 : (c.valMinAbs).natAbs ≤ 2 ^ N.M := h.trans this
  exact_mod_cast h2

theorem honest_rec (hM : 1 ≤ N.M) (hb : 1 ≤ N.b) (x : ∀ g : Gate ι N.A, FreeT N g) :
    ∀ g, honest F (dOf x) g = outG N F g (x g, fun q => honest F (dOf x) q.1) := by
  intro g
  have hbd := carS_bound hM hb (fun j' => (NPar.coefS F (dOf x) j').valMinAbs)
    (fun j => abs_valMinAbs_le _)
  cases g with
  | fa i s => rfl
  | mid k => rfl
  | ib j => rfl
  | car j =>
    have hcf : cfOf N j (fun q => honest F (dOf x) q.1) =
        (NPar.coefS F (dOf x) j.val).valMinAbs := rfl
    have hcin : cinOf N j (fun q => honest F (dOf x) q.1) =
        NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) j.val := by
      unfold cinOf
      split_ifs with h0
      · show decC N (encC N (NPar.carS N.b _ (j.val - 1 + 1))) = _
        rw [decC_encC N _ (hbd _), Nat.sub_add_cancel h0]
      · have : j.val = 0 := by omega
        rw [this]; rfl
    show encC N _ = encC N ((cinOf N j _ + cfOf N j _) / 2 ^ N.b)
    rw [hcin, hcf]
    rfl

theorem tv_eq_honest (ok : ι → Fin N.A → (Fin N.h → Fin (2 ^ N.b)) → Prop) (hM : 1 ≤ N.M) (hb : 1 ≤ N.b) (x : ∀ g : Gate ι N.A, FreeT N g) :
    (gadgetNet N F ok).tv x = honest F (dOf x) :=
  ((gadgetNet N F ok).tv_unique x _ (honest_rec F hM hb x)).symm

end
end ECDLP.L38
end
