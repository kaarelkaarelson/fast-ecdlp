import ECDLP.L34_Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# L34 / Final: main theorems

* `gadget_accept_iff` (L34_Main, restated): functional gate-level run accepts iff the integer identity holds.
* `good_iff`: in the network, a setting is good iff it is the honest run of its FA settings and the identity holds.
* `good_ncard`: number of good settings = number of FA settings (digit assignments) satisfying the identity.
* `prod_accept_iff`: the single product `u * v = r` (slot 3 is the constant `1`).
-/
namespace ECDLP.L34

open Finset Factoring.Aux

variable {ι : Type}

namespace NPar
variable {N : NPar} (F : Form ι)

/-- Size condition: ring exponent, transform length, digit and coefficient bounds. -/
def SizeOK (N : NPar) (F : Form ι) : Prop :=
  1 ≤ N.M ∧ 2 * 2 ^ N.k ≤ N.A * N.A ∧ 2 * (Form.mass F * (2 ^ N.k * (2 ^ N.b * 2 ^ N.b))) ≤ 2 ^ N.M

/-- **Main theorem (network).** A global setting of the gadget's gates has all edge messages consistent and
all weights `1` iff it is the honest run of its FA settings and the digits satisfy the integer identity. -/
theorem good_iff (hS : N.SizeOK F) (a : Asg ι N) :
    Good F a ↔ a = run F a.fa ∧ N.Holds F (N.dgOf a.fa) := by
  constructor
  · intro h
    have hp := good_pinned h
    refine ⟨hp, ?_⟩
    have hr : Good F (run F a.fa) := by rw [← hp]; exact h
    rw [good_run_iff F] at hr
    exact (N.accept_iff F hS.1 hS.2.1 hS.2.2 _).1 hr
  · rintro ⟨hp, hh⟩
    rw [hp]
    rw [good_run_iff F]
    exact (N.accept_iff F hS.1 hS.2.1 hS.2.2 _).2 hh

/-- **Counting form.** The number of good settings equals the number of FA settings (digit assignments of all
slots) satisfying the integer identity. -/
theorem good_ncard (hS : N.SizeOK F) :
    {a : Asg ι N | Good F a}.ncard = {d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) | N.Holds F (N.dgOf d)}.ncard := by
  have himg : {a : Asg ι N | Good F a} = (run F) '' {d | N.Holds F (N.dgOf d)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_image]
    rw [good_iff F hS]
    constructor
    · rintro ⟨hp, hh⟩; exact ⟨a.fa, hh, hp.symm⟩
    · rintro ⟨d, hd, rfl⟩; exact ⟨rfl, hd⟩
  have hinj : Function.Injective (run (N := N) F) := fun d d' h => congrArg Asg.fa h
  rw [himg, Set.ncard_image_of_injective _ hinj]

end NPar

/-! ### The single product -/

/-- `u * v - r * o`, slots `0 = u`, `1 = v`, `2 = r`, `3 = o` (the constant `1`). -/
def prodForm : Form (Fin 4) where
  n := 2
  l := ![0, 2]
  r := ![1, 3]
  ε := ![1, -1]

theorem prodForm_mass : Form.mass prodForm = 2 := by
  unfold Form.mass
  change ∑ t : Fin 2, ((![1, -1] : Fin 2 → ℤ) t).natAbs = 2
  simp [Fin.sum_univ_two]

theorem prod_holds_iff (P : Par) (dg : Fin 4 → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (ho : P.val (dg 3) = 1) :
    P.Holds prodForm dg ↔ P.val (dg 0) * P.val (dg 1) = P.val (dg 2) := by
  unfold Par.Holds
  change ∑ t : Fin 2, ((![1, -1] : Fin 2 → ℤ) t) * ((P.val (dg ((![0, 2] : Fin 2 → Fin 4) t)) : ℤ) *
    (P.val (dg ((![1, 3] : Fin 2 → Fin 4) t)) : ℤ)) = 0 ↔ _
  simp [Fin.sum_univ_two, ho]
  constructor <;> intro h <;> linarith

/-- **Single product `u * v = r`**: the gadget (two transform layers, one inverse transform, signed carry chain)
accepts iff the integers are equal. -/
theorem prod_accept_iff (P : Par) (hM : 1 ≤ P.M) (hD : 2 * 2 ^ P.k ≤ P.A * P.A)
    (hb : 2 * (2 * (2 ^ P.k * (2 ^ P.b * 2 ^ P.b))) ≤ 2 ^ P.M)
    (dg : Fin 4 → Fin (2 ^ P.k) → Fin (2 ^ P.b)) (ho : P.val (dg 3) = 1) :
    P.accept prodForm dg ↔ P.val (dg 0) * P.val (dg 1) = P.val (dg 2) := by
  rw [P.accept_iff prodForm hM hD (by rw [prodForm_mass]; exact hb), prod_holds_iff P dg ho]

/-! ### Non-vacuity: concrete parameters satisfy all size conditions -/

/-- `k = 1`, `A = 2`, `h = 1`, `w = 3` (ring `Z/65`), `b = 1`. -/
def exN : NPar where
  k := 1
  A := 2
  w := 3
  b := 1
  hA := by norm_num
  h := 1
  hAh := by norm_num

example : exN.SizeOK prodForm := by
  refine ⟨by simp [Par.M, exN], by simp [exN], ?_⟩
  rw [prodForm_mass]; simp [Par.M, exN]

end ECDLP.L34

#print axioms ECDLP.L34.NPar.good_iff
#print axioms ECDLP.L34.NPar.good_ncard
#print axioms ECDLP.L34.Par.accept_iff
#print axioms ECDLP.L34.prod_accept_iff
#print axioms ECDLP.L34.ib_mid_fa_gen
#print axioms ECDLP.L34.chainZ_iff
