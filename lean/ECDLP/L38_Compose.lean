import ECDLP.L38_Main

/-!
# L38 / Compose: several integer identities on shared operand slots in one forced network

A family of quadratic forms `F c` (`c : Fin K`) over the same slots is combined into ONE form
`combine F B = Σ_c B^c · F c` (base `B` larger than the absolute value of every `F c`); then
`Σ_c B^c H_c = 0 ⇔ ∀ c, H_c = 0` (`base_zero`).  Together with the per-FA-gate checks `ok` (pinned constant
digits, digit-range checks) the network `gadgetNet N (combine F B) ok` has `Net.value` equal to the number
of digit assignments with `ok` and *all* identities (`system_value`).  The operand slots are shared:
each slot is a single set of FA gates feeding every identity.
-/
noncomputable section
namespace ECDLP.L38
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35

section
variable {ι : Type} {K : ℕ}

/-- the value of a form on a digit assignment -/
def Hval (P : Par) (F : Form ι) (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) : ℤ :=
  ∑ t : Fin F.n, F.ε t * ((P.val (dg (F.l t)) : ℤ) * (P.val (dg (F.r t)) : ℤ))

theorem holds_iff_Hval (P : Par) (F : Form ι) (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) :
    P.Holds F dg ↔ Hval P F dg = 0 := Iff.rfl

/-- the combined form `Σ_c B^c F c` -/
def combine (F : Fin K → Form ι) (B : ℤ) : Form ι where
  n := Fintype.card (Σ c : Fin K, Fin (F c).n)
  l t := (fun s : (Σ c : Fin K, Fin (F c).n) => (F s.1).l s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm t)
  r t := (fun s : (Σ c : Fin K, Fin (F c).n) => (F s.1).r s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm t)
  ε t := (fun s : (Σ c : Fin K, Fin (F c).n) => B ^ (s.1 : ℕ) * (F s.1).ε s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm t)

theorem combine_l (F : Fin K → Form ι) (B : ℤ) (s : Σ c : Fin K, Fin (F c).n) :
    (combine F B).l (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s) = (F s.1).l s.2 := by
  show (fun s : (Σ c : Fin K, Fin (F c).n) => (F s.1).l s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm
      (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s)) = _
  rw [Equiv.symm_apply_apply]

theorem combine_r (F : Fin K → Form ι) (B : ℤ) (s : Σ c : Fin K, Fin (F c).n) :
    (combine F B).r (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s) = (F s.1).r s.2 := by
  show (fun s : (Σ c : Fin K, Fin (F c).n) => (F s.1).r s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm
      (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s)) = _
  rw [Equiv.symm_apply_apply]

theorem combine_ε (F : Fin K → Form ι) (B : ℤ) (s : Σ c : Fin K, Fin (F c).n) :
    (combine F B).ε (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s) = B ^ (s.1 : ℕ) * (F s.1).ε s.2 := by
  show (fun s : (Σ c : Fin K, Fin (F c).n) => B ^ (s.1 : ℕ) * (F s.1).ε s.2)
    ((Fintype.equivFin (Σ c : Fin K, Fin (F c).n)).symm
      (Fintype.equivFin (Σ c : Fin K, Fin (F c).n) s)) = _
  rw [Equiv.symm_apply_apply]

theorem Hval_combine (P : Par) (F : Fin K → Form ι) (B : ℤ)
    (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) :
    Hval P (combine F B) dg = ∑ c : Fin K, B ^ (c : ℕ) * Hval P (F c) dg := by
  unfold Hval
  refine ((Equiv.sum_comp (Fintype.equivFin (Σ c : Fin K, Fin (F c).n))
    (fun t : Fin (combine F B).n => (combine F B).ε t *
      ((P.val (dg ((combine F B).l t)) : ℤ) * (P.val (dg ((combine F B).r t)) : ℤ)))).symm).trans ?_
  simp only [combine_l, combine_r, combine_ε]
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  ring

theorem base_zero : ∀ (K : ℕ) (B : ℤ) (E : Fin K → ℤ), 0 < B → (∀ c, |E c| < B) →
    (∑ c : Fin K, B ^ (c : ℕ) * E c = 0 ↔ ∀ c, E c = 0)
  | 0, B, E, _, _ => by simp
  | K + 1, B, E, hB, hE => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    have e : ∑ i : Fin K, B ^ (i : ℕ) * B * E i.succ = B * ∑ i : Fin K, B ^ (i : ℕ) * E i.succ := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [e]
    have ih := base_zero K B (fun i => E i.succ) hB (fun i => hE _)
    constructor
    · intro h
      have hd : B ∣ E 0 := ⟨-(∑ i : Fin K, B ^ (i : ℕ) * E i.succ), by linarith⟩
      have h0 : E 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (hE 0)
      rw [h0, zero_add] at h
      have h1 : ∑ i : Fin K, B ^ (i : ℕ) * E i.succ = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h hB.ne'
        · exact h
      have := ih.1 h1
      intro c
      refine Fin.cases h0 (fun i => this i) c
    · intro h
      rw [h 0, (ih.2 (fun i => h _))]; simp

theorem val_lt (P : Par) (x : Fin (2 ^ P.k) → Fin (2 ^ P.b)) : P.val x < 2 ^ (P.b * 2 ^ P.k) :=
  numOf_lt P.b (P.sq x) (P.sq_lt x) _

theorem Hval_abs_le (P : Par) (F : Form ι) (dg : ι → Fin (2 ^ P.k) → Fin (2 ^ P.b)) :
    |Hval P F dg| ≤ (F.mass : ℤ) * ((2 ^ (P.b * 2 ^ P.k) : ℕ) : ℤ) ^ 2 := by
  unfold Hval Form.mass
  refine (abs_sum_le_sum_abs _ _).trans ?_
  push_cast
  rw [sum_mul]
  refine sum_le_sum fun t _ => ?_
  rw [abs_mul, Int.abs_eq_natAbs (F.ε t)]
  have h1 : ((P.val (dg (F.l t)) : ℤ)) ≤ ((2 ^ (P.b * 2 ^ P.k) : ℕ) : ℤ) :=
    by exact_mod_cast (val_lt P _).le
  have h2 : ((P.val (dg (F.r t)) : ℤ)) ≤ ((2 ^ (P.b * 2 ^ P.k) : ℕ) : ℤ) :=
    by exact_mod_cast (val_lt P _).le
  have h0 : (0 : ℤ) ≤ (P.val (dg (F.l t)) : ℤ) := by positivity
  have h0' : (0 : ℤ) ≤ (P.val (dg (F.r t)) : ℤ) := by positivity
  rw [abs_of_nonneg (mul_nonneg h0 h0')]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  push_cast at h1 h2
  rw [sq]
  exact mul_le_mul h1 h2 h0' (by positivity)

variable [Fintype ι] [DecidableEq ι]

theorem holds_combine (N : NPar) (F : Fin K → Form ι) (B : ℤ) (hB : 0 < B)
    (hBd : ∀ c, ((F c).mass : ℤ) * ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B)
    (dg : ι → Fin (2 ^ N.k) → Fin (2 ^ N.b)) :
    N.Holds (combine F B) dg ↔ ∀ c, N.Holds (F c) dg := by
  rw [holds_iff_Hval, Hval_combine]
  simp only [holds_iff_Hval]
  exact base_zero K B (fun c => Hval N.toPar (F c) dg) hB
    (fun c => lt_of_le_of_lt (Hval_abs_le N.toPar (F c) dg) (hBd c))

open Classical in
/-- **Composition of identities over shared operands (2).**  `K` integer identities `F c` on the same slots,
combined into one gadget network with per-FA-gate checks `ok` (constants, digit ranges):
`Net.value` = number of digit assignments passing `ok` and all `K` identities. -/
theorem system_value (N : NPar) (F : Fin K → Form ι)
    (ok : ι → Fin N.A → (Fin N.h → Fin (2 ^ N.b)) → Prop) (B : ℤ) (hB : 0 < B)
    (hBd : ∀ c, ((F c).mass : ℤ) * ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B)
    (hS : N.SizeOK (combine F B)) (hb : 1 ≤ N.b) {g : ℕ} (e : Gate ι N.A ≃ Fin g) :
    (((gadgetNet N (combine F B) ok).toForced.toGNet).toNet e).value =
      ((univ.filter fun d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) =>
        (∀ i s, ok i s (d i s)) ∧ ∀ c, N.Holds (F c) (N.dgOf d)).card : ℤ) := by
  rw [gadget_value_ok (combine F B) ok hS hb e]
  congr 2
  ext d
  simp only [mem_filter, mem_univ, true_and, holds_combine N F B hB hBd]

end
end ECDLP.L38
end

#print axioms ECDLP.L38.system_value
#check @ECDLP.L38.system_value
