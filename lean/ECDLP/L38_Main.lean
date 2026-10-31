import ECDLP.L38_Count

/-!
# L38 / Main: `Net.value` of the gadget = number of digit assignments satisfying the integer identity
-/
noncomputable section
namespace ECDLP.L38
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 Gate

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : NPar} (F : Form ι)
  (ok : ι → Fin N.A → (Fin N.h → Fin (2 ^ N.b)) → Prop)

/-- chain conditions in terms of carries -/
theorem accept_iff_chain (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) :
    N.accept F (N.dgOf d) ↔
      (∀ j, j < N.A * N.A → (2 ^ N.b : ℤ) ∣ NPar.carS N.b (fun j' => (NPar.coefS F d j').valMinAbs) j +
          (NPar.coefS F d j).valMinAbs) ∧
      NPar.carS N.b (fun j' => (NPar.coefS F d j').valMinAbs) (N.A * N.A) = 0 := by
  set c' : ℕ → ℤ := fun j => (NPar.coefS F d j).valMinAbs with hc'
  have hcar : ∀ j, NPar.carS N.b c' (j + 1) = (NPar.carS N.b c' j + c' j) / 2 ^ N.b := fun j => rfl
  have hacc : N.accept F (N.dgOf d) ↔ chainZ N.b c' (N.A * N.A) 0 (NPar.carS N.b c' 0) := by
    unfold Par.accept
    have e1 := chainZ_iff N.b (fun j => (N.coef F (N.dgOf d) j).valMinAbs) (N.A * N.A) 0 0
    have e2 := chainZ_iff N.b c' (N.A * N.A) 0 (NPar.carS N.b c' 0)
    have : ∑ j ∈ range (N.A * N.A), (N.coef F (N.dgOf d) (0 + j)).valMinAbs * 2 ^ (N.b * j) =
        ∑ j ∈ range (N.A * N.A), c' (0 + j) * 2 ^ (N.b * j) := by
      refine sum_congr rfl fun j hj => ?_
      rw [zero_add]; show _ = (NPar.coefS F d j).valMinAbs * _; rw [NPar.coefS_eq]
    change chainZ N.b (fun j => (N.coef F (N.dgOf d) j).valMinAbs) (N.A * N.A) 0 0 ↔ _
    rw [e1, e2, this]; rfl
  rw [hacc, chainZ_car N.b c' (NPar.carS N.b c') hcar]
  simp only [zero_add, Nat.zero_le, true_imp_iff]
  rfl

/-- all local checks of the gadget hold on the honest messages iff the chain conditions hold -/
theorem checks_iff (hM : 1 ≤ N.M) (hb : 1 ≤ N.b) (x : ∀ g : Gate ι N.A, FreeT N g) :
    (∀ g, WG N ok g (x g, fun q => (gadgetNet N F ok).tv x q.1) = 1) ↔
      (∀ i s, ok i s (dOf x i s)) ∧ N.accept F (N.dgOf (dOf x)) := by
  rw [tv_eq_honest F ok hM hb x, accept_iff_chain F]
  have hbd := carS_bound hM hb (fun j' => (NPar.coefS F (dOf x) j').valMinAbs)
    (fun j => abs_valMinAbs_le _)
  have hcf : ∀ j : Fin (N.A * N.A), cfOf N j (fun q => honest F (dOf x) q.1) =
        (NPar.coefS F (dOf x) j.val).valMinAbs := fun j => rfl
  have hcin : ∀ j : Fin (N.A * N.A), cinOf N j (fun q => honest F (dOf x) q.1) =
        NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) j.val := by
    intro j
    unfold cinOf
    split_ifs with h0
    · show decC N (encC N (NPar.carS N.b _ (j.val - 1 + 1))) = _
      rw [decC_encC N _ (hbd _), Nat.sub_add_cancel h0]
    · have : j.val = 0 := by omega
      rw [this]; rfl
  have hq : ∀ j : ℕ, (NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) j +
      (NPar.coefS F (dOf x) j).valMinAbs) / 2 ^ N.b =
      NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) (j + 1) := fun j => rfl
  have hfa : ∀ i s, WG N ok (Gate.fa i s) (x (Gate.fa i s), fun q => honest F (dOf x) q.1) = 1 ↔
      ok i s (dOf x i s) := by
    intro i s
    simp only [WG, dOf]
    split_ifs with h <;> simp [h]
  constructor
  · intro h
    refine ⟨fun i s => (hfa i s).1 (h _), ?_⟩
    have hc : ∀ j : Fin (N.A * N.A), WG N ok (Gate.car j) (x (Gate.car j), fun q => honest F (dOf x) q.1) = 1 :=
      fun j => h _
    have hc' : ∀ j : Fin (N.A * N.A), ((2 ^ N.b : ℤ) ∣ NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) j +
          (NPar.coefS F (dOf x) j).valMinAbs) ∧ (j.val + 1 = N.A * N.A →
        NPar.carS N.b (fun j' => (NPar.coefS F (dOf x) j').valMinAbs) (j.val + 1) = 0) := by
      intro j
      have := hc j
      simp only [WG, hcin, hcf, hq] at this
      by_contra hn
      rw [if_neg hn] at this
      exact zero_ne_one this
    refine ⟨fun j hj => (hc' ⟨j, hj⟩).1, ?_⟩
    have hpos : 0 < N.A * N.A := Nat.mul_pos N.toPar.A_pos N.toPar.A_pos
    have := (hc' ⟨N.A * N.A - 1, by omega⟩).2 (by simp; omega)
    simpa [Nat.sub_add_cancel hpos] using this
  · rintro ⟨hok, h1, h2⟩ g
    cases g with
    | fa i s => exact (hfa i s).2 (hok i s)
    | mid _ => rfl
    | ib _ => rfl
    | car j =>
      simp only [WG, hcin, hcf, hq]
      rw [if_pos]
      refine ⟨h1 j.val j.2, fun hj => ?_⟩
      rw [hj]; exact h2

/-- extension of a digit assignment by trivial free variables -/
def xOf (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) : ∀ g : Gate ι N.A, FreeT N g
  | .fa i s => d i s
  | .mid _ => ()
  | .ib _ => ()
  | .car _ => ()

theorem card_free (P : (ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) → Prop) [DecidablePred P] :
    (univ.filter fun x : (∀ g : Gate ι N.A, FreeT N g) => P (dOf x)).card =
      (univ.filter fun d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) => P d).card := by
  refine Finset.card_bij' (fun x _ => dOf x) (fun d _ => xOf d) ?_ ?_ ?_ ?_
  · intro x hx; simpa using hx
  · intro d hd
    have : dOf (xOf d) = d := rfl
    simpa [this] using hd
  · intro x _
    funext g
    cases g with
    | fa _ _ => rfl
    | mid _ => rfl
    | ib _ => rfl
    | car _ => rfl
  · intro d _; rfl

open Classical in
/-- **Main theorem (1).**  L34's gadget, as a forced network `gadgetNet` on Rudich's `GNet`/`Net`
framework, with an extra `0/1` local check `ok i s` on the free digit slice of each FA gate, has `Net.value`
equal to the number of digit assignments (one `h`-digit slice per `(slot, s < A)` gate) passing all the
`ok` checks and satisfying the integer identity `Σ ε_t · val(l_t) · val(r_t) = 0`. -/
theorem gadget_value_ok (hS : N.SizeOK F) (hb : 1 ≤ N.b) {g : ℕ} (e : Gate ι N.A ≃ Fin g) :
    (((gadgetNet N F ok).toForced.toGNet).toNet e).value =
      ((univ.filter fun d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) =>
        (∀ i s, ok i s (d i s)) ∧ N.Holds F (N.dgOf d)).card : ℤ) := by
  rw [(gadgetNet N F ok).tforced_value e (fun g z => WG_01 N ok g z)]
  congr 1
  rw [← card_free (fun d => (∀ i s, ok i s (d i s)) ∧ N.Holds F (N.dgOf d))]
  have key : ∀ x : (∀ g : Gate ι N.A, (gadgetNet N F ok).Free g),
      (∀ g, (gadgetNet N F ok).W g (x g, fun j => (gadgetNet N F ok).tv x j.1) = 1) ↔
        ((∀ i s, ok i s (dOf x i s)) ∧ N.Holds F (N.dgOf (dOf x))) := fun x =>
    (checks_iff F ok hS.1 hb x).trans (and_congr Iff.rfl
      (N.accept_iff F hS.1 hS.2.1 hS.2.2 (N.dgOf (dOf x))))
  simp only [key]
  congr

open Classical in
/-- **Main theorem (1), plain form** (no extra checks): `Net.value` of the gadget network is the number of
digit assignments satisfying the integer identity. -/
theorem gadget_value (hS : N.SizeOK F) (hb : 1 ≤ N.b) {g : ℕ} (e : Gate ι N.A ≃ Fin g) :
    (((gadgetNet N F (fun _ _ _ => True)).toForced.toGNet).toNet e).value =
      ((univ.filter fun d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) => N.Holds F (N.dgOf d)).card : ℤ) := by
  rw [gadget_value_ok F (fun _ _ _ => True) hS hb e]
  simp only [implies_true, true_and]

end
end ECDLP.L38
end

#print axioms ECDLP.L38.TForced.tforced_value
#print axioms ECDLP.L38.gadget_value
#print axioms ECDLP.L38.gadget_value_ok
#check @ECDLP.L38.gadget_value
#check @ECDLP.L38.gadget_value_ok
