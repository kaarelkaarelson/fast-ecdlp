import ECDLP.L54_Comp

/-!
# L54 / Value: `Net.value` of the glued per-identity network
-/
noncomputable section
namespace ECDLP.L54
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- digits of the sources -/
def dC (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) : ι → Fin N0.A → Dg N0 := fun i s => x (.src i s)

/-- extension of digits by trivial free variables -/
def xC (d : ι → Fin N0.A → Dg N0) : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g
  | .src i s => d i s
  | .gt _ _ => ()

/-- digits seen by identity `c` -/
def dcOf (c : Fin K) (d : ι → Fin N0.A → Dg N0) : ιc c → Fin (NP N0 w c).A → Fin (NP N0 w c).h → Fin (2 ^ (NP N0 w c).b) :=
  fun j s => d (φ c j) s

/-- the claimed forced messages -/
def uC (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) : ∀ g : CG ι ιc N0.A, CM ι ιc N0 w g
  | .src i s => x (.src i s)
  | .gt c g => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) g

theorem toGS_eq (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) (c : Fin K) (g : Gate (ιc c) N0.A) :
    toGS (w := w) φ c g (x (.gt c g), fun j => uC (w := w) φ F x j.1) =
      (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)) g,
        fun q : {q // q ∈ paG (NP N0 w c) g} => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) q.1) := by
  refine Prod.ext ?_ rfl
  cases g with
  | fa j s => rfl
  | mid _ => rfl
  | ib _ => rfl
  | car _ => rfl

theorem uC_rec (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) :
    ∀ g, uC (w := w) φ F x g = (compNet (w := w) φ F ok).out g (x g, fun j => uC (w := w) φ F x j.1) := by
  intro g
  cases g with
  | src i s => rfl
  | gt c g =>
    have h := honest_rec (N := NP N0 w c) (F c) (hS c).1 hb (xOf (dcOf (w := w) φ c (dC x))) g
    show honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) g =
      outG (NP N0 w c) (F c) g (toGS (w := w) φ c g (x (.gt c g), fun j => uC (w := w) φ F x j.1))
    rw [toGS_eq]
    exact h

theorem tv_eq_uC (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) : (compNet (w := w) φ F ok).tv x = uC (w := w) φ F x :=
  ((compNet (w := w) φ F ok).tv_unique x _ (uC_rec φ F ok hS hb x)).symm

open Classical in
theorem comp_01 : ∀ (g : CG ι ιc N0.A) z, (compNet (w := w) φ F ok).W g z = 0 ∨ (compNet (w := w) φ F ok).W g z = 1 := by
  intro g z
  cases g with
  | src i s =>
    by_cases h : ok i s z.1
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  | gt c g => exact WG_01 (NP N0 w c) (fun _ _ _ => True) g (toGS (w := w) φ c g z)

theorem gadget_chk (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) (c : Fin K) :
    (∀ g, WG (NP N0 w c) (fun _ _ _ => True) g
        (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)) g,
          fun q => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) q.1) = 1) ↔
      (NP N0 w c).Holds (F c) ((NP N0 w c).dgOf (dcOf (w := w) φ c (dC x))) := by
  have key := checks_iff (N := NP N0 w c) (F c) (fun _ _ _ => True) (hS c).1 hb
    (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)))
  rw [tv_eq_honest (F c) (fun _ _ _ => True) (hS c).1 hb] at key
  refine key.trans ?_
  rw [← ((NP N0 w c).accept_iff (F c) (hS c).1 (hS c).2.1 (hS c).2.2 _)]
  simp only [implies_true, true_and]
  rfl

open Classical in
theorem checks_comp (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) :
    (∀ g, (compNet (w := w) φ F ok).W g (x g, fun j => (compNet (w := w) φ F ok).tv x j.1) = 1) ↔
      (∀ i s, ok i s (dC x i s)) ∧ ∀ c, (NP N0 w c).Holds (F c) ((NP N0 w c).dgOf (dcOf (w := w) φ c (dC x))) := by
  have hu := tv_eq_uC φ F ok hS hb x
  simp only [hu]
  have hgt : ∀ c g, (compNet (w := w) φ F ok).W (.gt c g) (x (.gt c g), fun j => uC (w := w) φ F x j.1) =
      WG (NP N0 w c) (fun _ _ _ => True) g
        (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)) g,
          fun q => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) q.1) := by
    intro c g
    exact congrArg (WG (NP N0 w c) (fun _ _ _ => True) g) (toGS_eq (w := w) φ F x c g)
  have hsrc : ∀ i s, (compNet (w := w) φ F ok).W (.src i s) (x (.src i s), fun j => uC (w := w) φ F x j.1) =
      if ok i s (x (.src i s)) then 1 else 0 := fun i s => rfl
  constructor
  · intro h
    refine ⟨fun i s => ?_, fun c => (gadget_chk φ F hS hb x c).1 (fun g => ?_)⟩
    · have := h (.src i s)
      have this := (hsrc i s).symm.trans this
      by_contra hn
      exact zero_ne_one (((if_neg (show ¬ ok i s (dC x i s) from hn)).symm.trans this))
    · have := h (.gt c g)
      exact (hgt c g).symm.trans this
  · rintro ⟨h1, h2⟩ g
    cases g with
    | src i s => exact (hsrc i s).trans (if_pos (h1 i s))
    | gt c g => rw [hgt]; exact (gadget_chk φ F hS hb x c).2 (h2 c) g

theorem card_freeC (P : (ι → Fin N0.A → Dg N0) → Prop) [DecidablePred P] :
    (univ.filter fun x : (∀ g : CG ι ιc N0.A, CF ι ιc N0 g) => P (dC x)).card =
      (univ.filter fun d : ι → Fin N0.A → Dg N0 => P d).card := by
  refine Finset.card_bij' (fun x _ => dC x) (fun d _ => xC (K := K) (ιc := ιc) d) ?_ ?_ ?_ ?_
  · intro x hx; simpa using hx
  · intro d hd
    have : dC (xC (K := K) (ιc := ιc) d) = d := rfl
    simpa [this] using hd
  · intro x _
    funext g
    cases g with
    | src _ _ => rfl
    | gt _ _ => rfl
  · intro d _; rfl

theorem holds_NP (c : Fin K) (G : Form (ιc c)) (dg : ιc c → Fin N0.A → Dg N0) :
    (NP N0 w c).Holds G ((NP N0 w c).dgOf dg) ↔ N0.Holds G (N0.dgOf dg) := Iff.rfl

/-- filter cardinalities agree for equivalent predicates, with the decidability instances explicit -/
theorem card_congr_pred {α : Type*} [Fintype α] (p q : α → Prop) (dp : DecidablePred p) (dq : DecidablePred q)
    (h : ∀ x, p x ↔ q x) : (univ.filter p).card = (univ.filter q).card := by
  have : univ.filter p = univ.filter q := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h x
  rw [this]

open Classical in
/-- **Composition theorem.**  The glued per-identity network has `Net.value` equal to the number of digit
assignments of the shared slots passing the source checks `ok` and satisfying every identity `F c` (in its own
ring `Z/(2^{M_c}+1)`, `M_c = 2^k w_c`, on the slots `φ c` it reads). -/
theorem comp_value (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ((((compNet (w := w) φ F ok).toForced.toGNet).toNet e).value) =
      ((univ.filter fun d : ι → Fin N0.A → Dg N0 =>
        (∀ i s, ok i s (d i s)) ∧
          ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card : ℤ) := by
  rw [(compNet (w := w) φ F ok).tforced_value e (fun g z => comp_01 φ F ok g z)]
  congr 1
  rw [← card_freeC (K := K) (ιc := ιc) (fun d => (∀ i s, ok i s (d i s)) ∧
    ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j))))]
  have hh : ∀ x : (∀ g : CG ι ιc N0.A, CF ι ιc N0 g),
      (∀ g, (compNet (w := w) φ F ok).W g (x g, fun j => (compNet (w := w) φ F ok).tv x j.1) = 1) ↔
      ((∀ i s, ok i s (dC x i s)) ∧ ∀ c, N0.Holds (F c) (N0.dgOf (fun j => dC x (φ c j)))) := by
    intro x
    refine (checks_comp φ F ok hS hb x).trans ?_
    have h : (∀ c, (NP N0 w c).Holds (F c) ((NP N0 w c).dgOf (dcOf (w := w) φ c (dC x)))) ↔
        ∀ c, N0.Holds (F c) (N0.dgOf fun j => dC x (φ c j)) :=
      forall_congr' fun c => holds_NP (w := w) c (F c) (fun j s => dC x (φ c j) s)
    exact and_congr Iff.rfl h
  exact card_congr_pred _ _ _ _ hh

end
end ECDLP.L54
end
