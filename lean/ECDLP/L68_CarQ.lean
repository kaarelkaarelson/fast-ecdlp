import ECDLP.L68_Car
import ECDLP.L68_Code
import ECDLP.L58_Edge

/-!
# L68 / CarQ: the car gate of `edgeNetM` at the node level (`q` a variable, no enumeration)

`out_car_q`: for a node `q = gt c (car j)` and a setting `z : S q`, the CODE (`edgeE`) of the message sent is
`(encC N (sZ N j ci r / 2^b)).val` with `ci`, `r` the codes of the messages of the two parents
(`ci = 0` for `j = 0`).  `w_car_q`: the weight (`0/1` in `ZMod m`) is the test of `eval_carWE`.
-/
noncomputable section
namespace ECDLP.L68
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem car_prev_mem (c : Fin K) (j : Fin (N0.A * N0.A)) (h : 0 < j.val) :
    CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩) ∈ paC (w := w) φ (CG.gt c (Gate.car j)) :=
  mem_paC_gt φ c (Finset.mem_insert_of_mem (by rw [dif_pos h]; exact Finset.mem_singleton_self _))

theorem car_ib_mem (c : Fin K) (j : Fin (N0.A * N0.A)) :
    CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩) ∈ paC (w := w) φ (CG.gt c (Gate.car j)) :=
  mem_paC_gt φ c (Finset.mem_insert_self _ _)

/-- `edgeE` as the coding of the messages of `edgeNetM m` -/
def edgeEM (m : ℕ) : ∀ i, (edgeNetM (w := w) φ F ok m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Msg i)) :=
  fun i => edgeE (w := w) i

def edgeEFM (m : ℕ) : ∀ i, (edgeNetM (w := w) φ F ok m).Free i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Free i)) :=
  fun i => edgeEF i

/-- numeric code of a message -/
def ec (i : CG ι ιc N0.A) (x : CM2 ι ιc N0 w i) : ℕ := (edgeE i x : ℕ)

/-- code of the message that parent `p` sent in the setting `z` of node `q` (`0` if `p` is not a parent) -/
def pm (m : ℕ) {q : CG ι ιc N0.A} (z : (edgeNetM (w := w) φ F ok m).S q) (p : CG ι ιc N0.A) : ℕ :=
  if hp : p ∈ paC (w := w) φ q then ec (ι := ι) (ιc := ιc) (w := w) p (z.2 ⟨p, hp⟩) else 0

/-- the previous-carry and ring codes read by `car c j` -/
def carCiQ (m : ℕ) (c : Fin K) (j : Fin (N0.A * N0.A)) {q : CG ι ιc N0.A} (z : (edgeNetM (w := w) φ F ok m).S q) : ℕ :=
  if 0 < j.val then pm (w := w) φ F ok m z (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) else 0

def carRQ (m : ℕ) (c : Fin K) (j : Fin (N0.A * N0.A)) {q : CG ι ιc N0.A} (z : (edgeNetM (w := w) φ F ok m).S q) : ℕ :=
  pm (w := w) φ F ok m z (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩))

theorem out_car_q (m : ℕ) (c : Fin K) (j : Fin (N0.A * N0.A)) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.car j))
    (z : (edgeNetM (w := w) φ F ok m).S q) (ch : CG ι ιc N0.A) :
    ec (ι := ι) (ιc := ιc) (w := w) q ((edgeNetM (w := w) φ F ok m).out q z ch) =
      (encC (NP N0 w c) (sZ (NP N0 w c) j.val (carCiQ (w := w) φ F ok m c j z) (carRQ (w := w) φ F ok m c j z) /
        2 ^ (NP N0 w c).b)).val := by
  subst hq
  have h1 : carCiQ (w := w) φ F ok m c j z = carCi (w := w) φ c j z := by
    unfold carCiQ carCi pm
    by_cases h : 0 < j.val
    · simp only [h, if_true, dif_pos, car_prev_mem φ c j h]; rfl
    · simp [h]
  have h2 : carRQ (w := w) φ F ok m c j z = carR (w := w) φ c j z := by
    unfold carRQ carR pm
    simp only [car_ib_mem (w := w) φ c j, dif_pos]; rfl
  rw [h1, h2]
  exact car_out_sem (w := w) φ F c j z ch

open Classical in
theorem w_car_q (m : ℕ) (hm1 : 1 < m) (c : Fin K) (j : Fin (N0.A * N0.A)) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.car j))
    (z : (edgeNetM (w := w) φ F ok m).S q) :
    (if (edgeNetM (w := w) φ F ok m).W q z = 1 then 1 else 0 : ℕ) =
      if ((2 ^ (NP N0 w c).b : ℤ) ∣ sZ (NP N0 w c) j.val (carCiQ (w := w) φ F ok m c j z) (carRQ (w := w) φ F ok m c j z) ∧
        (j.val + 1 = (NP N0 w c).A * (NP N0 w c).A →
          sZ (NP N0 w c) j.val (carCiQ (w := w) φ F ok m c j z) (carRQ (w := w) φ F ok m c j z) / 2 ^ (NP N0 w c).b = 0))
      then 1 else 0 := by
  have : Fact (1 < m) := ⟨hm1⟩
  subst hq
  have h1 : carCiQ (w := w) φ F ok m c j z = carCi (w := w) φ c j z := by
    unfold carCiQ carCi pm
    by_cases h : 0 < j.val
    · simp only [h, if_true, dif_pos, car_prev_mem φ c j h]; rfl
    · simp [h]
  have h2 : carRQ (w := w) φ F ok m c j z = carR (w := w) φ c j z := by
    unfold carRQ carR pm
    simp only [car_ib_mem (w := w) φ c j, dif_pos]; rfl
  rw [h1, h2]
  have hw := car_w_sem (w := w) φ ok c j z
  have hW : (edgeNetM (w := w) φ F ok m).W (CG.gt c (Gate.car j)) z =
      (Int.castRingHom (ZMod m)) (WE (w := w) φ ok (CG.gt c (Gate.car j)) z) := rfl
  rw [hW, hw]
  by_cases hc : ((2 ^ (NP N0 w c).b : ℤ) ∣ sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) ∧
        (j.val + 1 = (NP N0 w c).A * (NP N0 w c).A →
          sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) / 2 ^ (NP N0 w c).b = 0))
  · simp [hc]
  · simp [hc]

end
end ECDLP.L68
end
