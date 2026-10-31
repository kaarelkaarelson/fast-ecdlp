import ECDLP.L64_Edge
import ECDLP.L56_Edge

/-!
# L68 / Car: the CAR gate's message and local check as `Ex` expressions

The carry gate `car c j` of `edgeNet` receives the ring element `r` of `ib` (code = `ZMod.val`) and, when `j > 0`,
the previous carry (code `ci < 2^(M+3)`, `decC q = ci - 2^(M+1)`); it sends
`encC ((cin + cf) / 2^b)` and checks `2^b ∣ cin + cf` and (`j+1 = A*A → (cin+cf)/2^b = 0`), where
`cf = valMinAbs r`.  All integer arithmetic is shifted by `Z = 2^b * 2^(M+3)` into `ℕ`.
Slots: `vb` holds `2^b`, `vM` holds `2^M`, `vj` the gate index `j`, `vA2` holds `A*A`, `vc` the carry code, `vr` the
ring code.
-/
noncomputable section
namespace ECDLP.L68
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L38

/-- the shifted total `t = cin + cf + Z` as `ℕ`, from the slot values -/
def tN (pb pM j ci r : ℕ) : ℕ :=
  (if 0 < j then ci else 2 * pM) + r + (if r < (pM + 1) / 2 + 1 then pb * (8 * pM) - 2 * pM else
    pb * (8 * pM) - 2 * pM - (pM + 1))

def tE (vb vM vj vc vr : ℕ) : Ex :=
  .add (.add (.ifLt (.lit 0) (.var vj) (.var vc) (.mul (.lit 2) (.var vM))) (.var vr))
    (.ifLt (.var vr) (.add (.div (.add (.var vM) (.lit 1)) (.lit 2)) (.lit 1))
      (.sub (.mul (.var vb) (.mul (.lit 8) (.var vM))) (.mul (.lit 2) (.var vM)))
      (.sub (.sub (.mul (.var vb) (.mul (.lit 8) (.var vM))) (.mul (.lit 2) (.var vM))) (.add (.var vM) (.lit 1))))

theorem eval_tE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vb vM vj vc vr : ℕ} :
    Ex.eval σ A (tE vb vM vj vc vr) = tN (σ vb) (σ vM) (σ vj) (σ vc) (σ vr) := by
  simp only [tE, tN, Ex.eval]
  rfl

/-- the output code -/
def carOutE (vb vM vj vc vr : ℕ) : Ex :=
  .mod (.sub (.add (.div (tE vb vM vj vc vr) (.var vb)) (.mul (.lit 2) (.var vM))) (.mul (.lit 8) (.var vM)))
    (.mul (.lit 8) (.var vM))

/-- the weight -/
def carWE (vb vM vj vA2 vc vr : ℕ) : Ex :=
  .ifLt (.lit 0) (.mod (tE vb vM vj vc vr) (.var vb)) (.lit 0)
    (.ifLt (.add (.var vj) (.lit 1)) (.var vA2) (.lit 1)
      (.ifLt (.var vA2) (.add (.var vj) (.lit 1)) (.lit 1)
        (.ifLt (.div (tE vb vM vj vc vr) (.var vb)) (.mul (.lit 8) (.var vM)) (.lit 0)
          (.ifLt (.mul (.lit 8) (.var vM)) (.div (tE vb vM vj vc vr) (.var vb)) (.lit 0) (.lit 1)))))

/-! ### The arithmetic -/

section arith
variable (N : NPar)

/-- the integer `cin + cf` of the gate, from the codes -/
def sZ (j ci r : ℕ) : ℤ :=
  (if 0 < j then (ci : ℤ) - 2 ^ (N.M + 1) else 0) +
    (if r ≤ (2 ^ N.M + 1) / 2 then (r : ℤ) else (r : ℤ) - (2 ^ N.M + 1))

theorem tN_eq (j ci r : ℕ) :
    ((tN (2 ^ N.b) (2 ^ N.M) j ci r : ℕ) : ℤ) = sZ N j ci r + 2 ^ N.b * 2 ^ (N.M + 3) := by
  have hb : 1 ≤ 2 ^ N.b := Nat.one_le_two_pow
  have hM1 : 1 ≤ 2 ^ N.M := Nat.one_le_two_pow
  have hZ : 8 * 2 ^ N.M ≤ 2 ^ N.b * (8 * 2 ^ N.M) := Nat.le_mul_of_pos_left _ hb
  have e : (2 : ℤ) ^ N.b * 2 ^ (N.M + 3) = ((2 ^ N.b * (8 * 2 ^ N.M) : ℕ) : ℤ) := by push_cast; ring
  have hp1 : (2 : ℤ) ^ (N.M + 1) = ((2 * 2 ^ N.M : ℕ) : ℤ) := by push_cast; ring
  unfold tN sZ
  rw [e, hp1]
  generalize 2 ^ N.b * (8 * 2 ^ N.M) = Zv at *
  generalize 2 ^ N.M = P at *
  split_ifs <;> omega


theorem tN_div (j ci r : ℕ) :
    (((tN (2 ^ N.b) (2 ^ N.M) j ci r) / 2 ^ N.b : ℕ) : ℤ) = sZ N j ci r / 2 ^ N.b + 8 * 2 ^ N.M := by
  have h := tN_eq N j ci r
  have hb : (0 : ℤ) < 2 ^ N.b := by positivity
  have e : (2 : ℤ) ^ N.b * 2 ^ (N.M + 3) = 2 ^ N.b * (8 * 2 ^ N.M) := by ring
  rw [e] at h
  rw [Int.natCast_div, h]
  push_cast
  rw [Int.add_mul_ediv_left _ _ hb.ne']

theorem tN_dvd (j ci r : ℕ) :
    tN (2 ^ N.b) (2 ^ N.M) j ci r % 2 ^ N.b = 0 ↔ (2 ^ N.b : ℤ) ∣ sZ N j ci r := by
  have h := tN_eq N j ci r
  have e : (2 : ℤ) ^ N.b * 2 ^ (N.M + 3) = 2 ^ N.b * (8 * 2 ^ N.M) := by ring
  rw [e] at h
  rw [← Nat.dvd_iff_mod_eq_zero]
  have : ((2 ^ N.b : ℕ) : ℤ) ∣ ((tN (2 ^ N.b) (2 ^ N.M) j ci r : ℕ) : ℤ) ↔ (2 ^ N.b : ℤ) ∣ sZ N j ci r := by
    rw [h]; push_cast
    exact (dvd_add_left (dvd_mul_right _ _))
  rw [← this]
  exact Int.natCast_dvd_natCast.symm


theorem carOut_val (j ci r : ℕ) :
    (tN (2 ^ N.b) (2 ^ N.M) j ci r / 2 ^ N.b + 2 * 2 ^ N.M - 8 * 2 ^ N.M) % (8 * 2 ^ N.M) =
      (encC N (sZ N j ci r / 2 ^ N.b)).val := by
  have h := tN_div N j ci r
  unfold encC
  rw [Fin.val_ofNat]
  have hp : (2 : ℤ) ^ (N.M + 1) = 2 * 2 ^ N.M := by ring
  have hp3 : 2 ^ (N.M + 3) = 8 * 2 ^ N.M := by ring
  rw [hp, hp3]
  congr 1
  generalize tN (2 ^ N.b) (2 ^ N.M) j ci r / 2 ^ N.b = q at *
  generalize sZ N j ci r / 2 ^ N.b = s at *
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 2 ^ N.M := ⟨_, rfl⟩
  have hc : (2 : ℤ) ^ N.M = (P : ℤ) := by rw [hP]; push_cast; rfl
  rw [hc] at h ⊢
  rw [← hP]
  omega

theorem carW_iff (j ci r : ℕ) :
    ((2 ^ N.b : ℤ) ∣ sZ N j ci r ∧ (j + 1 = N.A * N.A → sZ N j ci r / 2 ^ N.b = 0)) ↔
      (tN (2 ^ N.b) (2 ^ N.M) j ci r % 2 ^ N.b = 0 ∧
        (j + 1 = N.A * N.A → tN (2 ^ N.b) (2 ^ N.M) j ci r / 2 ^ N.b = 8 * 2 ^ N.M)) := by
  rw [tN_dvd]
  have h := tN_div N j ci r
  refine and_congr Iff.rfl (imp_congr_right fun _ => ?_)
  generalize tN (2 ^ N.b) (2 ^ N.M) j ci r / 2 ^ N.b = q at *
  generalize sZ N j ci r / 2 ^ N.b = s at *
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 2 ^ N.M := ⟨_, rfl⟩
  have hc : (2 : ℤ) ^ N.M = (P : ℤ) := by rw [hP]; push_cast; rfl
  rw [hc] at h
  rw [← hP]
  omega

end arith

open Classical in
theorem eval_carOutE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vb vM vj vc vr : ℕ} (N : NPar)
    (hb : σ vb = 2 ^ N.b) (hM : σ vM = 2 ^ N.M) :
    Ex.eval σ A (carOutE vb vM vj vc vr) = (encC N (sZ N (σ vj) (σ vc) (σ vr) / 2 ^ N.b)).val := by
  rw [← carOut_val N]
  simp only [carOutE, Ex.eval, eval_tE, hb, hM]

theorem eval_carWE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vb vM vj vA2 vc vr : ℕ} (N : NPar)
    (hb : σ vb = 2 ^ N.b) (hM : σ vM = 2 ^ N.M) (hA : σ vA2 = N.A * N.A) :
    Ex.eval σ A (carWE vb vM vj vA2 vc vr) =
      if ((2 ^ N.b : ℤ) ∣ sZ N (σ vj) (σ vc) (σ vr) ∧
        (σ vj + 1 = N.A * N.A → sZ N (σ vj) (σ vc) (σ vr) / 2 ^ N.b = 0)) then 1 else 0 := by
  rw [if_congr (carW_iff N _ _ _) rfl rfl]
  simp only [carWE, Ex.eval, eval_tE, hb, hM, hA]
  generalize tN (2 ^ N.b) (2 ^ N.M) (σ vj) (σ vc) (σ vr) / 2 ^ N.b = q
  generalize tN (2 ^ N.b) (2 ^ N.M) (σ vj) (σ vc) (σ vr) % 2 ^ N.b = z
  split_ifs <;> omega

/-! ### Bridge to the real network (`edgeNet`, gate `car c j`) -/

section bridge
open ECDLP.L54 ECDLP.L56
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)

/-- code of the previous carry that the gate `car c j` reads (`0` for `j = 0`) -/
def carCi (c : Fin K) (j : Fin (N0.A * N0.A)) (z : EZ (w := w) φ (CG.gt c (Gate.car j))) : ℕ :=
  if h : 0 < j.val then
    (show Fin (2 ^ ((NP N0 w c).M + 3)) from
      z.2 ⟨CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩), mem_paC_gt φ c (Finset.mem_insert_of_mem
        (by rw [dif_pos h]; exact Finset.mem_singleton_self _))⟩).val
  else 0

/-- code of the ring element that `car c j` reads from `ib` -/
def carR (c : Fin K) (j : Fin (N0.A * N0.A)) (z : EZ (w := w) φ (CG.gt c (Gate.car j))) : ℕ :=
  (show (NP N0 w c).Rg from z.2 ⟨CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩),
    mem_paC_gt φ c (Finset.mem_insert_self _ _)⟩).val

theorem valMinAbs_val (N : NPar) (x : N.Rg) :
    x.valMinAbs = if x.val ≤ (2 ^ N.M + 1) / 2 then (x.val : ℤ) else (x.val : ℤ) - (2 ^ N.M + 1) := by
  have : NeZero (2 ^ N.M + 1) := ⟨Nat.succ_ne_zero _⟩
  have := ZMod.valMinAbs_def_pos (n := 2 ^ N.M + 1) x
  convert this using 2
  push_cast; rfl

theorem cin_add_cf (c : Fin K) (j : Fin (N0.A * N0.A)) (z : EZ (w := w) φ (CG.gt c (Gate.car j))) :
    cinE (w := w) φ c j z + cfE (w := w) φ c j z =
      sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) := by
  unfold cinE cfE sZ carCi carR
  rw [valMinAbs_val (NP N0 w c)]
  by_cases h : 0 < j.val
  · simp [h, decC]
  · simp [h]

theorem car_out_sem (F : ∀ c, Form (ιc c)) (c : Fin K) (j : Fin (N0.A * N0.A))
    (z : EZ (w := w) φ (CG.gt c (Gate.car j))) (ch : CG ι ιc N0.A) :
    (outE (w := w) φ F (CG.gt c (Gate.car j)) z ch : Fin (2 ^ ((NP N0 w c).M + 3))).val =
      (encC (NP N0 w c) (sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) /
        2 ^ (NP N0 w c).b)).val := by
  show (encC (NP N0 w c) ((cinE (w := w) φ c j z + cfE (w := w) φ c j z) / 2 ^ N0.b)).val = _
  rw [cin_add_cf]
  rfl

open Classical in
theorem car_w_sem (ok : ι → Fin N0.A → Dg N0 → Prop) (c : Fin K) (j : Fin (N0.A * N0.A))
    (z : EZ (w := w) φ (CG.gt c (Gate.car j))) :
    WE (w := w) φ ok (CG.gt c (Gate.car j)) z =
      if ((2 ^ (NP N0 w c).b : ℤ) ∣ sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) ∧
        (j.val + 1 = (NP N0 w c).A * (NP N0 w c).A →
          sZ (NP N0 w c) j.val (carCi (w := w) φ c j z) (carR (w := w) φ c j z) / 2 ^ (NP N0 w c).b = 0))
      then 1 else 0 := by
  show (if ((2 ^ N0.b : ℤ) ∣ cinE (w := w) φ c j z + cfE (w := w) φ c j z) ∧
        (j.val + 1 = N0.A * N0.A → (cinE (w := w) φ c j z + cfE (w := w) φ c j z) / 2 ^ N0.b = 0) then 1 else 0) = _
  rw [cin_add_cf]
  rfl

end bridge
end ECDLP.L68
end
