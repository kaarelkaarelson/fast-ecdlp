import ECDLP.L73_Iface
import ECDLP.L68_CarQ

/-!
# L68 / CarPEx: the `hout` / `hwt` obligations of `PEx` for a car node (one gate kind, end to end)

`carOutL' X jE pcE pibE`: the local expression for the code of the message sent by a car node: reads the codes of
the previous carry and of the `ib` message from the setting code with `digE`, then runs `carOutE`.
The parent indices come from index oracles `jE` (the gate number `j`), `pcE` (global index of `car (j-1)`),
`pibE` (global index of `ib (j % A)`), each a function of the node slot `u+5` only.
-/
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

/-- parameter slots (inside the context, below `u`) and scratch slots -/
def carIn' (vj vc vr : ℕ) (jE pcE pibE body : Ex) : Ex :=
  .lett u (.var (u + 5)) (.lett (u + 2) (.var (u + 7))
    (.lett vj jE
      (.lett vc (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0))
        (.lett (u + 1) pibE (.lett vr (digE X u (u + 1)) body))))) 


variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

/-- the digit of the setting code at a parent, as `pm` -/
theorem eval_digE_pm' {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) {p : CG ι ιc N0.A} (hkp : e.symm k = p) (hp : p ∈ paC (w := w) φ (e.symm a))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e (hF := edge_free_nonempty φ F ok m)).e a z) :
    Ex.eval σ A (digE X fr tt) = pm (w := w) φ F ok m z p := by
  subst hkp
  have := eval_digE X hu hC hσ hfr htt ha hk (E := edgeEM (w := w) φ F ok m) (EF := edgeEFM φ F ok m)
    (hF := edge_free_nonempty φ F ok m) hp z hz
  rw [this]
  unfold ECDLP.L68.pm
  rw [dif_pos hp]
  rfl


/-- **The code of the message of a car node**, computed from the setting code. -/
theorem eval_carIn' {vj vc vr : ℕ} {body : Ex} (hj : u + 90 ≤ vj) (hc : u + 90 ≤ vc)
    (hr : u + 90 ≤ vr) (hjc : vj ≠ vc) (hjr : vj ≠ vr) (hcr : vc ≠ vr)
    {a : Fin g} {c : Fin K} {j : Fin (N0.A * N0.A)} (hka : e.symm a = CG.gt c (Gate.car j))
    {jE pcE pibE : Ex}
    (hjE : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → Ex.eval σ' A jE = j.val)
    (hpc : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → ∀ h : 0 < j.val,
      Ex.eval σ' A pcE = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)))
    (hpib : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a →
      Ex.eval σ' A pibE = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z) (ha : σ (u + 5) = a) :
    ∃ σ6 : ℕ → ℕ, Ex.eval σ A (carIn' X vj vc vr jE pcE pibE body) = Ex.eval σ6 A body ∧ σ6 vj = j.val ∧
      σ6 vc = carCiQ (w := w) φ F ok m c j z ∧ σ6 vr = carRQ (w := w) φ F ok m c j z ∧ (∀ y, y ≠ u → y ≠ u + 1 → y ≠ u + 2 → y ≠ vj → y ≠ vc → y ≠ vr → σ6 y = σ y) := by
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have a1 : σ1 (u + 5) = a := by rw [hσ1, Function.update_of_ne (by omega)]; exact ha
  have a2 : σ2 (u + 5) = a := by rw [hσ2, Function.update_of_ne (by omega)]; exact a1
  have hz2 : σ2 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]; exact hz
  have hj2 : Ex.eval σ2 A jE = j.val := hjE σ2 g2 a2
  set σ3 := Function.update σ2 vj (Ex.eval σ2 A jE) with hσ3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
  have hz3 : σ3 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ3, Function.update_of_ne (by omega)]; exact hz2
  have u3 : σ3 u = a := by
    rw [hσ3, Function.update_of_ne (by omega), hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  have hvj3 : σ3 vj = j.val := by rw [hσ3, Function.update_self, hj2]
  -- the previous carry
  have hci : Ex.eval σ3 A (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0)) =
      carCiQ (w := w) φ F ok m c j z := by
    simp only [Ex.eval, hvj3]
    unfold carCiQ
    by_cases h0 : 0 < j.val
    · simp only [h0, if_true]
      set σ' := Function.update σ3 (u + 1) (Ex.eval σ3 A pcE) with hσ'
      have g' : Ag B σ₀ σ' := g3.upd (by omega) _
      have hk : σ' (u + 1) = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) := by
        rw [hσ', Function.update_self]; exact hpc σ3 g3 a3 h0
      have := eval_digE_pm' X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
        (k := e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)))
        (p := CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩))
        (by rw [hσ', Function.update_of_ne (by omega)]; exact u3) hk (by simp)
        (by rw [hka]; exact car_prev_mem φ c j h0) z
        (by rw [hσ', Function.update_of_ne (by omega)]; exact hz3)
      exact this
    · simp [h0]
  set σ4 := Function.update σ3 vc (Ex.eval σ3 A (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0))) with hσ4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have a4 : σ4 (u + 5) = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact a3
  have hz4 : σ4 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ4, Function.update_of_ne (by omega)]; exact hz3
  have u4 : σ4 u = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact u3
  have hr4 : Ex.eval (Function.update σ4 (u + 1) (Ex.eval σ4 A pibE)) A (digE X u (u + 1)) =
      carRQ (w := w) φ F ok m c j z := by
    set σ' := Function.update σ4 (u + 1) (Ex.eval σ4 A pibE) with hσ'
    have g' : Ag B σ₀ σ' := g4.upd (by omega) _
    have hk : σ' (u + 1) = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) := by
      rw [hσ', Function.update_self]; exact hpib σ4 g4 a4
    exact eval_digE_pm' X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
      (k := e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)))
      (p := CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩))
      (by rw [hσ', Function.update_of_ne (by omega)]; exact u4) hk (by simp)
      (by rw [hka]; exact car_ib_mem φ c j) z
      (by rw [hσ', Function.update_of_ne (by omega)]; exact hz4)
  set σ5 := Function.update σ4 (u + 1) (Ex.eval σ4 A pibE) with hσ5
  set σ6 := Function.update σ5 vr (Ex.eval σ5 A (digE X u (u + 1))) with hσ6
  refine ⟨σ6, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hσ6, Function.update_of_ne hjr, hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne hjc]; exact hvj3
  · rw [hσ6, Function.update_of_ne hcr, hσ5, Function.update_of_ne (by omega), hσ4, Function.update_self, hci]
  · rw [hσ6, Function.update_self, hr4]
  · intro y h0 h1 h2 h3 h4 h5
    rw [hσ6, Function.update_of_ne h5, hσ5, Function.update_of_ne h1, hσ4,
      Function.update_of_ne h4, hσ3, Function.update_of_ne h3,
      hσ2, Function.update_of_ne h2, hσ1, Function.update_of_ne h0]

def carOutL' (vb vM vj vc vr : ℕ) (jE pcE pibE : Ex) : Ex := carIn' X vj vc vr jE pcE pibE (carOutE vb vM vj vc vr)
def carWL' (vb vM vj vA2 vc vr : ℕ) (jE pcE pibE : Ex) : Ex :=
  .lett (u + 5) (.var (u + 4)) (carIn' X vj vc vr jE pcE pibE (carWE vb vM vj vA2 vc vr))


/-- **`hout` for a car node.** -/
theorem car_hout' {vb vM vj vc vr : ℕ} (hvb : vb < u + 90) (hvb0 : u + 10 ≤ vb) (hvM : vM < u + 90) (hvM0 : u + 10 ≤ vM) (hj : u + 90 ≤ vj) (hc : u + 90 ≤ vc)
    (hr : u + 90 ≤ vr) (hjc : vj ≠ vc) (hjr : vj ≠ vr) (hcr : vc ≠ vr)
    {a b : Fin g} {c : Fin K} {j : Fin (N0.A * N0.A)} (hka : e.symm a = CG.gt c (Gate.car j))
    (hvb' : σ vb = 2 ^ (NP N0 w c).b) (hvM' : σ vM = 2 ^ (NP N0 w c).M)
    {jE pcE pibE : Ex}
    (hjE : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → Ex.eval σ' A jE = j.val)
    (hpc : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → ∀ h : 0 < j.val,
      Ex.eval σ' A pcE = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)))
    (hpib : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a →
      Ex.eval σ' A pibE = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z) (ha : σ (u + 5) = a) :
    Ex.eval σ A (carOutL' X vb vM vj vc vr jE pcE pibE) =
      ec (ι := ι) (ιc := ιc) (w := w) (e.symm a) ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b)) := by
  obtain ⟨σ6, h, h1, h2, h3, h4⟩ := eval_carIn' X hu hC hσ (body := carOutE vb vM vj vc vr) hj hc hr hjc hjr hcr hka hjE hpc hpib z hz ha
  rw [out_car_q (w := w) φ F ok m c j (e.symm a) hka z (e.symm b)]
  unfold carOutL'
  rw [h, eval_carOutE (NP N0 w c) (by rw [h4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hvb') (by rw [h4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hvM'), h1, h2, h3]

open Classical in
/-- **`hwt` for a car node** (the node index is in slot `u+4`). -/
theorem car_hwt' {vb vM vj vA2 vc vr : ℕ} (hvb : vb < u + 90) (hvb0 : u + 10 ≤ vb) (hvM : vM < u + 90) (hvM0 : u + 10 ≤ vM) (hvA : vA2 < u + 90) (hvA0 : u + 10 ≤ vA2) (hj : u + 90 ≤ vj)
    (hc : u + 90 ≤ vc) (hr : u + 90 ≤ vr) (hjc : vj ≠ vc) (hjr : vj ≠ vr) (hcr : vc ≠ vr)
    (hm1 : 1 < m) {a : Fin g} {c : Fin K} {j : Fin (N0.A * N0.A)} (hka : e.symm a = CG.gt c (Gate.car j))
    (hvb' : σ vb = 2 ^ (NP N0 w c).b) (hvM' : σ vM = 2 ^ (NP N0 w c).M) (hvA' : σ vA2 = (NP N0 w c).A * (NP N0 w c).A)
    {jE pcE pibE : Ex}
    (hjE : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → Ex.eval σ' A jE = j.val)
    (hpc : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → ∀ h : 0 < j.val,
      Ex.eval σ' A pcE = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)))
    (hpib : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a →
      Ex.eval σ' A pibE = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z) (ha : σ (u + 4) = a) :
    Ex.eval σ A (carWL' X vb vM vj vA2 vc vr jE pcE pibE) =
      if (edgeNetM (w := w) φ F ok m).W (e.symm a) z = 1 then 1 else 0 := by
  have g' : Ag B σ₀ (Function.update σ (u + 5) (σ (u + 4))) := hσ.upd (by omega) _
  have hz' : (Function.update σ (u + 5) (σ (u + 4))) (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [Function.update_of_ne (by omega)]; exact hz
  obtain ⟨σ6, h, h1, h2, h3, h4⟩ := eval_carIn' X hu hC g' (body := carWE vb vM vj vA2 vc vr) hj hc hr hjc hjr hcr hka hjE hpc hpib z hz'
    (by simp [ha])
  rw [w_car_q (w := w) φ F ok m hm1 c j (e.symm a) hka z]
  unfold carWL'
  have hh : Ex.eval σ A (Ex.lett (u + 5) (Ex.var (u + 4)) (carIn' X vj vc vr jE pcE pibE (carWE vb vM vj vA2 vc vr))) =
      Ex.eval (Function.update σ (u + 5) (σ (u + 4))) A (carIn' X vj vc vr jE pcE pibE (carWE vb vM vj vA2 vc vr)) := rfl
  rw [hh, h, eval_carWE (NP N0 w c) (by rw [h4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [Function.update_of_ne, show vb ≠ u + 5 by omega]; exact hvb')
    (by rw [h4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [Function.update_of_ne, show vM ≠ u + 5 by omega]; exact hvM')
    (by rw [h4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [Function.update_of_ne, show vA2 ≠ u + 5 by omega]; exact hvA'), h1, h2, h3]

end
end ECDLP.L73
end
