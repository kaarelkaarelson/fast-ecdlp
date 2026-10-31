import ECDLP.L84_PExB0
import ECDLP.L68_CarB
import ECDLP.L73_Disp2
import ECDLP.L81_Bdd

/-!
# L95 / Car: the car-gate dispatch bounds `hcarO` (`carOutX`) and `hcarW` (`carWX`) of L89's `EdgeBdd`

Following L89's plan: `carIn'` is a chain of 6 `lett`; the two `digE` reads are bounded by `bdd_digE0` (L75) and are `< card Msg` of the parent
(`digE_lt_nm0`): `2^(M+3)` for a car parent, `2^M + 1` for the `ib` parent; then L68's `bdd_carOutE` / `bdd_carWE`.
Numeric hypotheses: `4 * (2^b * (8 * 2^M)) <= V`, `A*A <= V`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex SB ECDLP.L81 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L84

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}

theorem card_msg_car (c : Fin K) (j : Fin (N0.A * N0.A)) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.car j))) = 2 ^ ((NP N0 w c).M + 3) := by
  show Fintype.card (Fin (2 ^ ((NP N0 w c).M + 3))) = _
  exact Fintype.card_fin _

theorem card_msg_ib (c : Fin K) (j : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.ib j))) = 2 ^ (NP N0 w c).M + 1 := by
  show Fintype.card (ZMod (2 ^ (NP N0 w c).M + 1)) = _
  exact ZMod.card _

end

section carIn
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u) {V : ℕ} {σ : ℕ → ℕ}
  (H : ECDLP.L75.PExB0 X V) (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

/-- **Bdd of `carIn'`** (the let-chain of a car node): bounds the body at the final state, given the oracle expressions' values and bounds. -/
theorem bdd_carIn' {vj vc vr : ℕ} {body : Ex} (hj : u + 90 ≤ vj) (hc : u + 90 ≤ vc)
    (hr : u + 90 ≤ vr) (hjc : vj ≠ vc) (hjr : vj ≠ vr) (hcr : vc ≠ vr)
    {a : Fin g} {c : Fin K} {j : Fin (N0.A * N0.A)} (hka : e.symm a = CG.gt c (Gate.car j))
    {jE pcE pibE : Ex}
    (hjE : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → Ex.eval σ' A jE = j.val ∧ Bdd V σ' A jE)
    (hpc : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a → ∀ h : 0 < j.val,
      Ex.eval σ' A pcE = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) ∧ Bdd V σ' A pcE)
    (hpib : ∀ σ' : ℕ → ℕ, Ag B σ₀ σ' → σ' (u + 5) = a →
      Ex.eval σ' A pibE = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) ∧ Bdd V σ' A pibE)
    (hAA : N0.A * N0.A ≤ V) (cmax rmax : ℕ)
    (hcm : 2 ^ ((NP N0 w c).M + 3) ≤ cmax) (hrm : 2 ^ (NP N0 w c).M + 1 ≤ rmax)
    (ha : σ (u + 5) = a) (hz : σ (u + 7) ≤ V)
    (hbody : ∀ σ6 : ℕ → ℕ, Ag B σ₀ σ6 → σ6 vj = j.val → σ6 vc ≤ cmax → σ6 vr ≤ rmax →
      (∀ y, y ≠ u → y ≠ u + 1 → y ≠ u + 2 → y ≠ vj → y ≠ vc → y ≠ vr → σ6 y = σ y) → Bdd V σ6 A body) :
    Bdd V σ A (carIn' X vj vc vr jE pcE pibE body) := by
  have haV : σ (u + 5) ≤ V := by rw [ha]; exact le_trans a.2.le H.hgV
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have a1 : σ1 (u + 5) = a := by rw [hσ1, Function.update_of_ne (by omega)]; exact ha
  have a2 : σ2 (u + 5) = a := by rw [hσ2, Function.update_of_ne (by omega)]; exact a1
  have z1 : σ1 (u + 7) ≤ V := by rw [hσ1, Function.update_of_ne (by omega)]; exact hz
  have z2 : σ2 (u + 2) ≤ V := by rw [hσ2, Function.update_self]; exact z1
  have z2' : σ2 (u + 2) = σ (u + 7) := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]
  have h11 : σ1 u = a := by rw [hσ1, Function.update_self]; exact ha
  refine ⟨haV, ?_⟩
  refine ⟨z1, ?_⟩
  obtain ⟨hj2, bj2⟩ := hjE σ2 g2 a2
  refine ⟨bj2, ?_⟩
  set σ3 := Function.update σ2 vj (Ex.eval σ2 A jE) with hσ3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
  have z3 : σ3 (u + 2) ≤ V := by rw [hσ3, Function.update_of_ne (by omega)]; exact z2
  have u3 : σ3 u = a := by
    rw [hσ3, Function.update_of_ne (by omega), hσ2, Function.update_of_ne (by omega)]; exact h11
  have hvj3 : σ3 vj = j.val := by rw [hσ3, Function.update_self, hj2]
  -- the previous carry
  have hv : Bdd V σ3 A (Ex.var vj) := by show σ3 vj ≤ V; rw [hvj3]; have := j.2; omega
  have hci : Bdd V σ3 A (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0)) ∧
      Ex.eval σ3 A (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0)) ≤ cmax := by
    by_cases h0 : 0 < j.val
    · obtain ⟨hpcv, hpcB⟩ := hpc σ3 g3 a3 h0
      set σ' := Function.update σ3 (u + 1) (Ex.eval σ3 A pcE) with hσ'
      have g' : Ag B σ₀ σ' := g3.upd (by omega) _
      have hk : σ' (u + 1) = e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) := by
        rw [hσ', Function.update_self]; exact hpcv
      have hu' : σ' u = a := by rw [hσ', Function.update_of_ne (by omega)]; exact u3
      have hz' : σ' (u + 2) ≤ V := by rw [hσ', Function.update_of_ne (by omega)]; exact z3
      have hb := ECDLP.L75.bdd_digE0 X H hu hC g' (hF := edge_free_nonempty φ F ok m) (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
        (k := e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩))) hu' hk hz'
      have hl := ECDLP.L75.digE_lt_nm0 X H hu hC g' (hF := edge_free_nonempty φ F ok m) (fr := u) (tt := u + 1) (k := e (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩))) hk
      rw [Equiv.symm_apply_apply, card_msg_car] at hl
      refine ⟨⟨bdd_lit (Nat.zero_le V), hv, ?_⟩, ?_⟩
      · simp only [Ex.eval, hvj3, h0, if_true]
        exact ⟨hpcB, hb⟩
      · simp only [Ex.eval, hvj3, h0, if_true]
        show Ex.eval σ' A (digE X u (u + 1)) ≤ cmax
        omega
    · refine ⟨⟨bdd_lit (Nat.zero_le V), hv, ?_⟩, ?_⟩
      · simp only [Ex.eval, hvj3, h0, if_false]; exact bdd_lit (Nat.zero_le V)
      · simp only [Ex.eval, hvj3, h0, if_false]; exact Nat.zero_le _
  obtain ⟨hciB, hciV⟩ := hci
  refine ⟨hciB, ?_⟩
  set σ4 := Function.update σ3 vc (Ex.eval σ3 A (.ifLt (.lit 0) (.var vj) (.lett (u + 1) pcE (digE X u (u + 1))) (.lit 0))) with hσ4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have a4 : σ4 (u + 5) = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact a3
  have z4 : σ4 (u + 2) ≤ V := by rw [hσ4, Function.update_of_ne (by omega)]; exact z3
  have u4 : σ4 u = a := by rw [hσ4, Function.update_of_ne (by omega)]; exact u3
  have c4 : σ4 vc ≤ cmax := by rw [hσ4, Function.update_self]; exact hciV
  obtain ⟨hpibv, hpibB⟩ := hpib σ4 g4 a4
  refine ⟨hpibB, ?_⟩
  set σ5 := Function.update σ4 (u + 1) (Ex.eval σ4 A pibE) with hσ5
  have g5 : Ag B σ₀ σ5 := g4.upd (by omega) _
  have hk5 : σ5 (u + 1) = e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) := by
    rw [hσ5, Function.update_self]; exact hpibv
  have hu5 : σ5 u = a := by rw [hσ5, Function.update_of_ne (by omega)]; exact u4
  have hz5 : σ5 (u + 2) ≤ V := by rw [hσ5, Function.update_of_ne (by omega)]; exact z4
  have hb5 := ECDLP.L75.bdd_digE0 X H hu hC g5 (hF := edge_free_nonempty φ F ok m) (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
    (k := e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩))) hu5 hk5 hz5
  have hl5 := ECDLP.L75.digE_lt_nm0 X H hu hC g5 (hF := edge_free_nonempty φ F ok m) (fr := u) (tt := u + 1)
    (k := e (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩))) hk5
  rw [Equiv.symm_apply_apply, card_msg_ib] at hl5
  refine ⟨hb5, ?_⟩
  set σ6 := Function.update σ5 vr (Ex.eval σ5 A (digE X u (u + 1))) with hσ6
  have g6 : Ag B σ₀ σ6 := g5.upd (by omega) _
  refine hbody σ6 g6 ?_ ?_ ?_ ?_
  · rw [hσ6, Function.update_of_ne hjr, hσ5, Function.update_of_ne (by omega), hσ4, Function.update_of_ne hjc]; exact hvj3
  · rw [hσ6, Function.update_of_ne hcr, hσ5, Function.update_of_ne (by omega)]; exact c4
  · rw [hσ6, Function.update_self]; omega
  · intro y h0 h1 h2 h3 h4 h5
    rw [hσ6, Function.update_of_ne h5, hσ5, Function.update_of_ne h1, hσ4,
      Function.update_of_ne h4, hσ3, Function.update_of_ne h3,
      hσ2, Function.update_of_ne h2, hσ1, Function.update_of_ne h0]

end carIn

section carX
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u) {V : ℕ}
  (hu : B ≤ u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V) (H : ECDLP.L75.PExB0 X V) (hAA : N0.A * N0.A ≤ V)

include hu IB DN h8 hAA in
/-- Bdd of the oracle `carJ`: it equals `j < A*A <= V` -/
theorem bdd_carJ {σ₀ σ : ℕ → ℕ} (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (ha : σ (u + 5) = a) :
    Ex.eval σ A (carJ I) = j.val ∧ Bdd V σ A (carJ I) := by
  refine ⟨eval_carJ I hu hC hσ hka ha, ?_⟩
  unfold carJ
  refine bdd_decodeE I IB DN h8 hu hC hσ (xs := u + 5) (by omega) (CG.gt c (Gate.car j))
    (by rw [ha, ← hka]; simp) (by rw [ha]; exact le_trans a.2.le DN.hG) (fun σ' hD => ?_)
  obtain ⟨g', agr, k21, j16, s17, hp, hg⟩ := hD
  show σ' (u + 16) ≤ V
  rw [j16]
  simp only [coordOf]
  have := j.2
  omega

include hu IB DN h8 hAA in
/-- Bdd of the oracle `carPIB`: it equals the global index of an `ib` gate, `< gTot <= V` -/
theorem bdd_carPIB {σ₀ σ : ℕ → ℕ} (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (ha : σ (u + 5) = a) :
    Ex.eval σ A (carPIB I) = (L.enum N0.A (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) : ℕ) ∧
      Bdd V σ A (carPIB I) := by
  refine ⟨eval_carPIB I hu hC hσ hka ha, ?_⟩
  unfold carPIB
  refine bdd_decodeE I IB DN h8 hu hC hσ (xs := u + 5) (by omega) (CG.gt c (Gate.car j))
    (by rw [ha, ← hka]; simp) (by rw [ha]; exact le_trans a.2.le DN.hG) (fun σ' hD => ?_)
  obtain ⟨g', agr, k21, j16, s17, hp, hg⟩ := hD
  obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
  have hlt := (L.enum N0.A (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩))).2
  have hG := DN.hG
  have hmod : j.val % N0.A ≤ N0.A := (Nat.mod_lt _ N0.toPar.A_pos).le
  rw [Lay.enum_gt, Lay.gateE_ib] at hlt
  have hmul : σ' (u + 19) * σ' (u + 12) = L.nc c * N0.A := by rw [p19, p12]
  simp only [Bdd, Ex.eval, j16, coordOf, p18, p19, p12] at hmul ⊢
  simp only [Fin.val_mk] at hlt
  have hjV : j.val ≤ V := by have := j.2; omega
  have hAV : N0.A ≤ V := le_trans (Nat.le_mul_self _) hAA
  have hncle : L.nc c ≤ L.nc c * N0.A := Nat.le_mul_of_pos_right _ N0.toPar.A_pos
  generalize L.nι * N0.A = t1 at *
  generalize L.nc c * N0.A = t2 at *
  generalize j.val % N0.A = r at *
  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, ⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

include hu IB DN h8 hAA in
/-- Bdd of the oracle `carPC` -/
theorem bdd_carPC {σ₀ σ : ℕ → ℕ} {a : Fin (L.gTot N0.A)} (hσ : Ag B σ₀ σ) (ha : σ (u + 5) = a) :
    Bdd V σ A (carPC (u := u)) := by
  refine ⟨show σ (u + 5) ≤ V by rw [ha]; exact le_trans a.2.le DN.hG, show 1 ≤ V by omega⟩

include hu IB DN h8 H hAA in
/-- **`hcarO` of L89's `EdgeBdd`**: the message code of a car node is bounded by `V` -/
theorem hcarO_of (hZ : ∀ c : Fin K, 4 * (2 ^ (NP N0 w c).b * (8 * 2 ^ (NP N0 w c).M)) ≤ V) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 5) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 7) ≤ V → Bdd V σ A (carOutX I X) := by
  intro σ₀ hC σ hσ a c j hka ha h10 h11 h7
  unfold carOutX carOutL'
  refine bdd_carIn' X H hu hC hσ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hka
    (jE := carJ I) (pcE := carPC (u := u)) (pibE := carPIB I)
    (fun σ' g' a' => bdd_carJ I hu IB DN h8 hAA hC g' hka a')
    (fun σ' g' a' h0 => ⟨eval_carPC hu hC g' hka a' h0, bdd_carPC I hu IB DN h8 hAA g' a'⟩)
    (fun σ' g' a' => bdd_carPIB I hu IB DN h8 hAA hC g' hka a')
    hAA (8 * 2 ^ (NP N0 w c).M) (2 ^ (NP N0 w c).M + 1) (le_of_eq (by ring)) le_rfl ha h7 ?_
  intro σ6 g6 hvj hvc hvr frame
  have hb : σ6 (u + 10) = 2 ^ (NP N0 w c).b := by rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h10
  have hM : σ6 (u + 11) = 2 ^ (NP N0 w c).M := by rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h11
  exact ECDLP.L68.bdd_carOutE hb hM Nat.one_le_two_pow Nat.one_le_two_pow hvc hvr (hZ c) (by rw [hvj]; have := j.2; omega)

include hu IB DN h8 H hAA in
/-- **`hcarW` of L89's `EdgeBdd`**: the weight of a car node is bounded by `V` -/
theorem hcarW_of (hZ : ∀ c : Fin K, 4 * (2 ^ (NP N0 w c).b * (8 * 2 ^ (NP N0 w c).M)) ≤ V) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 4) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 28) = N0.A * N0.A → σ (u + 7) ≤ V →
      Bdd V σ A (carWX I X) := by
  intro σ₀ hC σ hσ a c j hka ha h10 h11 h28 h7
  unfold carWX carWL'
  have haV : σ (u + 4) ≤ V := by rw [ha]; exact le_trans a.2.le DN.hG
  refine ⟨haV, ?_⟩
  set σ' := Function.update σ (u + 5) (Ex.eval σ A (.var (u + 4))) with hσ'
  have g' : Ag B σ₀ σ' := hσ.upd (by omega) _
  have a' : σ' (u + 5) = a := by rw [hσ', Function.update_self]; exact ha
  have e' : ∀ y, y ≠ u + 5 → σ' y = σ y := fun y hy => by rw [hσ', Function.update_of_ne hy]
  refine bdd_carIn' X H hu hC g' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hka
    (jE := carJ I) (pcE := carPC (u := u)) (pibE := carPIB I)
    (fun σ'' g'' a'' => bdd_carJ I hu IB DN h8 hAA hC g'' hka a'')
    (fun σ'' g'' a'' h0 => ⟨eval_carPC hu hC g'' hka a'' h0, bdd_carPC I hu IB DN h8 hAA g'' a''⟩)
    (fun σ'' g'' a'' => bdd_carPIB I hu IB DN h8 hAA hC g'' hka a'')
    hAA (8 * 2 ^ (NP N0 w c).M) (2 ^ (NP N0 w c).M + 1) (le_of_eq (by ring)) le_rfl a' (by rw [e' _ (by omega)]; exact h7) ?_
  intro σ6 g6 hvj hvc hvr frame
  have hb : σ6 (u + 10) = 2 ^ (NP N0 w c).b := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e' _ (by omega)]; exact h10
  have hM : σ6 (u + 11) = 2 ^ (NP N0 w c).M := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e' _ (by omega)]; exact h11
  have hA2 : σ6 (u + 28) ≤ V := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e' _ (by omega), h28]; exact hAA
  exact ECDLP.L68.bdd_carWE hb hM Nat.one_le_two_pow Nat.one_le_two_pow hvc hvr (hZ c) (by rw [hvj]; have := j.2; omega) hA2

end carX

end ECDLP.L95
end
