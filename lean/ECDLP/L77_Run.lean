import ECDLP.L77_Rec

/-!
# L77 / Run: the recoding machine runs `R` after phase 0

* `step_lift`, `sim_lift` : Rudich's `Simulates` for his machine `tmOf` transfers to the lifted statements (`stepAux_lift`).
* `run_all` : from the initial configuration of `tmRec R` on the input list `l0.map some ++ none :: … ++ π.map some`, the machine reaches
  the halt configuration with output `out` after `phase0 steps + cost R s0 + 1` steps, provided `R.exec s0 = initStacks out`, `s0` being the
  stacks left by phase 0.
-/
namespace ECDLP.L77
open Turing Function Factoring.Aux Factoring.Aux.SProg

section Run
variable (R : SProg) {nK : ℕ} (hK : 0 < nK) (t1 t2 : Fin nK)

theorem step_lift (c : CfgOf R nK) (l : Fin (size R + 1)) (hl : c.l = some l) :
    TM2.step (mRec R hK t1 t2) (liftCfg Sum.inl [] c) = (TM2.step (mOf R hK) c).map (liftCfg Sum.inl []) := by
  obtain ⟨cl, v, S⟩ := c
  simp only at hl
  subst hl
  simp only [TM2.step, liftCfg, Option.map_some]
  have := stepAux_lift (Sum.inl : Fin (size R + 1) → ΛR R) [] (mOf R hK l) v S
  exact congrArg some this

theorem sim_lift (hst : R.StacksBelow nK = true) :
    Simulates (flatCode R) (TM2.step (mRec R hK t1 t2))
      (fun pc s => liftCfg Sum.inl [] (enc R nK hK pc s)) := by
  have hs := simulates R nK hK hst
  constructor
  · intro pc s k b n hC
    rw [step_lift R hK t1 t2 _ (lab R pc) rfl, hs.push pc s k b n hC]
    rfl
  · intro pc s k t f e hC
    rw [step_lift R hK t1 t2 _ (lab R pc) rfl, hs.read pc s k t f e hC]
    rfl

theorem init_eq (L : List (Option Bool)) :
    initList (tmRec R hK t1 t2) L = (⟨some (Sum.inr 0), none, liftStk L (fun _ => [])⟩ : TM2.Cfg (Gm nK) (ΛR R) σR) := by
  show (⟨_, _, _⟩ : TM2.Cfg (Gm nK) (ΛR R) σR) = _
  congr 1
  funext k
  cases k with
  | none => simp [liftStk, tmRec]; rfl
  | some j => simp [liftStk, tmRec]

theorem halt_eq (out : List Bool) :
    haltList (tmRec R hK t1 t2) out = (⟨none, none, liftStk [] (fun j : Fin nK => initStacks out j.val)⟩ : TM2.Cfg (Gm nK) (ΛR R) σR) := by
  show (⟨_, _, _⟩ : TM2.Cfg (Gm nK) (ΛR R) σR) = _
  congr 1
  funext k
  cases k with
  | none => simp [liftStk, tmRec]
  | some j =>
      by_cases hj : j = ⟨0, hK⟩
      · subst hj; simp [liftStk, tmRec, initStacks]; rfl
      · have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [liftStk, tmRec, initStacks, hj, this]

/-- the stacks left by phase 0 (as `ℕ`-indexed `Stacks`) -/
def s0Of (a1 a2 : ℕ) (X Y : List Bool) : Stacks := update (update (fun _ => []) a1 X) a2 Y

theorem phase0_stacks {a1 a2 : ℕ} (h1 : a1 < nK) (h2 : a2 < nK) (X Y : List Bool) :
    update (update (fun _ : Fin nK => ([] : List Bool)) ⟨a1, h1⟩ X) ⟨a2, h2⟩ Y =
      fun j : Fin nK => s0Of a1 a2 X Y j.val := by
  have e1 := upd_fin' (nK := nK) h1 (fun _ => []) X
  have e2 := upd_fin' (nK := nK) h2 (update (fun _ => []) a1 X) Y
  rw [show (fun _ : Fin nK => ([] : List Bool)) = fun j : Fin nK => (fun _ : ℕ => ([] : List Bool)) j.val from rfl, e1, e2]
  rfl

theorem run_all (hst : R.StacksBelow nK = true) (hwf : R.WF = true) {a1 a2 : ℕ} (h1 : a1 < nK) (h2 : a2 < nK)
    (hne : a1 ≠ a2) (l0 l1 l2 l3 l4 π out : List Bool) (s0 : Stacks)
    (hs0 : s0 = s0Of a1 a2 (codeB l0 ++ codeB l1 ++ codeB l2 ++ codeB l3 ++ codeB l4).reverse
      (π.flatMap fun b => [true, b]).reverse)
    (hexec : R.exec s0 = initStacks out) :
    (flip Option.bind (tmRec R hK ⟨a1, h1⟩ ⟨a2, h2⟩).step)^[1 + R.cost s0 +
        ((1 + π.length) + (l4.length + 1) + (l3.length + 1) + (l2.length + 1) + (l1.length + 1) + (l0.length + 1))]
      (some (initList (tmRec R hK ⟨a1, h1⟩ ⟨a2, h2⟩)
        (l0.map some ++ none :: (l1.map some ++ none :: (l2.map some ++ none ::
          (l3.map some ++ none :: (l4.map some ++ none :: π.map some)))))))
    = some (haltList (tmRec R hK ⟨a1, h1⟩ ⟨a2, h2⟩) out) := by
  have hne' : (⟨a1, h1⟩ : Fin nK) ≠ ⟨a2, h2⟩ := fun h => hne (by simpa using h)
  have p0 := phase0 R hK ⟨a1, h1⟩ ⟨a2, h2⟩ hne' l0 l1 l2 l3 l4 π (fun _ => [])
  have fin : (fun j : Fin nK => (fun _ : ℕ => ([] : List Bool)) j.val) = fun _ => [] := rfl
  simp only [List.append_nil] at p0
  rw [phase0_stacks h1 h2] at p0
  rw [init_eq R hK ⟨a1, h1⟩ ⟨a2, h2⟩]
  show runR R hK ⟨a1, h1⟩ ⟨a2, h2⟩ _ _ = _
  subst hs0
  refine key R hK _ _ _ _ _ _ _ p0 ?_
  have hit := iterate_cost (sim_lift R hK ⟨a1, h1⟩ ⟨a2, h2⟩ hst) R 0 (size R) (s0Of a1 a2
    (codeB l0 ++ codeB l1 ++ codeB l2 ++ codeB l3 ++ codeB l4).reverse (π.flatMap fun b => [true, b]).reverse)
    (loaded_flat R) hwf
  rw [hexec] at hit
  have hm : mOf R hK (lab R (size R)) = .halt := by
    show instrStmt hK (lab R) (flatCode R (lab R (size R)).val) = _
    rw [lab_val (Nat.le_refl _)]; simp [flatCode, instrStmt]
  have hlast : TM2.step (mRec R hK ⟨a1, h1⟩ ⟨a2, h2⟩) (liftCfg Sum.inl [] (enc R nK hK (size R) (initStacks out))) =
      some (haltList (tmRec R hK ⟨a1, h1⟩ ⟨a2, h2⟩) out) := by
    rw [step_lift R hK _ _ _ (lab R (size R)) rfl, halt_eq]
    simp [enc, TM2.step, hm, TM2.stepAux, liftCfg]
    rfl
  refine key R hK _ _ _ _ _ _ _ hit (runR_one R hK _ _ _ _ hlast)

end Run

end ECDLP.L77
