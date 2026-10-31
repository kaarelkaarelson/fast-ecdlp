import Mathlib.Computability.TuringMachine.Computable

/-!
# L77 / Lift: lifting a `Bool`-stack TM2 statement to a machine with one extra stack over `Option Bool`

`Gm n : Option (Fin n) → Type` is the stack alphabet family: `Option Bool` on the new stack `none`, `Bool` on the old stacks `some j`.
`liftStmt` embeds a statement of a machine with stacks `Fin n` (all `Bool`) and local state `Option Bool` into one with stacks
`Option (Fin n)` and local state `Option (Option Bool)`.  `stepAux_lift`: the lifted statement does what the old one did, on the lifted
configuration (the new stack is not touched).
-/
namespace ECDLP.L77
open Turing Function

/-- stack alphabets: `Option Bool` on the new stack `none`, `Bool` on the old stacks -/
@[reducible] def Gm (n : ℕ) : Option (Fin n) → Type
  | none => Option Bool
  | some _ => Bool

/-- the stacks: new stack content `e`, old stacks `S` -/
def liftStk {n : ℕ} (e : List (Option Bool)) (S : Fin n → List Bool) : ∀ k : Option (Fin n), List (Gm n k)
  | none => e
  | some j => S j

/-- embedding of the old local state -/
def ι : Option Bool → Option (Option Bool) := Option.map some

/-- projection of the local state -/
def πσ : Option (Option Bool) → Option Bool := Option.join

@[simp] theorem πσ_ι (v : Option Bool) : πσ (ι v) = v := by cases v <;> rfl

theorem update_liftStk {n : ℕ} (e : List (Option Bool)) (S : Fin n → List Bool) (k : Fin n) (w : List Bool) :
    update (liftStk e S) (some k) (w : List (Gm n (some k))) = liftStk e (update S k w) := by
  funext k'
  cases k' with
  | none =>
      unfold update
      rw [dif_neg (by simp)]
      try rfl
  | some j =>
      by_cases h : j = k
      · subst h
        unfold update
        rw [dif_pos rfl]
        simp [liftStk]
        try rfl
      · unfold update
        rw [dif_neg (by simpa using h)]
        simp [liftStk, h]
        try rfl

/-- lift a statement -/
def liftStmt {n : ℕ} {Λ Λ' : Type} (lb : Λ → Λ') :
    TM2.Stmt (fun _ : Fin n => Bool) Λ (Option Bool) → TM2.Stmt (Gm n) Λ' (Option (Option Bool))
  | .push k f q => .push (some k) (fun v => f (πσ v)) (liftStmt lb q)
  | .peek k f q => .peek (some k) (fun v x => ι (f (πσ v) x)) (liftStmt lb q)
  | .pop k f q => .pop (some k) (fun v x => ι (f (πσ v) x)) (liftStmt lb q)
  | .load a q => .load (fun v => ι (a (πσ v))) (liftStmt lb q)
  | .branch p q₁ q₂ => .branch (fun v => p (πσ v)) (liftStmt lb q₁) (liftStmt lb q₂)
  | .goto g => .goto (fun v => lb (g (πσ v)))
  | .halt => .halt

/-- lift a configuration (new stack content `e`) -/
def liftCfg {n : ℕ} {Λ Λ' : Type} (lb : Λ → Λ') (e : List (Option Bool))
    (c : TM2.Cfg (fun _ : Fin n => Bool) Λ (Option Bool)) : TM2.Cfg (Gm n) Λ' (Option (Option Bool)) :=
  ⟨c.l.map lb, ι c.var, liftStk e c.stk⟩

theorem stepAux_lift {n : ℕ} {Λ Λ' : Type} (lb : Λ → Λ') (e : List (Option Bool)) :
    ∀ (q : TM2.Stmt (fun _ : Fin n => Bool) Λ (Option Bool)) (v : Option Bool) (S : Fin n → List Bool),
      TM2.stepAux (liftStmt lb q) (ι v) (liftStk e S) = liftCfg lb e (TM2.stepAux q v S)
  | .push k f q, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι]
      have := stepAux_lift lb e q v (update S k (f v :: S k))
      rw [← this, ← update_liftStk e S k (f v :: S k)]
      rfl
  | .peek k f q, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι]
      have := stepAux_lift lb e q (f v (S k).head?) S
      rw [← this]
      rfl
  | .pop k f q, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι]
      have := stepAux_lift lb e q (f v (S k).head?) (update S k (S k).tail)
      rw [← this, ← update_liftStk e S k (S k).tail]
      rfl
  | .load a q, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι]
      exact stepAux_lift lb e q (a v) S
  | .branch p q₁ q₂, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι]
      cases p v
      · exact stepAux_lift lb e q₂ v S
      · exact stepAux_lift lb e q₁ v S
  | .goto g, v, S => by
      simp only [liftStmt, TM2.stepAux, πσ_ι, liftCfg]
      rfl
  | .halt, v, S => by
      simp only [liftStmt, TM2.stepAux, liftCfg]
      rfl

end ECDLP.L77
