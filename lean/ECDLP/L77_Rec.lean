import ECDLP.L77_Lift
import FactoringAux.SProg.Machine

/-!
# L77 / Rec: the machine `tmRec R nK` that reads an `Option Bool` input, recodes it, and then runs the `Bool`-stack program `R`

Stacks `Option (Fin nK)`: the new stack `none` (alphabet `Option Bool`) carries the input; the stacks `some j` are Rudich's.
Phase 0 (labels `inr c`, `c : Fin 6` = number of `none` separators read so far) pops the input, writing the self-delimiting code
(`some b ↦ true, b`; `none ↦ false`) REVERSED onto the stack `t1` (while `c < 5`, the five numbers) or `t2` (the prefix).
It then jumps to the entry of `R`, i.e. into the lifted copy of Rudich's machine (`liftStmt`).
-/
namespace ECDLP.L77
open Turing Function Factoring.Aux Factoring.Aux.SProg

abbrev ΛR (R : SProg) : Type := Fin (size R + 1) ⊕ Fin 6

/-- local state, config type -/
abbrev σR : Type := Option (Option Bool)

/-- statement of phase 0 at count `c` -/
def p0Stmt (R : SProg) (nK : ℕ) (t1 tg : Fin nK) (c : Fin 6) : TM2.Stmt (Gm nK) (ΛR R) σR :=
  let tgt : ΛR R := Sum.inl (lab R (entry R 0 (size R)))
  .pop none (fun _ x => x)
   (.branch (fun v => v == some (some true))
      (.push (some tg) (fun _ => true) (.push (some tg) (fun _ => true) (.load (fun _ => none) (.goto fun _ => Sum.inr c))))
   (.branch (fun v => v == some (some false))
      (.push (some tg) (fun _ => true) (.push (some tg) (fun _ => false) (.load (fun _ => none) (.goto fun _ => Sum.inr c))))
   (.branch (fun v => v == some none)
      (if h : c.val < 5 then
        .push (some t1) (fun _ => false) (.load (fun _ => none) (.goto fun _ => Sum.inr ⟨c.val + 1, by omega⟩))
       else .load (fun _ => none) (.goto fun _ => tgt))
      (.load (fun _ => none) (.goto fun _ => tgt)))))

def mRec (R : SProg) {nK : ℕ} (hK : 0 < nK) (t1 t2 : Fin nK) : ΛR R → TM2.Stmt (Gm nK) (ΛR R) σR
  | .inl l => liftStmt Sum.inl (mOf R hK l)
  | .inr c => p0Stmt R nK t1 (if c.val < 5 then t1 else t2) c

instance (n : ℕ) : Fintype (Gm n none) := inferInstanceAs (Fintype (Option Bool))

/-- The machine. -/
def tmRec (R : SProg) {nK : ℕ} (hK : 0 < nK) (t1 t2 : Fin nK) : FinTM2 where
  K := Option (Fin nK)
  k₀ := none
  k₁ := some ⟨0, hK⟩
  Γ := Gm nK
  Λ := ΛR R
  main := Sum.inr 0
  σ := σR
  initialState := none
  m := mRec R hK t1 t2
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))

theorem update_liftStk_none {n : ℕ} (e e' : List (Option Bool)) (S : Fin n → List Bool) :
    update (liftStk e S) none (e' : List (Gm n none)) = liftStk e' S := by
  funext k'
  cases k' with
  | none => simp [update, liftStk]; try rfl
  | some j => unfold update; rw [dif_neg (by simp)]; rfl

theorem upd_fin' {nK a : ℕ} (ha : a < nK) (s : Stacks) (v : List Bool) :
    update (fun j : Fin nK => s j.val) ⟨a, ha⟩ v = fun j : Fin nK => update s a v j.val := by
  funext j
  by_cases hj : j.val = a
  · have : j = ⟨a, ha⟩ := Fin.ext hj
    subst this
    simp
  · have : j ≠ ⟨a, ha⟩ := fun h => hj (by rw [h])
    rw [update_of_ne this, update_of_ne hj]

/-- configuration of the machine at a label, with input-stack content `e` and the `Bool` stacks `s` -/
def cfgR (R : SProg) (nK : ℕ) (lbl : ΛR R) (e : List (Option Bool)) (s : Stacks) : TM2.Cfg (Gm nK) (ΛR R) σR :=
  ⟨some lbl, none, liftStk e (fun j : Fin nK => s j.val)⟩

@[simp] theorem liftStk_none {n : ℕ} (e : List (Option Bool)) (S : Fin n → List Bool) : liftStk e S none = e := rfl
@[simp] theorem liftStk_some {n : ℕ} (e : List (Option Bool)) (S : Fin n → List Bool) (j : Fin n) :
    liftStk e S (some j) = S j := rfl

section P0
variable (R : SProg) {nK : ℕ} (t1 tg : Fin nK) (c : Fin 6)

theorem p0_sym (b : Bool) (rest : List (Option Bool)) (S : Fin nK → List Bool) :
    TM2.stepAux (p0Stmt R nK t1 tg c) none (liftStk (some b :: rest) S) =
      ⟨some (Sum.inr c), none, liftStk rest (update S tg (b :: true :: S tg))⟩ := by
  cases b <;> simp [TM2.stepAux, p0Stmt] <;> rw [update_liftStk_none, update_liftStk]

theorem p0_sep (hc : c.val < 5) (rest : List (Option Bool)) (S : Fin nK → List Bool) :
    TM2.stepAux (p0Stmt R nK t1 tg c) none (liftStk (none :: rest) S) =
      ⟨some (Sum.inr ⟨c.val + 1, by omega⟩), none, liftStk rest (update S t1 (false :: S t1))⟩ := by
  simp [TM2.stepAux, p0Stmt, hc]
  rw [update_liftStk_none, update_liftStk]

theorem p0_end (S : Fin nK → List Bool) :
    TM2.stepAux (p0Stmt R nK t1 tg c) none (liftStk [] S) =
      ⟨some (Sum.inl (lab R (entry R 0 (size R)))), none, liftStk [] S⟩ := by
  simp [TM2.stepAux, p0Stmt]
  try rw [update_liftStk_none]

end P0

section Seq
variable (R : SProg) {nK : ℕ} (hK : 0 < nK) (t1 t2 : Fin nK)

/-- iterate the machine `k` steps -/
def runR (k : ℕ) (c : TM2.Cfg (Gm nK) (ΛR R) σR) : Option (TM2.Cfg (Gm nK) (ΛR R) σR) :=
  (flip Option.bind (TM2.step (mRec R hK t1 t2)))^[k] (some c)

theorem runR_add (j k : ℕ) (c : TM2.Cfg (Gm nK) (ΛR R) σR) (c' : TM2.Cfg (Gm nK) (ΛR R) σR)
    (h : runR R hK t1 t2 j c = some c') : runR R hK t1 t2 (k + j) c = runR R hK t1 t2 k c' := by
  unfold runR at *
  rw [Function.iterate_add_apply, h]

theorem runR_one (c c' : TM2.Cfg (Gm nK) (ΛR R) σR) (h : TM2.step (mRec R hK t1 t2) c = some c') :
    runR R hK t1 t2 1 c = some c' := by
  simp only [runR, Function.iterate_one, flip, Option.bind_some]
  exact h

theorem step_sym (c : Fin 6) (b : Bool) (rest : List (Option Bool)) (S : Fin nK → List Bool) :
    TM2.step (mRec R hK t1 t2) ⟨some (Sum.inr c), none, liftStk (some b :: rest) S⟩ =
      some ⟨some (Sum.inr c), none, liftStk rest
        (update S (if c.val < 5 then t1 else t2) (b :: true :: S (if c.val < 5 then t1 else t2)))⟩ := by
  simp only [TM2.step]
  exact congrArg some (p0_sym R t1 _ c b rest S)

theorem step_sep (c : Fin 6) (hc : c.val < 5) (rest : List (Option Bool)) (S : Fin nK → List Bool) :
    TM2.step (mRec R hK t1 t2) ⟨some (Sum.inr c), none, liftStk (none :: rest) S⟩ =
      some ⟨some (Sum.inr ⟨c.val + 1, by omega⟩), none, liftStk rest (update S t1 (false :: S t1))⟩ := by
  simp only [TM2.step]
  exact congrArg some (p0_sep R t1 _ c hc rest S)

theorem step_end (c : Fin 6) (S : Fin nK → List Bool) :
    TM2.step (mRec R hK t1 t2) ⟨some (Sum.inr c), none, liftStk [] S⟩ =
      some ⟨some (Sum.inl (lab R (entry R 0 (size R)))), none, liftStk [] S⟩ := by
  simp only [TM2.step]
  exact congrArg some (p0_end R t1 _ c S)

/-- the code of a bit string, as in `block`: `b ↦ true, b`, then the terminator `false` -/
def codeB (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

/-- one number: `ℓ.map some ++ [none]` is consumed in `|ℓ| + 1` steps, its reversed code lands on `t1` -/
theorem seg_num (c : Fin 6) (hc : c.val < 5) (ℓ : List Bool) (rest : List (Option Bool)) :
    ∀ (S : Fin nK → List Bool),
    runR R hK t1 t2 (ℓ.length + 1) ⟨some (Sum.inr c), none, liftStk (ℓ.map some ++ none :: rest) S⟩ =
      some ⟨some (Sum.inr ⟨c.val + 1, by omega⟩), none,
        liftStk rest (update S t1 ((codeB ℓ).reverse ++ S t1))⟩ := by
  induction ℓ with
  | nil =>
      intro S
      have := runR_one R hK t1 t2 _ _ (step_sep R hK t1 t2 c hc rest S)
      simpa [codeB] using this
  | cons b ℓ ih =>
      intro S
      have e : (b :: ℓ).map some ++ none :: rest = some b :: (ℓ.map some ++ none :: rest) := by simp
      have h1 : runR R hK t1 t2 1 ⟨some (Sum.inr c), none, liftStk ((b :: ℓ).map some ++ none :: rest) S⟩ =
          some ⟨some (Sum.inr c), none, liftStk (ℓ.map some ++ none :: rest) (update S t1 (b :: true :: S t1))⟩ :=
        runR_one R hK t1 t2 _ _ (by
          rw [e]
          have := step_sym R hK t1 t2 c b (ℓ.map some ++ none :: rest) S
          simpa only [hc, ite_true] using this)
      have h2 := runR_add R hK t1 t2 1 (ℓ.length + 1) _ _ h1
      rw [show (b :: ℓ).length + 1 = (ℓ.length + 1) + 1 by simp, h2, ih]
      congr 3
      simp [codeB, update_idem]

theorem seg_pi (ℓ : List Bool) :
    ∀ (S : Fin nK → List Bool),
    runR R hK t1 t2 ℓ.length ⟨some (Sum.inr 5), none, liftStk (ℓ.map some) S⟩ =
      some ⟨some (Sum.inr 5), none,
        liftStk [] (update S t2 ((ℓ.flatMap fun b => [true, b]).reverse ++ S t2))⟩ := by
  induction ℓ with
  | nil =>
      intro S
      simp [runR]
  | cons b ℓ ih =>
      intro S
      have h1 : runR R hK t1 t2 1 ⟨some (Sum.inr 5), none, liftStk ((b :: ℓ).map some) S⟩ =
          some ⟨some (Sum.inr 5), none, liftStk (ℓ.map some) (update S t2 (b :: true :: S t2))⟩ :=
        runR_one R hK t1 t2 _ _ (by
          have := step_sym R hK t1 t2 5 b (ℓ.map some) S
          simpa using this)
      have h2 := runR_add R hK t1 t2 1 ℓ.length _ _ h1
      rw [show (b :: ℓ).length = ℓ.length + 1 by simp, h2, ih]
      congr 3
      simp [update_idem]

theorem push1 (S : Fin nK → List Bool) (t : Fin nK) (a b : List Bool) :
    update (update S t (a ++ S t)) t (b ++ (update S t (a ++ S t)) t) = update S t ((b ++ a) ++ S t) := by
  simp [update_idem, List.append_assoc]

theorem key (n1 n2 : ℕ) (c c' d : TM2.Cfg (Gm nK) (ΛR R) σR) (h1 : runR R hK t1 t2 n1 c = some c')
    (h2 : runR R hK t1 t2 n2 c' = d) : runR R hK t1 t2 (n2 + n1) c = d := by
  rw [runR_add R hK t1 t2 n1 n2 c c' h1]; exact h2

theorem phase0 (hne : t1 ≠ t2) (l0 l1 l2 l3 l4 π : List Bool) (S : Fin nK → List Bool) :
    runR R hK t1 t2 ((1 + π.length) + (l4.length + 1) + (l3.length + 1) + (l2.length + 1) + (l1.length + 1) +
        (l0.length + 1))
      ⟨some (Sum.inr 0), none, liftStk (l0.map some ++ none :: (l1.map some ++ none :: (l2.map some ++ none ::
        (l3.map some ++ none :: (l4.map some ++ none :: π.map some))))) S⟩ =
    some ⟨some (Sum.inl (lab R (entry R 0 (size R)))), none,
      liftStk [] (update (update S t1 ((codeB l0 ++ codeB l1 ++ codeB l2 ++ codeB l3 ++ codeB l4).reverse ++ S t1)) t2
        ((π.flatMap fun b => [true, b]).reverse ++ S t2))⟩ := by
  have a0 := seg_num R hK t1 t2 0 (by decide) l0 (l1.map some ++ none :: (l2.map some ++ none ::
        (l3.map some ++ none :: (l4.map some ++ none :: π.map some)))) S
  have a1 := seg_num R hK t1 t2 1 (by decide) l1 (l2.map some ++ none ::
        (l3.map some ++ none :: (l4.map some ++ none :: π.map some))) (update S t1 ((codeB l0).reverse ++ S t1))
  rw [push1] at a1
  have a2 := seg_num R hK t1 t2 2 (by decide) l2 (l3.map some ++ none :: (l4.map some ++ none :: π.map some))
    (update S t1 (((codeB l1).reverse ++ (codeB l0).reverse) ++ S t1))
  rw [push1] at a2
  have a3 := seg_num R hK t1 t2 3 (by decide) l3 (l4.map some ++ none :: π.map some)
    (update S t1 (((codeB l2).reverse ++ ((codeB l1).reverse ++ (codeB l0).reverse)) ++ S t1))
  rw [push1] at a3
  have a4 := seg_num R hK t1 t2 4 (by decide) l4 (π.map some)
    (update S t1 (((codeB l3).reverse ++ ((codeB l2).reverse ++ ((codeB l1).reverse ++ (codeB l0).reverse))) ++ S t1))
  rw [push1] at a4
  set S5 := update S t1 (((codeB l4).reverse ++ ((codeB l3).reverse ++ ((codeB l2).reverse ++
    ((codeB l1).reverse ++ (codeB l0).reverse)))) ++ S t1) with hS5
  have a5 := seg_pi R hK t1 t2 π S5
  have hS5t2 : S5 t2 = S t2 := by rw [hS5, update_of_ne (Ne.symm hne)]
  have a6 := runR_one R hK t1 t2 _ _ (step_end R hK t1 t2 5 (update S5 t2 ((π.flatMap fun b => [true, b]).reverse ++ S5 t2)))
  have e : (codeB l0 ++ codeB l1 ++ codeB l2 ++ codeB l3 ++ codeB l4).reverse =
      (codeB l4).reverse ++ ((codeB l3).reverse ++ ((codeB l2).reverse ++
        ((codeB l1).reverse ++ (codeB l0).reverse))) := by
    simp [List.reverse_append, List.append_assoc]
  rw [e, ← hS5]
  rw [← hS5t2]
  exact key R hK t1 t2 _ _ _ _ _ a0 (key R hK t1 t2 _ _ _ _ _ a1 (key R hK t1 t2 _ _ _ _ _ a2
    (key R hK t1 t2 _ _ _ _ _ a3 (key R hK t1 t2 _ _ _ _ _ a4 (key R hK t1 t2 _ _ _ _ _ a5 a6)))))

end Seq

end ECDLP.L77
