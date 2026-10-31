import ECDLP.L77_Run
import ECDLP.L61_Challenge

/-!
# L77 / Q: the reassembly program `Qprog` (SProg), which turns the stacks left by phase 0 into Rudich's input stack `encB x`

`Qprog a1 a2 = transfer a1 → 0 ; push 0 false ; transfer a2 → 0`.  On `s0Of a1 a2 X Y` (X on `a1`, Y on `a2`, rest empty) it produces
`initStacks (Y.reverse ++ false :: X.reverse)` in `2|X| + 2|Y| + 3` steps.
-/
namespace ECDLP.L77
open Function Factoring.Aux Factoring.Aux.SProg

def transfer (k : ℕ) : SProg := .loop k (.push 0 true) (.push 0 false)

def Qprog (a1 a2 : ℕ) : SProg := .seq (transfer a1) (.seq (.push 0 false) (transfer a2))

theorem loopExec_transfer (k : ℕ) (hk : k ≠ 0) :
    ∀ (l : List Bool) (s : Stacks), s k = l →
      loopExec k (fun b => bif b then exec (.push 0 true) else exec (.push 0 false)) l s =
        update (update s k []) 0 (l.reverse ++ s 0) := by
  intro l
  induction l with
  | nil =>
      intro s hs
      have : update s k [] = s := by rw [← hs]; exact update_eq_self k s
      simp [loopExec, this, hs]
  | cons b l ih =>
      intro s hs
      have h0 : (update s k l) 0 = s 0 := update_of_ne (Ne.symm hk) _ _
      have e : (bif b then exec (.push 0 true) else exec (.push 0 false)) (update s k l) =
          update (update s k l) 0 (b :: s 0) := by
        cases b <;> simp [exec, h0]
      simp only [loopExec]
      rw [e]
      have hk' : (update (update s k l) 0 (b :: s 0)) k = l := by
        rw [update_of_ne hk, update_self]
      rw [ih _ hk']
      have h00 : (update (update s k l) 0 (b :: s 0)) 0 = b :: s 0 := update_self _ _ _
      rw [h00]
      funext j
      by_cases hj0 : j = 0
      · subst hj0; simp [hk.symm, update_self, Ne.symm hk]
      · by_cases hjk : j = k
        · subst hjk; simp [hj0]
        · simp [hj0, hjk]

theorem exec_transfer (k : ℕ) (hk : k ≠ 0) (s : Stacks) :
    exec (transfer k) s = update (update s k []) 0 ((s k).reverse ++ s 0) :=
  loopExec_transfer k hk (s k) s rfl

theorem loopCost_transfer (k : ℕ) (hk : k ≠ 0) :
    ∀ (l : List Bool) (s : Stacks), s k = l →
      loopCost k (fun b => bif b then exec (.push 0 true) else exec (.push 0 false))
        (fun b => bif b then cost (.push 0 true) else cost (.push 0 false)) l s = 2 * l.length + 1 := by
  intro l
  induction l with
  | nil => intro s hs; simp [loopCost]
  | cons b l ih =>
      intro s hs
      have h0 : (update s k l) 0 = s 0 := update_of_ne (Ne.symm hk) _ _
      have e : (bif b then exec (.push 0 true) else exec (.push 0 false)) (update s k l) =
          update (update s k l) 0 (b :: s 0) := by
        cases b <;> simp [exec, h0]
      have hk' : (update (update s k l) 0 (b :: s 0)) k = l := by
        rw [update_of_ne hk, update_self]
      simp only [loopCost]
      rw [e, ih _ hk']
      cases b <;> simp [cost] <;> omega

theorem cost_transfer (k : ℕ) (hk : k ≠ 0) (s : Stacks) : cost (transfer k) s = 2 * (s k).length + 1 :=
  loopCost_transfer k hk (s k) s rfl

def s0Of' (a1 a2 : ℕ) (X Y : List Bool) : Stacks := update (update (fun _ => []) a1 X) a2 Y

theorem exec_Q (a1 a2 : ℕ) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h12 : a1 ≠ a2) (X Y : List Bool) :
    exec (Qprog a1 a2) (s0Of' a1 a2 X Y) = initStacks (Y.reverse ++ false :: X.reverse) ∧
    cost (Qprog a1 a2) (s0Of' a1 a2 X Y) = 2 * X.length + 2 * Y.length + 3 := by
  have hX : s0Of' a1 a2 X Y a1 = X := by simp [s0Of', update_of_ne h12]
  have hY : s0Of' a1 a2 X Y a2 = Y := by simp [s0Of']
  have h00 : s0Of' a1 a2 X Y 0 = [] := by
    simp [s0Of', update_of_ne (Ne.symm h1), update_of_ne (Ne.symm h2)]
  set s1 := exec (transfer a1) (s0Of' a1 a2 X Y) with hs1
  have e1 : s1 = update (update (s0Of' a1 a2 X Y) a1 []) 0 (X.reverse) := by
    rw [hs1, exec_transfer a1 h1, hX, h00]; simp
  have s1a2 : s1 a2 = Y := by
    rw [e1, update_of_ne h2, update_of_ne (Ne.symm h12), hY]
  have s10 : s1 0 = X.reverse := by rw [e1, update_self]
  set s2 := exec (.push 0 false) s1 with hs2
  have e2 : s2 = update s1 0 (false :: X.reverse) := by simp [hs2, exec, s10]
  have s2a2 : s2 a2 = Y := by rw [e2, update_of_ne h2, s1a2]
  have s20 : s2 0 = false :: X.reverse := by rw [e2, update_self]
  constructor
  · show exec (transfer a2) (exec (.push 0 false) (exec (transfer a1) (s0Of' a1 a2 X Y))) = _
    rw [← hs1, ← hs2, exec_transfer a2 h2, s2a2, s20]
    funext j
    by_cases hj0 : j = 0
    · subst hj0; simp [initStacks]
    · by_cases hj2 : j = a2
      · subst hj2; simp [initStacks, hj0, h2]
      · by_cases hj1 : j = a1
        · subst hj1; simp [initStacks, hj0, hj2, e2, e1, s0Of']
        · simp [initStacks, hj0, hj2, hj1, e2, e1, s0Of']
  · show cost (transfer a1) (s0Of' a1 a2 X Y) + (cost (.push 0 false) (exec (transfer a1) (s0Of' a1 a2 X Y)) +
      cost (transfer a2) (exec (.push 0 false) (exec (transfer a1) (s0Of' a1 a2 X Y)))) = _
    rw [← hs1, ← hs2, cost_transfer a1 h1, cost_transfer a2 h2, hX, s2a2]
    simp [cost]
    omega

/-- monotonicity of `StacksBelow` -/
theorem stacksBelow_mono {n m : ℕ} (h : n ≤ m) : ∀ p : SProg, p.StacksBelow n = true → p.StacksBelow m = true
  | .skip, _ => rfl
  | .push k b, hp => by simp [StacksBelow] at hp ⊢; omega
  | .read k pt pf pe, hp => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := hp
      exact ⟨⟨⟨by omega, stacksBelow_mono h pt h1⟩, stacksBelow_mono h pf h2⟩, stacksBelow_mono h pe h3⟩
  | .seq p q, hp => by
      simp only [StacksBelow, Bool.and_eq_true] at hp ⊢
      exact ⟨stacksBelow_mono h p hp.1, stacksBelow_mono h q hp.2⟩
  | .loop k pt pf, hp => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
      obtain ⟨⟨hk, h1⟩, h2⟩ := hp
      exact ⟨⟨by omega, stacksBelow_mono h pt h1⟩, stacksBelow_mono h pf h2⟩

end ECDLP.L77
