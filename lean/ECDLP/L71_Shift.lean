import Mathlib.Computability.TuringMachine.Computable
import FactoringAux.UniDrvSpec

/-!
# L71 / Shift: running a `Cmd` in a renamed frame

`Cmd.shift S c` renames every scalar `x` to `S + x` and every array `a` to `S + a` (the `call M a` array too).
`St.unshift S st` is the state seen through the renaming.  The run of `c.shift S` on `st` is the run of `c` on
`st.unshift S` (same cost), and it never writes an index `< S`.  This is the isolation primitive used to call
Rudich's *proved* commands (which are specified from `St.init`) as subroutines inside a bigger state.
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def _root_.Factoring.Aux.Copied.PLib.Cmd.shift (S : ℕ) : Cmd → Cmd
  | .skip => .skip
  | .seq s t => .seq (shift S s) (shift S t)
  | .setK x k => .setK (S + x) k
  | .copy x y => .copy (S + x) (S + y)
  | .incr x => .incr (S + x)
  | .decr x => .decr (S + x)
  | .rd x a i o => .rd (S + x) (S + a) (S + i) o
  | .wr a i o y => .wr (S + a) (S + i) o (S + y)
  | .ifLt x y s t => .ifLt (S + x) (S + y) (shift S s) (shift S t)
  | .ifZero x s t => .ifZero (S + x) (shift S s) (shift S t)
  | .loop b c body => .loop (S + b) (S + c) (shift S body)
  | .call M a => .call M (S + a)

def unshift (S : ℕ) (st : St) : St := ⟨fun i => st.sc (S + i), fun a => st.ar (S + a)⟩

@[simp] theorem unshift_sc (S : ℕ) (st : St) (i : ℕ) : (unshift S st).sc i = st.sc (S + i) := rfl
@[simp] theorem unshift_ar (S : ℕ) (st : St) (a : ℕ) : (unshift S st).ar a = st.ar (S + a) := rfl

theorem unshift_setSc (S : ℕ) (st : St) (x v : ℕ) :
    unshift S (st.setSc (S + x) v) = (unshift S st).setSc x v := by
  apply St.ext
  · funext i; simp [unshift, St.setSc, Function.update_apply]
  · rfl

theorem unshift_putAr (S : ℕ) (st : St) (a : ℕ) (f : ℕ → ℕ) :
    unshift S (st.putAr (S + a) f) = (unshift S st).putAr a f := by
  apply St.ext
  · rfl
  · funext b; simp [unshift, St.putAr, Function.update_apply]

theorem unshift_setAr (S : ℕ) (st : St) (a i v : ℕ) :
    unshift S (st.setAr (S + a) i v) = (unshift S st).setAr a i v := by
  simp only [St.setAr, unshift_putAr]
  rfl

/-- agreement below `S` -/
def LowEq (S : ℕ) (s t : St) : Prop := (∀ i, i < S → s.sc i = t.sc i) ∧ ∀ a, a < S → s.ar a = t.ar a

theorem LowEq.refl (S : ℕ) (s : St) : LowEq S s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
theorem LowEq.trans {S : ℕ} {s t u : St} (h : LowEq S s t) (h' : LowEq S t u) : LowEq S s u :=
  ⟨fun i hi => (h.1 i hi).trans (h'.1 i hi), fun a ha => (h.2 a ha).trans (h'.2 a ha)⟩

theorem lowEq_setSc (S : ℕ) (st : St) (x v : ℕ) : LowEq S st (st.setSc (S + x) v) :=
  ⟨fun i hi => by simp [St.setSc, Function.update_apply]; omega, fun _ _ => rfl⟩

theorem lowEq_putAr (S : ℕ) (st : St) (a : ℕ) (f : ℕ → ℕ) : LowEq S st (st.putAr (S + a) f) :=
  ⟨fun _ _ => rfl, fun b hb => by simp [St.putAr, Function.update_apply]; omega⟩

theorem lowEq_setAr (S : ℕ) (st : St) (a i v : ℕ) : LowEq S st (st.setAr (S + a) i v) :=
  lowEq_putAr S st a _

/-- **Shift lemma.** -/
theorem run_shift (S : ℕ) : ∀ (c : Cmd) (st : St),
    unshift S (Cmd.run (c.shift S) st).1 = (Cmd.run c (unshift S st)).1 ∧
    (Cmd.run (c.shift S) st).2 = (Cmd.run c (unshift S st)).2 ∧
    LowEq S st (Cmd.run (c.shift S) st).1
  | .skip, st => ⟨rfl, rfl, LowEq.refl _ _⟩
  | .seq s t, st => by
      obtain ⟨a1, a2, a3⟩ := run_shift S s st
      obtain ⟨b1, b2, b3⟩ := run_shift S t (Cmd.run (s.shift S) st).1
      simp only [Cmd.shift, Cmd.run_seq]
      refine ⟨?_, ?_, a3.trans b3⟩
      · rw [b1, a1]
      · rw [b2, a1, a2]
  | .setK x k, st => ⟨unshift_setSc S st x k, rfl, lowEq_setSc S st x k⟩
  | .copy x y, st => ⟨by simp [Cmd.shift, Cmd.run_copy, unshift_setSc], rfl,
      by simpa [Cmd.shift, Cmd.run_copy] using lowEq_setSc S st x _⟩
  | .incr x, st => ⟨by simp [Cmd.shift, Cmd.run_incr, unshift_setSc], rfl,
      by simpa [Cmd.shift, Cmd.run_incr] using lowEq_setSc S st x _⟩
  | .decr x, st => ⟨by simp [Cmd.shift, Cmd.run_decr, unshift_setSc], rfl,
      by simpa [Cmd.shift, Cmd.run_decr] using lowEq_setSc S st x _⟩
  | .rd x a i o, st => ⟨by simp [Cmd.shift, Cmd.run_rd, unshift_setSc], rfl,
      by simpa [Cmd.shift, Cmd.run_rd] using lowEq_setSc S st x _⟩
  | .wr a i o y, st => ⟨by simp [Cmd.shift, Cmd.run_wr, unshift_setAr], rfl,
      by simpa [Cmd.shift, Cmd.run_wr] using lowEq_setAr S st a _ _⟩
  | .ifLt x y s t, st => by
      obtain ⟨a1, a2, a3⟩ := run_shift S s st
      obtain ⟨b1, b2, b3⟩ := run_shift S t st
      by_cases h : st.sc (S + x) < st.sc (S + y)
      · simp [Cmd.shift, Cmd.run_ifLt, h, a1, a2, a3]
      · simp [Cmd.shift, Cmd.run_ifLt, h, b1, b2, b3]
  | .ifZero x s t, st => by
      obtain ⟨a1, a2, a3⟩ := run_shift S s st
      obtain ⟨b1, b2, b3⟩ := run_shift S t st
      by_cases h : st.sc (S + x) = 0
      · simp [Cmd.shift, Cmd.run_ifZero, h, a1, a2, a3]
      · simp [Cmd.shift, Cmd.run_ifZero, h, b1, b2, b3]
  | .loop b c body, st => by
      have key : ∀ j, unshift S (Cmd.loopSt (body.shift S) (S + c) j st) = Cmd.loopSt body c j (unshift S st) ∧
          Cmd.loopCost (body.shift S) (S + c) j st = Cmd.loopCost body c j (unshift S st) ∧
          LowEq S st (Cmd.loopSt (body.shift S) (S + c) j st) := by
        intro j
        induction j with
        | zero => exact ⟨rfl, rfl, LowEq.refl _ _⟩
        | succ j ih =>
            obtain ⟨i1, i2, i3⟩ := ih
            obtain ⟨r1, r2, r3⟩ := run_shift S body ((Cmd.loopSt (body.shift S) (S + c) j st).setSc (S + c) j)
            refine ⟨?_, ?_, ?_⟩
            · simp only [Cmd.loopSt]; rw [r1, unshift_setSc, i1]
            · simp only [Cmd.loopCost]; rw [r2, unshift_setSc, i1, i2]
            · simp only [Cmd.loopSt]
              exact (i3.trans (lowEq_setSc S _ c j)).trans r3
      simp only [Cmd.shift, Cmd.run_loop_eq]
      have hb : st.sc (S + b) = (unshift S st).sc b := rfl
      rw [hb]
      obtain ⟨k1, k2, k3⟩ := key ((unshift S st).sc b)
      exact ⟨k1, k2, k3⟩
  | .call M a, st => ⟨by simp [Cmd.shift, Cmd.run_call, unshift_putAr], rfl, by
      simpa [Cmd.shift, Cmd.run_call] using lowEq_putAr S st a _⟩

end ECDLP.L71
