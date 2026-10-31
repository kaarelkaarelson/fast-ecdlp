import ECDLP.L61_Main

/-!
# L61 / Zero: non-vacuity of the interface

For `m = 0` there are no decompositions (the empty sum is `0`, and `strings` demands a nonzero sum), so the zero-test
oracle is the constant command `setK 3 0`.  `ZSpec 0 c0 (fun _ => 1)` holds, and the whole pipeline
(driver, compile, simulate, TM) yields a machine for `lexLeast 0` within `C_k 2^(L/k)` for every `k`.
This is only a check that the hypotheses of `driver_subexp` are satisfiable by a genuine `Cmd` and that the
statement, the encoding and the output convention fit together; it says nothing about `m ≥ 1`.
-/
namespace ECDLP.L61
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Turing Computability

theorem strings_zero (x : Inst) : strings 0 x = ∅ := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  ext s
  simp only [strings, Set.mem_empty_iff_false, iff_false]
  split_ifs with hp
  · rintro ⟨_, P, _, _, _, _, hsum, _⟩
    simp at hsum
  · simp

def c0 : Cmd := .setK 3 0

theorem zspec_zero : ZSpec 0 c0 (fun _ => 1) := by
  refine ⟨⟨fun st i _ hi => ?_, fun st a _ => ?_⟩, fun x st τ _ _ _ _ _ => ?_⟩
  · simp [c0, Cmd.run_setK, Function.update_apply, hi]
  · simp [c0, Cmd.run_setK]
  · have : Zc 0 x τ = 0 := by simp [Zc, strings_zero]
    simp [c0, Cmd.run_setK, this]

/-- The pipeline at `m = 0`: a machine for `lexLeast 0` within `C_k 2^(L/k)`, from the generic driver. -/
theorem subexponentialRate_zero : SubexpRate 0 :=
  driver_subexp 0 c0 (fun _ => 1) zspec_zero (fun k _ => ⟨1, fun L => by simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ (L / k))⟩)

end ECDLP.L61
