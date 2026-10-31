import ECDLP.L71_Shift
import FactoringAux.UniMain

/-!
# L71 / MinFac: Rudich's proved `minFac` command as a subroutine in a shifted frame

* `uni_cspec` : `CSpec (uniC UP) B` for a `B` with `B n ≤ C_k 2^(n/k)` for every `k` (Rudich's `subexp_of_poly`, first half).
* `drvC_sub` : `srcCost (drvC UP) xs ≤ C_k 2^(|xs|/k)` for every `k ≥ 1` (all `xs`).
* `minFacCmd S := (drvC UP).shift S`.  On a state `st` whose `S`-shifted view is `St.init (encodeNat N)`, it writes
  `encodeNat N.minFac` into array `S + 2`, touches no index `< S`, and costs at most `srcCost (drvC UP) (encodeNat N)`.
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

theorem uni_cspec : ∃ B : ℕ → ℕ, CSpec (uniC UP) B ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, B n ≤ C * 2 ^ (n / k) := by
  obtain ⟨c, E, hc⟩ := uniC_cost
  obtain ⟨Z, hR, hZ⟩ := uniReq_exp
  refine ⟨fun n => c * (2 ^ Z n + 1) ^ E, ?_, ?_⟩
  · refine ⟨fun st => ?_, uniC_le_one, fun st hkn hN hD _ => uniC_val st hkn hN hD,
      fun st hkn hA => hc _ st hkn hA (hR _)⟩
    obtain ⟨h1, h2⟩ := uniC_keeps st
    exact ⟨h1 0 (by norm_num) (by simp [Uni.Wu]), h1 2 (by norm_num) (by simp [Uni.Wu]),
      h1 4 (by norm_num) (by simp [Uni.Wu]), fun a ha => h2 a (by omega)⟩
  · intro k hk
    obtain ⟨C, hC⟩ := hZ ((E + 1) * k) (by nlinarith)
    exact ⟨c * 2 ^ (E * (C + 1)), fun n => by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (pow_absorb E k C n (Z n) hk (hC n))⟩

theorem drvC_sub : ∃ B : ℕ → ℕ, CSpec (uniC UP) B ∧ (∀ xs, srcCost (drvC (uniC UP)) xs ≤ 200 * (xs.length + 1) ^ 3 * (B xs.length + 1)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ xs : List Bool, srcCost (drvC (uniC UP)) xs ≤ C * 2 ^ (xs.length / k) := by
  obtain ⟨B, hB, hBk⟩ := uni_cspec
  refine ⟨B, hB, fun xs => drvC_cost _ B hB xs, fun k hk => ?_⟩
  obtain ⟨C1, hC1⟩ := hBk (4 * k) (by omega)
  refine ⟨200 * (4 * k + 1) ^ 3 * (C1 + 1), fun xs => ?_⟩
  set n := xs.length
  set P := 2 ^ (n / (4 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : n + 1 ≤ (4 * k + 1) * P := by
    have := le_two_pow_div n (4 * k) (by omega)
    nlinarith
  have hv : B n + 1 ≤ (C1 + 1) * P := by
    have := hC1 n; rw [← hP] at this; nlinarith
  have h4 : P ^ 4 ≤ 2 ^ (n / k) := by
    have h := mul_div_mul_le 4 k n
    calc P ^ 4 = 2 ^ (4 * (n / (4 * k))) := by rw [hP, ← pow_mul, mul_comm]
      _ ≤ 2 ^ (n / k) := Nat.pow_le_pow_right (by norm_num) h
  calc srcCost (drvC (uniC UP)) xs ≤ 200 * (n + 1) ^ 3 * (B n + 1) := drvC_cost _ B hB xs
    _ ≤ 200 * ((4 * k + 1) * P) ^ 3 * ((C1 + 1) * P) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu 3)) hv
    _ = 200 * (4 * k + 1) ^ 3 * (C1 + 1) * P ^ 4 := by ring
    _ ≤ 200 * (4 * k + 1) ^ 3 * (C1 + 1) * 2 ^ (n / k) := Nat.mul_le_mul_left _ h4

/-- the subroutine -/
def minFacCmd (S : ℕ) : Cmd := (drvC (uniC UP)).shift S

/-- **The subroutine's contract.** -/
theorem minFacCmd_spec (S : ℕ) (N : ℕ) (st : St) (h : unshift S st = St.init (encodeNat N)) :
    outOf ((Cmd.run (minFacCmd S) st).1.ar (S + 2)) = encodeNat N.minFac ∧
    (Cmd.run (minFacCmd S) st).2 = srcCost (drvC (uniC UP)) (encodeNat N) ∧
    LowEq S st (Cmd.run (minFacCmd S) st).1 := by
  obtain ⟨B, hB, -, -⟩ := drvC_sub
  obtain ⟨r1, r2, r3⟩ := run_shift S (drvC (uniC UP)) st
  rw [h] at r1 r2
  refine ⟨?_, r2, r3⟩
  have := drvC_out (uniC UP) B hB N
  have e : (Cmd.run (minFacCmd S) st).1.ar (S + 2) = (Cmd.run (drvC (uniC UP)) (St.init (encodeNat N))).1.ar 2 := by
    have := congrArg (fun s => s.ar 2) r1
    simpa [minFacCmd] using this
  rw [e]
  exact this

end ECDLP.L71
