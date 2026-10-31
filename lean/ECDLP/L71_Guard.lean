import ECDLP.L71_Feed
import ECDLP.L61_Final

/-!
# L71 / Guard: the primality clause of L70's `Good`, decided on the input code `encB x`

`guardPrime S q = feed S q ; primeFlag S q`.  On a state holding `encB x` in array 0 (length in scalar 0) and a pristine
`S`-frame, scalar `1204` becomes `[x.1.Prime]`, within `C_k · 2^(L/k)` source steps for every `k ≥ 1` (`L = |encB x|`).
Constants: `S ≥ 1400`, scratch array `1 ≤ q < S` (not an array the caller needs afterwards).
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability ECDLP ECDLP.L61

def guardPrime (S q : ℕ) : Cmd := .seq (feed S q) (primeFlag S q)

theorem encB_split (x : Inst) :
    ∃ r, encB x = block (pre x) ++ block (encodeNat x.1) ++ r := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  refine ⟨[a, b, xR, yR].flatMap (fun n => block (encodeNat n)), ?_⟩
  simp [encB, pre]

theorem enc_len_le (x : Inst) : (encodeNat x.1).length ≤ (encB x).length := by
  obtain ⟨r, hr⟩ := encB_split x
  have := block_length (encodeNat x.1)
  rw [hr]; simp only [List.length_append]; omega

/-- **The primality guard.** -/
theorem guardPrime_spec (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ (x : Inst) (st : St), st.sc 0 = (encB x).length →
      st.ar 0 = startingMemory (encB x) → unshift S st = St.init [] →
      (Cmd.run (guardPrime S q) st).1.sc 1204 = (if x.1.Prime then 1 else 0) ∧
      (Cmd.run (guardPrime S q) st).2 ≤ C * 2 ^ ((encB x).length / k) := by
  intro k hk
  obtain ⟨C1, hC1⟩ := primeFlag_subexp S q (by omega) hqS k hk
  refine ⟨C1 + 25 * k + 40 + 2, fun x st h0 hA hpr => ?_⟩
  obtain ⟨r, hr⟩ := encB_split x
  obtain ⟨f1, f2, f3, f4, f5⟩ := feed_run S q hS hq1 hqS (pre x) (encodeNat x.1) r st
    (by rw [hA, hr]) (by rw [h0, hr]) hpr
  obtain ⟨g1, g2⟩ := hC1 x.1 _ f1 f2
  set L := (encB x).length with hL
  have hn : (encodeNat x.1).length ≤ L := enc_len_le x
  have hrun : Cmd.run (guardPrime S q) st =
      ((Cmd.run (primeFlag S q) (Cmd.run (feed S q) st).1).1,
        (Cmd.run (feed S q) st).2 + (Cmd.run (primeFlag S q) (Cmd.run (feed S q) st).1).2 + 1) := by
    simp only [guardPrime, Cmd.run_seq]
  rw [hrun]
  refine ⟨g1, ?_⟩
  have m1 : 2 ^ ((encodeNat x.1).length / k) ≤ 2 ^ (L / k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right hn)
  have a2 := le_two_pow_div L k (by omega)
  have a3 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have b1 : C1 * 2 ^ ((encodeNat x.1).length / k) ≤ C1 * 2 ^ (L / k) := Nat.mul_le_mul_left _ m1
  have b2 : 25 * st.sc 0 + 40 ≤ 25 * (k * 2 ^ (L / k)) + 40 * 2 ^ (L / k) := by
    rw [h0]; nlinarith
  nlinarith

end ECDLP.L71
