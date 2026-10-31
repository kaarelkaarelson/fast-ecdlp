import ECDLP.L71_Cmp
import FactoringAux.Copied.PlibFn

/-!
# L71 / Prime: a sub-exponential primality-flag command (Rudich's `minFac` command + a comparison)

`primeFlag S` (S ≥ 1208): scalar `1200 := ar5[0] + 1`; run `(drvC (uniC UP)).shift S`; then compare array `5`
(the caller's copy of `startingMemory (encodeNat N)`) with the output array `S + 2`; the flag is scalar `1204`.

Contract (`primeFlag_spec`): if the `S`-shifted view of the state is `St.init (encodeNat N)` and array `5` agrees with
`startingMemory (encodeNat N)` on its first `n + 1` cells, then scalar `1204` is `[N.Prime]`.  The cost is
`srcCost (drvC (uniC UP)) (encodeNat N) + 15 n + O(1)`, hence `≤ C_k 2^(n/k)` for every `k` (`primeFlag_cost`).
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

def primePre (q : ℕ) : Cmd := .seq (.setK 1206 0) (.seq (.rd 1200 q 1206 0) (.incr 1200))

def primeFlag (S q : ℕ) : Cmd := .seq (primePre q) (.seq (minFacCmd S) (cmpC q (S + 2)))

theorem startingMemory_zero' (xs : List Bool) : startingMemory xs 0 = xs.length := rfl

theorem encodeNat_inj' {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have := congrArg decodeNat h
  simpa using this

theorem prime_iff_cmp (N : ℕ) (out : ℕ → ℕ) (hout : outOf out = encodeNat N.minFac) :
    N.Prime ↔ (2 ≤ (encodeNat N).length ∧ startingMemory (encodeNat N) 0 = out 0 ∧
      ∀ i, i < (encodeNat N).length →
        (startingMemory (encodeNat N) (i + 1) = 0 ↔ out (i + 1) = 0)) := by
  set xs := encodeNat N with hxs
  have hlen : (outOf out).length = out 0 := length_outOf out
  constructor
  · intro hp
    have hm : N.minFac = N := (Nat.prime_def_minFac.mp hp).2
    rw [hm] at hout
    have h2 : 2 ≤ xs.length := two_le_length_encodeNat N hp.two_le
    have hl : out 0 = xs.length := by rw [← hlen, hout]
    refine ⟨h2, by rw [startingMemory_zero', hl], fun i hi => ?_⟩
    have hg : (outOf out).getD i false = xs.getD i false := by rw [hout]
    have hlt : i < (outOf out).length := by rw [hlen, hl]; exact hi
    rw [List.getD_eq_getElem _ _ hlt] at hg
    simp only [outOf, List.getElem_ofFn] at hg
    rw [startingMemory_succ]
    by_cases ho : out (i + 1) = 0 <;> by_cases hx : xs.getD i false = true <;> simp_all
  · rintro ⟨h2, h0, hb⟩
    have hl : out 0 = xs.length := by rw [← h0, startingMemory_zero']
    have hys : outOf out = xs := by
      apply List.ext_getElem
      · rw [hlen, hl]
      · intro i h1 h2'
        have hi : i < xs.length := h2'
        simp only [outOf, List.getElem_ofFn]
        have := hb i hi
        rw [startingMemory_succ] at this
        rw [List.getD_eq_getElem _ _ hi] at this
        by_cases ho : out (i + 1) = 0 <;> by_cases hx : xs[i] = true <;> simp_all
    have hm : N.minFac = N := encodeNat_inj' (by rw [← hout, hys])
    have hN : 2 ≤ N := by
      by_contra hc
      have : N = 0 ∨ N = 1 := by omega
      rw [hxs] at h2
      rcases this with rfl | rfl
      · have e : (encodeNat 0).length = 0 := rfl
        omega
      · have e : (encodeNat 1).length = 1 := rfl
        omega
    exact Nat.prime_def_minFac.mpr ⟨hN, hm⟩


theorem unshift_setSc_low (S : ℕ) (st : St) (x v : ℕ) (hx : x < S) : unshift S (st.setSc x v) = unshift S st := by
  apply St.ext
  · funext i; simp [unshift, St.setSc, Function.update_apply]; intro h; omega
  · rfl

theorem primeFlag_spec (S q : ℕ) (hS : 1208 ≤ S) (hq : q < S) (N : ℕ) (st : St) (h : unshift S st = St.init (encodeNat N))
    (h5 : ∀ i, i ≤ (encodeNat N).length → st.ar q i = startingMemory (encodeNat N) i) :
    (Cmd.run (primeFlag S q) st).1.sc 1204 = (if N.Prime then 1 else 0) ∧
    (Cmd.run (primeFlag S q) st).2 ≤ srcCost (drvC (uniC UP)) (encodeNat N) + 15 * (encodeNat N).length + 100 := by
  set xs := encodeNat N with hxs
  set n := xs.length with hn
  have hn' : n = (encodeNat N).length := rfl
  set s1 := ((st.setSc 1206 0).setSc 1200 (st.ar q 0)).setSc 1200 (st.ar q 0 + 1) with hs1
  have hpre : Cmd.run (primePre q) st = (s1, 5) := by
    simp [primePre, Cmd.run_seq, Cmd.run_setK, Cmd.run_rd, Cmd.run_incr, hs1, Function.update_apply]
  have e0 : st.ar q 0 = n := by rw [h5 0 (by omega), startingMemory_zero']
  have e1200 : s1.sc 1200 = n + 1 := by simp [hs1, e0]
  have hu : unshift S s1 = St.init xs := by
    rw [hs1, unshift_setSc_low S _ _ _ (by omega), unshift_setSc_low S _ _ _ (by omega),
      unshift_setSc_low S _ _ _ (by omega), h]
  obtain ⟨m1, m2, m3⟩ := minFacCmd_spec S N s1 hu
  generalize hr2 : Cmd.run (minFacCmd S) s1 = r2 at m1 m2 m3
  obtain ⟨c1, c2, c3⟩ := cmpC_run q (S + 2) r2.1 n (by rw [(m3.1 1200 (by omega)).symm, e1200])
  have l5 : ∀ i, r2.1.ar q i = st.ar q i := fun i => by rw [← m3.2 q (by omega)]; simp [hs1]
  have key := prime_iff_cmp N (r2.1.ar (S + 2)) m1
  have hrun : Cmd.run (primeFlag S q) st = ((Cmd.run (cmpC q (S + 2)) r2.1).1,
      5 + (r2.2 + (Cmd.run (cmpC q (S + 2)) r2.1).2 + 1) + 1) := by
    simp only [primeFlag, Cmd.run_seq, hpre, hr2]
  rw [hrun]
  refine ⟨?_, ?_⟩
  · rw [c1]
    have : (2 ≤ n ∧ r2.1.ar q 0 = r2.1.ar (S + 2) 0 ∧
        ∀ i, i < n → (r2.1.ar q (i + 1) = 0 ↔ r2.1.ar (S + 2) (i + 1) = 0)) ↔ N.Prime := by
      rw [key]
      simp only [l5]
      constructor
      · rintro ⟨a, b, c⟩
        exact ⟨a, by rw [← h5 0 (by omega)]; exact b, fun i hi => by rw [← h5 (i + 1) (by omega)]; exact c i hi⟩
      · rintro ⟨a, b, c⟩
        exact ⟨a, by rw [h5 0 (by omega)]; exact b, fun i hi => by rw [h5 (i + 1) (by omega)]; exact c i hi⟩
    simp only [this]
  · simp only
    rw [← m2] at *
    omega


/-- **Sub-exponential primality flag.**  For every `k ≥ 1` there is `C` such that for every `N` and every state meeting the
contract, scalar `1204` is `[N.Prime]` and the cost is `≤ C · 2^(n/k)`, `n = |encodeNat N|`. -/
theorem primeFlag_subexp (S q : ℕ) (hS : 1208 ≤ S) (hq : q < S) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ (N : ℕ) (st : St), unshift S st = St.init (encodeNat N) →
      (∀ i, i ≤ (encodeNat N).length → st.ar q i = startingMemory (encodeNat N) i) →
      (Cmd.run (primeFlag S q) st).1.sc 1204 = (if N.Prime then 1 else 0) ∧
      (Cmd.run (primeFlag S q) st).2 ≤ C * 2 ^ ((encodeNat N).length / k) := by
  intro k hk
  obtain ⟨B, hB, -, hBk⟩ := drvC_sub
  obtain ⟨C1, hC1⟩ := hBk k hk
  refine ⟨C1 + 15 * k + 100, fun N st h h5 => ?_⟩
  obtain ⟨f1, f2⟩ := primeFlag_spec S q hS hq N st h h5
  refine ⟨f1, le_trans f2 ?_⟩
  set n := (encodeNat N).length
  have a1 := hC1 (encodeNat N)
  have a2 := le_two_pow_div n k (by omega)
  have a3 : 1 ≤ 2 ^ (n / k) := Nat.one_le_two_pow
  nlinarith

end ECDLP.L71
