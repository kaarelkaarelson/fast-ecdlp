import ECDLP.L61_Out

/-!
# L61 / Driver: the whole source-level driver `drvZ m c` and its specification

Analogue of Rudich's `drvC` / `drvC_spec` (`FactoringAux/UniDrv.lean`, `UniDrvSpec.lean`) for our input and output:
parse the prefix block of the input, test it with the oracle command `c`, compute the round count, run the rounds
of `stepF`, write `encOut`.
-/
namespace ECDLP.L61
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def drvZ (m : ℕ) (c : Cmd) : Cmd :=
  .seq (.loop 0 1 parseBody)
    (.seq c (.ifZero 3 noneOut
      (.seq (boundCmd m) (.seq (.loop 9 1 (roundBody c)) someOut))))

theorem stepF_len (Z : List Bool → ℕ) (p : List Bool × Bool) : (stepF Z p).1.length ≤ p.1.length + 1 := by
  obtain ⟨τ, d⟩ := p
  cases d <;> simp [stepF] <;> split_ifs <;> simp

theorem iter_len (Z : List Bool → ℕ) (π : List Bool) :
    ∀ i, ((stepF Z)^[i] (π, false)).1.length ≤ π.length + i
  | 0 => by simp
  | i + 1 => by
      rw [Function.iterate_succ_apply']
      have := stepF_len Z ((stepF Z)^[i] (π, false))
      have := iter_len Z π i
      omega

theorem RInv_setSc1 {A L R τ d} {s : St} (h : RInv A L R τ d s) (j : ℕ) : RInv A L R τ d (s.setSc 1 j) := by
  obtain ⟨h0, hA, h9, h2, hc, h5⟩ := h
  exact ⟨by simpa using h0, by simpa using hA, by simpa using h9, by simpa using h2, by simpa using hc,
    by simpa using h5⟩

/-- The bound on the source cost. -/
def drvBound (m L T : ℕ) : ℕ := (m * (L + 1) + 2) * (2 * T + 31) + (m + 2) * (40 * L + 40) + 100

theorem drvZ_spec (m : ℕ) (c : Cmd) (xs π r : List Bool) (hxs : xs = block π ++ r)
    (Z : List Bool → ℕ) (ok : List Bool → Prop) (T : ℕ)
    (hk : Keep c) (ho : Orc c (startingMemory xs) xs.length Z ok T) (hπ : ok π)
    (hW : 0 < Z π → ∀ i, i < m * (xs.length + 1) + 1 → ((stepF Z)^[i] (π, false)).2 = false →
      ok (((stepF Z)^[i] (π, false)).1 ++ [false]) ∧ ok (((stepF Z)^[i] (π, false)).1 ++ [true])) :
    outOf ((srcOut (drvZ m c) xs).ar 2) =
      ECDLP.encOut (if 0 < Z π then some (((stepF Z)^[m * (xs.length + 1) + 1] (π, false)).1) else none) ∧
    srcCost (drvZ m c) xs ≤ drvBound m xs.length T := by
  subst hxs
  simp only [srcOut, srcCost, drvZ, Cmd.run_seq, Cmd.run_ifZero]
  set L := (block π ++ r).length with hL
  have hπL : π.length ≤ L := by
    have := block_length π; rw [hL]; simp only [List.length_append]; omega
  set st0 := St.init (block π ++ r) with hst0
  have e2 : st0.sc 2 = 0 := by simp [st0, St.init]
  have e5 : st0.sc 5 = 0 := by simp [st0, St.init]
  have e7 : st0.sc 7 = 0 := by simp [st0, St.init]
  have e8 : st0.sc 8 = 0 := by simp [st0, St.init]
  obtain ⟨p2, pc, p0, pA, psc, par, pcost⟩ := parse_run π r st0 rfl rfl e2 e7 e8
  have p0' : (Cmd.run (.loop 0 1 parseBody) st0).1.sc 0 = L := p0
  have pA' : (Cmd.run (.loop 0 1 parseBody) st0).1.ar 0 = startingMemory (block π ++ r) := pA
  have p5 : (Cmd.run (.loop 0 1 parseBody) st0).1.sc 5 = 0 := by
    rw [psc 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e5]
  have pcost' : (Cmd.run (.loop 0 1 parseBody) st0).2 ≤ 21 * L + 1 := pcost
  generalize hs1 : Cmd.run (.loop 0 1 parseBody) st0 = s1 at p2 pc p0' pA' p5 pcost' ⊢
  have hv := ho.val s1.1 π p0' pA' p2 pc hπ
  have hkS := hk.sc s1.1
  have hkA := hk.ar s1.1
  generalize hr2 : Cmd.run c s1.1 = r2 at hv hkS hkA ⊢
  have r20 : r2.1.sc 0 = L := by rw [hkS 0 (by norm_num) (by norm_num), p0']
  by_cases hp : 0 < Z π
  · have h3 : r2.1.sc 3 ≠ 0 := by rw [hv.1]; simp [hp]
    simp only [h3, if_false, Cmd.run_seq, hp, if_true]
    obtain ⟨b9, b0, bsc, bar, bcost⟩ := boundCmd_run m r2.1
    rw [r20] at b9 bcost
    set R := m * (L + 1) + 1 with hR
    generalize hsb : Cmd.run (boundCmd m) r2.1 = sb at b9 b0 bsc bar bcost ⊢
    have hRI : RInv (startingMemory (block π ++ r)) L R π false sb.1 := by
      refine ⟨?_, ?_, b9, ?_, ?_, ?_⟩
      · rw [b0, r20]
      · rw [bar 0, hkA 0 (by norm_num), pA']
      · rw [bsc 2 (by norm_num) (by norm_num), hkS 2 (by norm_num) (by norm_num), p2]
      · intro j hj
        rw [bar 1, hkA 1 (by norm_num)]
        exact pc j hj
      · rw [bsc 5 (by norm_num) (by norm_num), hkS 5 (by norm_num) (by norm_num), p5]; simp
    let P : ℕ → St → Prop := fun j s => RInv (startingMemory (block π ++ r)) L R
      ((stepF Z)^[j] (π, false)).1 ((stepF Z)^[j] (π, false)).2 s
    have hstep : ∀ j s, j < sb.1.sc 9 → P j s → P (j + 1) (Cmd.run (roundBody c) (s.setSc 1 j)).1 := by
      intro j s hj hs
      rw [b9] at hj
      have := (round_step c _ L R T Z ok hk ho _ _ (s.setSc 1 j) (RInv_setSc1 hs j) (hW hp j hj))
      show RInv _ L R (((stepF Z)^[j + 1]) (π, false)).1 (((stepF Z)^[j + 1]) (π, false)).2 _
      rw [Function.iterate_succ_apply']
      exact this.1
    have hcost : ∀ j s, j < sb.1.sc 9 → P j s → (Cmd.run (roundBody c) (s.setSc 1 j)).2 ≤ 2 * T + 30 := by
      intro j s hj hs
      rw [b9] at hj
      exact (round_step c _ L R T Z ok hk ho _ _ (s.setSc 1 j) (RInv_setSc1 hs j) (hW hp j hj)).2
    have hP0 : P 0 sb.1 := hRI
    have hI := Cmd.loop_inv (b := 9) (c := 1) (body := roundBody c) P hP0 hstep
    have hC := Cmd.loop_cost_le (b := 9) (c := 1) (body := roundBody c) P (2 * T + 30) hP0 hstep hcost
    rw [b9] at hI hC
    generalize hsl : Cmd.run (.loop 9 1 (roundBody c)) sb.1 = sl at hI hC ⊢
    obtain ⟨_, _, _, i2, ic, _⟩ := hI
    obtain ⟨o1, o2⟩ := someOut_run _ sl.1 i2 ic
    have hlen := iter_len Z π R
    refine ⟨o1, ?_⟩
    simp only [drvBound]
    have hmL : m ≤ m * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hcl : R * (2 * T + 30 + 1) = m * (L + 1) * (2 * T + 31) + 2 * T + 31 := by rw [hR]; ring
    have hlen' : ((stepF Z)^[R] (π, false)).1.length ≤ L + R := by omega
    have e2 : (m + 1) * (2 * L + 4) = 2 * (m * (L + 1)) + 2 * m + 2 * L + 4 := by ring
    have e3 : (m * (L + 1) + 2) * (2 * T + 31) = m * (L + 1) * (2 * T + 31) + 4 * T + 62 := by ring
    have e4 : (m + 2) * (40 * L + 40) = 40 * (m * (L + 1)) + 80 * L + 80 := by ring
    rw [e3, e4]
    omega
  · have h3 : r2.1.sc 3 = 0 := by rw [hv.1]; simp [hp]
    simp only [h3, if_true, hp, if_false]
    obtain ⟨o1, o2⟩ := noneOut_run r2.1
    refine ⟨o1, ?_⟩
    simp only [drvBound]
    have e4 : (m + 2) * (40 * L + 40) = 40 * (m * (L + 1)) + 80 * L + 80 := by ring
    have e3 : (m * (L + 1) + 2) * (2 * T + 31) = m * (L + 1) * (2 * T + 31) + 4 * T + 62 := by ring
    rw [e3, e4]
    omega

end ECDLP.L61
