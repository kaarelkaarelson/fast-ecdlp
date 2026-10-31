import ECDLP.L92_Frame

/-!
# L92 / Orc: the per-call oracle with the repaired frame writer (`oraC1`), `EngVal'`, and `oracle_spec'`
(L80's `oracle_spec`, with `frameW'` and `FrameIn'`; the proofs are L80's with the extra `+2` cost of the zeroing `wr`.)
-/
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L60 ECDLP.L80 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

open Classical in
/-- `EngVal` on the repaired frame predicate -/
def EngVal' (r : ℕ) (eng : Cmd) : Prop :=
  ∀ (x : Inst) (τ : List Bool), ECDLP.L70.Good (r + 1) x τ → ∀ s : St, FrameIn' r (redInp x τ) s →
    (Cmd.run eng s).1.sc 3 = (if 0 < Zc (r + 1) x τ then 0 else 1)

def oraC1 (m S : ℕ) (eng : Cmd) : Cmd :=
  .seq (checkC m) (.seq (frameW' S) (.seq (eng.shift S) (.copy 3 (S + 3))))

theorem oraC1_keep (m S : ℕ) (hS : 1400 ≤ S) (eng : Cmd) : Keep (oraC1 m S eng) := by
  have h1 := checkC_rng m
  have h2 := frameW'_rng S hS
  have hsc : ∀ i, i < 10 → i ≠ 3 → i ∉ (oraC1 m S eng).wsc := by
    intro i hi h3 hm
    have e : (oraC1 m S eng).wsc = (checkC m).wsc ++ ((frameW' S).wsc ++ ((eng.shift S).wsc ++ [3])) := rfl
    rw [e] at hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm
    · have := (h1.1 i hm).1; omega
    · have := (h2.1 i hm).1; omega
    · have := shift_wsc S eng i hm; omega
    · exact h3 hm
  have har : ∀ a, a < 3 → a ∉ (oraC1 m S eng).war := by
    intro a ha hm
    have e : (oraC1 m S eng).war = (checkC m).war ++ ((frameW' S).war ++ ((eng.shift S).war ++ [])) := rfl
    rw [e] at hm
    simp only [List.mem_append, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm
    · have := (h1.2 a hm).1; omega
    · have := (h2.2 a hm).1; omega
    · have := shift_war S eng a hm; omega
  exact ⟨fun st i hi h3 => Cmd.run_sc_frame _ st i (hsc i hi h3), fun st a ha => Cmd.run_ar_frame _ st a (har a ha)⟩

set_option maxHeartbeats 4000000 in
theorem oracle_spec' (r S : ℕ) (hS : 1400 ≤ S) (eng : Cmd) (hv : EngVal' r eng) (hc : EngCost r eng) :
    ∃ Tc : ℕ → ℕ, ESpec (r + 1) (oraC1 (r + 1) S eng) Tc ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k) := by
  classical
  have hk := engRate r eng hc
  choose! C hC using hk
  set A := r + 1 + 6 with hA
  let U : ℕ → ℕ → ℕ := fun k L => PB (r + 1) L + C (A * k) * 2 ^ ((L + 1) / k) + 10
  have hU : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → ECDLP.L70.Good (r + 1) x τ → ∀ k, 1 ≤ k →
      (Cmd.run (oraC1 (r + 1) S eng) st).2 ≤ U k (encB x).length := by
    intro x st τ hconf hgood k hk1
    obtain ⟨hF, hcost, -, -⟩ := pre_frame' r S hS x τ st hconf hgood
    have hrun := run_shift S eng
    generalize hX : Cmd.run (checkC (r + 1)) st = X
    generalize hY : Cmd.run (frameW' S) X.1 = Y
    generalize hZ : Cmd.run (eng.shift S) Y.1 = Z
    have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st = (Y.1, X.2 + Y.2 + 1) := by
      simp only [Cmd.run_seq, hX, hY]
    rw [hs2] at hF hcost
    simp only at hF hcost
    have hZ2 : Z.2 = (Cmd.run eng (unshift S Y.1)).2 := by
      have := (hrun Y.1).2.1
      rw [← hZ]; exact this
    have hlen := len_red_le (r + 1) x τ hgood
    have hadm := adm_red r x τ hgood
    obtain ⟨⟨hF0, hF2, -⟩, -⟩ := hF
    have hF2' : (unshift S Y.1).sc 2 < (unshift S Y.1).sc 0 := by
      rw [hF2, hF0]; unfold EdgeInp.len; omega
    have hAk : 1 ≤ A * k := by nlinarith
    have a2 := hC (A * k) hAk (redInp x τ) hadm (unshift S Y.1) hF0 hF2'
    have a4 : (redInp x τ).len / (A * k) ≤ ((encB x).length + 1) / k := by
      calc (redInp x τ).len / (A * k) ≤ (A * ((encB x).length + 1)) / (A * k) :=
            Nat.div_le_div_right (by rw [hA]; nlinarith)
        _ = ((encB x).length + 1) / k := Nat.mul_div_mul_left _ _ (by omega)
    have a5 : 2 ^ ((redInp x τ).len / (A * k)) ≤ 2 ^ (((encB x).length + 1) / k) :=
      Nat.pow_le_pow_right (by norm_num) a4
    have a6 := Nat.mul_le_mul_left (C (A * k)) a5
    have hcopy : (Cmd.run (oraC1 (r + 1) S eng) st).2 = X.2 + (Y.2 + (Z.2 + 1 + 1) + 1) + 1 := by
      simp only [oraC1, Cmd.run_seq, Cmd.run_copy, hX, hY, hZ]
    show _ ≤ PB (r + 1) (encB x).length + C (A * k) * 2 ^ (((encB x).length + 1) / k) + 10
    rw [hcopy]
    omega
  refine ⟨fun L => ⨅ k : ℕ, U (k + 1) L, ⟨oraC1_keep (r + 1) S hS eng, fun x st τ hconf hok hgood => ?_⟩, fun k hk1 => ?_⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨hF, -, -, -⟩ := pre_frame' r S hS x τ st hconf hgood
      generalize hX : Cmd.run (checkC (r + 1)) st = X
      generalize hY : Cmd.run (frameW' S) X.1 = Y
      generalize hZ : Cmd.run (eng.shift S) Y.1 = Z
      have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st = (Y.1, X.2 + Y.2 + 1) := by
        simp only [Cmd.run_seq, hX, hY]
      rw [hs2] at hF
      simp only at hF
      have h3 : (Cmd.run (oraC1 (r + 1) S eng) st).1.sc 3 = Z.1.sc (S + 3) := by
        simp only [oraC1, Cmd.run_seq, Cmd.run_copy, hX, hY, hZ, St.setSc_sc, Function.update_self]
      rw [h3]
      have := (run_shift S eng Y.1).1
      rw [hZ] at this
      have e : Z.1.sc (S + 3) = (unshift S Z.1).sc 3 := rfl
      rw [e, this]
      exact hv x τ hgood _ hF
    · exact le_ciInf fun k => hU x st τ hconf hgood (k + 1) (by omega)
  · obtain ⟨Cp, hCp⟩ := PB_subexp (r + 1) k hk1
    refine ⟨Cp + 2 * C (A * k) + 10, fun L => ?_⟩
    have h1 : (⨅ k' : ℕ, U (k' + 1) L) ≤ U k L := by
      have := ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => U (k' + 1) L)) (k - 1)
      have e : k - 1 + 1 = k := by omega
      simpa [e] using this
    refine le_trans h1 ?_
    have h2 : 2 ^ ((L + 1) / k) ≤ 2 * 2 ^ (L / k) := by
      calc 2 ^ ((L + 1) / k) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) (div_succ_le L k hk1)
        _ = 2 * 2 ^ (L / k) := by ring
    have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    have h4 := Nat.mul_le_mul_left (C (A * k)) h2
    have h5 := hCp L
    show PB (r + 1) L + C (A * k) * 2 ^ ((L + 1) / k) + 10 ≤ _
    nlinarith

end ECDLP.L92
