import ECDLP.L104_Core
import ECDLP.L92_Merge
import ECDLP.L92_Br
import ECDLP.L93_Main

/-!
# L104 / Eng: `EngCostF` / `EngValF` (the engine contracts only at `Good` `FrameIn'` states), the oracle with them, the merge, and the engine from `EdgeCoreF`
`EngCostF r eng` : cost bound for `eng` run from a state `s` with `FrameIn' r (redInp x tau) s`, `Good (r+1) x tau` (L92 `oracle_spec'` applies the contract only at such states).
-/
noncomputable section
namespace ECDLP.L104
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L78 ECDLP.L87 ECDLP.L60 ECDLP.L80 ECDLP.L92 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

def EngCostF (r : ℕ) (eng : Cmd) : Prop :=
  ∃ c E : ℕ, ∀ (V : ℕ) (x : Inst) (τ : List Bool), Good (r + 1) x τ → (edgeFamily r).UniReq V (redInp x τ).len →
    ∀ s : St, FrameIn' r (redInp x τ) s → (Cmd.run eng s).2 ≤ c * (V + 1) ^ E

theorem engRateF (r : ℕ) (eng : Cmd) (h : EngCostF r eng) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → ∀ s : St, FrameIn' r (redInp x τ) s →
      (Cmd.run eng s).2 ≤ C * 2 ^ ((redInp x τ).len / k) := by
  obtain ⟨c, E, hc⟩ := h
  obtain ⟨Z, hR, hZ⟩ := NetFamily.uniReq_expG (edgeFamily_spec r)
  intro k hk
  obtain ⟨C, hC⟩ := hZ ((E + 1) * k) (by nlinarith)
  refine ⟨c * 2 ^ (E * (C + 1)), fun x τ hg s hF => ?_⟩
  calc (Cmd.run eng s).2 ≤ c * (2 ^ Z (redInp x τ).len + 1) ^ E := hc _ x τ hg (hR _) s hF
    _ ≤ c * (2 ^ (E * (C + 1)) * 2 ^ ((redInp x τ).len / k)) :=
        Nat.mul_le_mul_left _ (pow_absorb E k C (redInp x τ).len (Z (redInp x τ).len) hk (hC _))
    _ = c * 2 ^ (E * (C + 1)) * 2 ^ ((redInp x τ).len / k) := by ring

set_option maxHeartbeats 4000000 in
theorem oracleF_spec (r S : ℕ) (hS : 1400 ≤ S) (eng : Cmd) (hv : EngVal' r eng) (hc : EngCostF r eng) :
    ∃ Tc : ℕ → ℕ, ESpec (r + 1) (oraC1 (r + 1) S eng) Tc ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k) := by
  classical
  have hk := engRateF r eng hc
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
    have hAk : 1 ≤ A * k := by nlinarith
    have a2 := hC (A * k) hAk x τ hgood (unshift S Y.1) hF
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


theorem mergeF_data (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal' r eng) (H_cost : EngCostF r eng) :
    ∃ (c G : Cmd) (T Tg : ℕ → ℕ), GateSpec Gx G fl Tg ∧ ZSpecAt Gx (r + 1) c T ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k)) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) := by
  obtain ⟨Tc, hE, hT⟩ := oracleF_spec r S hS eng H_val H_cost
  obtain ⟨Tg, hG, hTg⟩ := gate_hook' S q hS hq1 hqS Gx2 (hookCmd (r + 1)) fl 775 hfl (Th (r + 1)) (hook_spec (r + 1) (by omega))
  have hz := zspecAt_of_wrap (lspec_len (r + 1) (by omega)) hE
  refine ⟨_, _, _, Tg, hG, hz, ?_, hTg (fun k hk => Th_subexp (r + 1) k hk)⟩
  intro k hk
  obtain ⟨C1, h1⟩ := Tl_subexp (r + 1) k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

theorem subexponentialRate_engF (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal' r eng) (H_cost : EngCostF r eng) : (ECDLP.SubexponentialRateStmt (r + 1)) := by
  obtain ⟨c, G, T, Tg, hG, hz, hT, hTg⟩ := mergeF_data r eng S q fl hS hq1 hqS hfl H_val H_cost
  exact subexponentialRate_gate_strong_enc (r + 1) c G fl T Tg hG hz hT hTg

/-- the branch command for `EngCostF` -/
theorem engBrF_cost (r T : ℕ) (eng : Cmd) (c E' : ℕ)
    (h : ∀ (V : ℕ) (x : Inst) (τ : List Bool), Good (r + 1) x τ → (edgeFamily r).UniReq V (redInp x τ).len →
      T ≤ (redInp x τ).len → ∀ s : St, FrameIn' r (redInp x τ) s → (Cmd.run eng s).2 ≤ c * (V + 1) ^ E') :
    EngCostF r (engBr r T eng) := by
  refine ⟨c + 38 * T + 4, E', fun V x τ hg hU s hF => ?_⟩
  have h0 : s.sc 0 = (redInp x τ).len := hF.1.1
  have e0 : (s.setSc 22 T).sc 0 = s.sc 0 := by simp [St.setSc, Function.update_of_ne]
  have e22 : (s.setSc 22 T).sc 22 = T := by simp [St.setSc]
  have hF2 : FrameIn' r (redInp x τ) (s.setSc 22 T) :=
    ⟨⟨by rw [e0]; exact hF.1.1, by simpa [St.setSc, Function.update_of_ne] using hF.1.2.1,
      reads72n_sc0 e0 hF.1.2.2⟩, hF.2⟩
  have ex : (c + 38 * T + 4) * (V + 1) ^ E' = c * (V + 1) ^ E' + (38 * T + 4) * (V + 1) ^ E' := by ring
  have hp : 1 ≤ (V + 1) ^ E' := Nat.one_le_pow _ _ (by omega)
  have k1 : 38 * T + 4 ≤ (38 * T + 4) * (V + 1) ^ E' := by
    calc 38 * T + 4 = (38 * T + 4) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  simp only [engBr, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
  by_cases hlt : s.sc 0 < T
  · simp only [hlt, if_true]
    have := look_cost (r + 1) T (s.setSc 22 T) (by rw [e0]; exact hlt)
    omega
  · simp only [hlt, if_false]
    have hE := h V x τ hg hU (by omega) (s.setSc 22 T) hF2
    omega

end ECDLP.L104
end
