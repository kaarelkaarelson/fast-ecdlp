import ECDLPv2.L132_Br
import ECDLPv2.L115_Top
import ECDLP.L104_Eng

/-!
# L115 / Ora: the counting oracle `cntOra r S = checkC; frameW' S; cntBr` and the guarded call `cc`
`cntOra_spec` : on `Conf` states with `Good` queries, array `2` gets `encodeNat (Zc (r+1) x τ)` within `Tc |encB x|` steps, `Tc` sub-exponential (L104 `oracleF_spec` pattern).
`cc_spec` : `CCSpec (r+1) (ccCmd)` with the L78 length guard (over-long prefixes give `0`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
noncomputable section
namespace ECDLP.L132
open ECDLP.L115 ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L78 ECDLP.L87 ECDLP.L60 ECDLP.L80 ECDLP.L92 ECDLP.L104
  Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

def cntOra (r S : ℕ) : Cmd := .seq (checkC (r + 1)) (.seq (frameW' S) (cntBr r S))

theorem run_seq3 (A B C : Cmd) (st : St) : Cmd.run (Cmd.seq A (Cmd.seq B C)) st =
    ((Cmd.run C (Cmd.run B (Cmd.run A st).1).1).1,
     (Cmd.run A st).2 + ((Cmd.run B (Cmd.run A st).1).2 + (Cmd.run C (Cmd.run B (Cmd.run A st).1).1).2 + 1) + 1) := by
  simp only [Cmd.run_seq]

theorem cntRateF (r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : 1400 ≤ S) :
    (∀ (V : ℕ) (x : Inst) (τ : List Bool), Good (r + 1) x τ → (edgeFamily r).UniReq V (redInp x τ).len →
      ∀ Sf : St, FrameIn' r (redInp x τ) (unshift S Sf) →
      outOf ((Cmd.run (cntBr r S) Sf).1.ar 2) = encodeNat (Zc (r + 1) x τ)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → ∀ Sf : St, FrameIn' r (redInp x τ) (unshift S Sf) →
      outOf ((Cmd.run (cntBr r S) Sf).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧ (Cmd.run (cntBr r S) Sf).2 ≤ C * 2 ^ ((redInp x τ).len / k) := by
  obtain ⟨c, hc⟩ := cntBr_spec r hr S hS
  obtain ⟨Z, hR, hZ⟩ := NetFamily.uniReq_expG (edgeFamily_spec r)
  refine ⟨fun V x τ hg hU Sf hF => (hc V x τ hg hU Sf hF).1, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := hZ ((24 * 200 + 8 + 1) * k) (by nlinarith)
  refine ⟨c * 2 ^ ((24 * 200 + 8) * (C + 1)), fun x τ hg Sf hF => ?_⟩
  obtain ⟨o1, o2⟩ := hc _ x τ hg (hR _) Sf hF
  refine ⟨o1, ?_⟩
  calc (Cmd.run (cntBr r S) Sf).2 ≤ c * (2 ^ Z (redInp x τ).len + 1) ^ (24 * 200 + 8) := o2
    _ ≤ c * (2 ^ ((24 * 200 + 8) * (C + 1)) * 2 ^ ((redInp x τ).len / k)) :=
        Nat.mul_le_mul_left _ (pow_absorb (24 * 200 + 8) k C (redInp x τ).len (Z (redInp x τ).len) hk (hC _))
    _ = c * 2 ^ ((24 * 200 + 8) * (C + 1)) * 2 ^ ((redInp x τ).len / k) := by ring

set_option maxHeartbeats 4000000 in
theorem cntOra_spec (r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : 1400 ≤ S) :
    ∃ Tc : ℕ → ℕ, (∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → Good (r + 1) x τ →
        outOf ((Cmd.run (cntOra r S) st).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧ (Cmd.run (cntOra r S) st).2 ≤ Tc (encB x).length) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k) := by
  classical
  obtain ⟨hval, hk⟩ := cntRateF r hr S hS
  choose! C hC using fun k (hk1 : 1 ≤ k) => ((cntRateF r hr S hS).2 k hk1)
  set A := r + 1 + 6 with hA
  let U : ℕ → ℕ → ℕ := fun k L => PB (r + 1) L + (C (A * k)) * 2 ^ ((L + 1) / k) + 10
  have hU : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → Good (r + 1) x τ → ∀ k, 1 ≤ k →
      outOf ((Cmd.run (cntOra r S) st).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧ (Cmd.run (cntOra r S) st).2 ≤ U k (encB x).length := by
    intro x st τ hconf hgood k hk1
    obtain ⟨hF, hcost, -, -⟩ := pre_frame' r S hS x τ st hconf hgood
    generalize hX : Cmd.run (checkC (r + 1)) st = X
    generalize hY : Cmd.run (frameW' S) X.1 = Y
    have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st = (Y.1, X.2 + Y.2 + 1) := by
      simp only [Cmd.run_seq, hX, hY]
    rw [hs2] at hF hcost
    simp only at hF hcost
    have hlen := len_red_le (r + 1) x τ hgood
    have hAk : 1 ≤ A * k := by nlinarith
    obtain ⟨a1, a2⟩ := hC (A * k) hAk x τ hgood Y.1 hF
    have a4 : (redInp x τ).len / (A * k) ≤ ((encB x).length + 1) / k := by
      calc (redInp x τ).len / (A * k) ≤ (A * ((encB x).length + 1)) / (A * k) :=
            Nat.div_le_div_right (by rw [hA]; nlinarith)
        _ = ((encB x).length + 1) / k := Nat.mul_div_mul_left _ _ (by omega)
    have a5 : 2 ^ ((redInp x τ).len / (A * k)) ≤ 2 ^ (((encB x).length + 1) / k) :=
      Nat.pow_le_pow_right (by norm_num) a4
    have a6 := Nat.mul_le_mul_left (C (A * k)) a5
    have hcopy : Cmd.run (cntOra r S) st = ((Cmd.run (cntBr r S) Y.1).1, X.2 + (Y.2 + (Cmd.run (cntBr r S) Y.1).2 + 1) + 1) := by
      have h := run_seq3 (checkC (r + 1)) (frameW' S) (cntBr r S) st
      rw [hX] at h
      rw [hY] at h
      exact h
    rw [hcopy]
    refine ⟨a1, ?_⟩
    show _ ≤ PB (r + 1) (encB x).length + C (A * k) * 2 ^ (((encB x).length + 1) / k) + 10
    simp only
    omega
  refine ⟨fun L => ⨅ k : ℕ, U (k + 1) L, ⟨fun x st τ hconf hgood => ?_, fun k hk1 => ?_⟩⟩
  · refine ⟨(hU x st τ hconf hgood 1 le_rfl).1, ?_⟩
    exact le_ciInf fun k => (hU x st τ hconf hgood (k + 1) (by omega)).2
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

end ECDLP.L132
end
