import ECDLPv2.L132_Eng

/-!
# L115 / Br: `cntBr r S` is correct and polynomial in `V` (the real engine)
`cntBr_spec` : for every `Good` query and `FrameIn'` state (viewed through the shift `S`), `outOf` of array `2` is `encodeNat (Zc (r+1) x τ)`, and the cost is `≤ c (V+1)^(24*200+8)`
whenever `V` meets the family's `UniReq` at the input length.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000
noncomputable section
namespace ECDLP.L132
open ECDLP.L115 Finset Factoring.Aux Ex ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L96 ECDLP.L92 ECDLP.L104 ECDLP.L104R ECDLP.L61 ECDLP
  ECDLP.L85A ECDLP.L85B ECDLP.L88 ECDLP.L60 Factoring.Aux.Copied Factoring.Aux.Copied.PLib Uni ECDLP.L71 ECDLP.L109 ECDLP.L113 Computability

theorem yb4_le (V : ℕ) :
    200 * UCost85.YB 200 V ^ 4 ≤ (200 * (4 * 4096 ^ 200) ^ 4) * (V + 1) ^ (24 * 200 + 8) := by
  haveI : Fact (100 ≤ 200) := ECDLP.L85.fact200
  have h := Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (UCost85.YB_le (D := 200) V) 4)
  generalize V + 1 = X at h ⊢
  generalize (4096 : ℕ) ^ 200 = c at h ⊢
  refine le_trans h (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_assoc]

theorem cntLong_eq (r S : ℕ) : cntLong r S = longC S 110 111 (UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv (Ereal2 r) (gEreal2 r) (btReal2 r)) (ECDLP.L85B.tabMv (Ereal2 r) (gEreal2 r) (btReal2 r))) 100 101 102 103 2 104 105 106 := rfl

theorem cntLong_run (r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : 1400 ≤ S) (V : ℕ) (x : Inst) (τ : List Bool) (hG : Good (r + 1) x τ)
    (hT : T1 r ≤ (redInp x τ).len) (hU : (edgeFamily r).UniReq V (redInp x τ).len) (Sf1 : St)
    (hF : FrameIn r (redInp x τ) (unshift S Sf1)) :
    outOf ((Cmd.run (cntLong r S) Sf1).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧
    (Cmd.run (cntLong r S) Sf1).2 ≤ 200 * UCost85.YB 200 V ^ 4 + 64000 * (V + 1) ^ 5 := by
  haveI : Fact (100 ≤ 200) := ECDLP.L85.fact200
  have hnet := engine_value_mod_real r hr
  have hI := ECDLP.L104A.topIfaceF_edgeH r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r)
  let SD := ECDLP.L104A.shapeDataF_edgeH r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r)
  set s := unshift S Sf1 with hs
  have h0 : s.sc 0 = (redInp x τ).len := hF.1
  have h2 : s.sc 2 = 0 := hF.2.1
  have hT0 : T0of r ≤ (redInp x τ).len := le_trans (le_max_left _ _) hT
  have hT0p : 0 < T0of r := by unfold T0of; positivity
  have hlen : 1 ≤ (redInp x τ).len := by omega
  have hn : 4 * Uc r ^ 4 ≤ (redInp x τ).len := le_trans (le_max_right _ _) hT
  have hPs : PL r (s.sc 0) s.ar := by rw [h0]; exact pl_of_frame r x τ hG hT s hF
  have hR : (famH r).UniReq V (s.sc 0) := by rw [h0]; exact uniReq_famH hU (V_ge_Ub hn hU)
  have key := long_run hI (famH_spec r) SD S 110 111 100 101 102 103 2 104 105 106 hS (by omega) (by omega) (by norm_num)
    (by decide) V Sf1 (cnt := Zc (r + 1) x τ) hPs (by show s.sc 2 < s.sc 0; omega) hR
  have hcnt : ∀ m, 1 < m → ((SD.D m (s.sc 0) (s.sc 2) s.ar).inner.value : ZMod m) = ((Zc (r + 1) x τ : ℕ) : ZMod m) :=
    fun m hm => by rw [h0, h2]; exact hnet x τ hG hT s hF m hm
  have hzl : Zc (r + 1) x τ < 2 ^ (s.sc 0) := by rw [h0]; exact zc_lt_len_real r x τ hG hT
  obtain ⟨o1, o2⟩ := key hcnt hzl
  rw [cntLong_eq]
  rw [← hs] at o2
  refine ⟨o1, ?_⟩
  have hM := hR.main.hM
  have hMof : (famH r).Mof K0u (ellOf (s.sc 0)) (s.sc 0) = s.sc 0 + mlogN K0u (ellOf (s.sc 0)) ((famH r).Ltop (Kb K0u (ellOf (s.sc 0))) (Gs K0u (ellOf (s.sc 0))) (s.sc 0)) + 4 := rfl
  have ht := tail_V (2 * (s.sc 0 + mlogN K0u (ellOf (s.sc 0)) ((famH r).Ltop (Kb K0u (ellOf (s.sc 0))) (Gs K0u (ellOf (s.sc 0))) (s.sc 0)) + 4) - 1) V (by omega)
  omega


theorem run_br (A B : Cmd) (q i j k : ℕ) (Sf : St) :
    Cmd.run (Cmd.seq (Cmd.setK q k) (Cmd.ifLt i j A B)) Sf =
      ((if (Sf.setSc q k).sc i < (Sf.setSc q k).sc j then Cmd.run A (Sf.setSc q k) else Cmd.run B (Sf.setSc q k)).1,
       1 + ((if (Sf.setSc q k).sc i < (Sf.setSc q k).sc j then Cmd.run A (Sf.setSc q k) else Cmd.run B (Sf.setSc q k)).2 + 1) + 1) := by
  simp only [Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt]

theorem fin_short (sB K X cost : ℕ) (hc : cost ≤ sB) (hX : 1 ≤ X) :
    1 + (cost + 1) + 1 ≤ (sB + K + 64000 + 4) * X := by
  have : sB + 3 ≤ (sB + K + 64000 + 4) * X := le_trans (by omega) (Nat.le_mul_of_pos_right _ hX)
  omega

theorem fin_long (sB K X P5 yb cost : ℕ) (hX : 1 ≤ X) (hP : P5 ≤ X) (hy : yb ≤ K * X)
    (hc : cost ≤ yb + 64000 * P5) :
    1 + (cost + 1) + 1 ≤ (sB + K + 64000 + 4) * X := by
  have h1 : 64000 * P5 ≤ 64000 * X := Nat.mul_le_mul_left _ hP
  have h2 : 4 * 1 ≤ 4 * X := Nat.mul_le_mul_left _ hX
  have h3 : (sB + K + 64000 + 4) * X = sB * X + K * X + 64000 * X + 4 * X := by ring
  have h4 : 0 ≤ sB * X := Nat.zero_le _
  omega

theorem cntBr_spec (r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : 1400 ≤ S) :
    ∃ c : ℕ, ∀ (V : ℕ) (x : Inst) (τ : List Bool), Good (r + 1) x τ → (edgeFamily r).UniReq V (redInp x τ).len →
      ∀ Sf : St, FrameIn' r (redInp x τ) (unshift S Sf) →
      outOf ((Cmd.run (cntBr r S) Sf).1.ar 2) = encodeNat (Zc (r + 1) x τ) ∧
      (Cmd.run (cntBr r S) Sf).2 ≤ c * (V + 1) ^ (24 * 200 + 8) := by
  refine ⟨shortB r + 200 * (4 * 4096 ^ 200) ^ 4 + 64000 + 4, fun V x τ hG hU Sf hF => ?_⟩
  set Sf1 := Sf.setSc (S + 22) (T1 r) with hSf1
  have hu1 : unshift S Sf1 = (unshift S Sf).setSc 22 (T1 r) := unshift_setSc S Sf 22 _
  have e0 : ((unshift S Sf).setSc 22 (T1 r)).sc 0 = (unshift S Sf).sc 0 := by simp [St.setSc, Function.update_of_ne]
  have hF2 : FrameIn r (redInp x τ) (unshift S Sf1) := by
    rw [hu1]
    exact ⟨by rw [e0]; exact hF.1.1, by simpa [St.setSc, Function.update_of_ne] using hF.1.2.1, reads72n_sc0 e0 hF.1.2.2⟩
  have h0 : (unshift S Sf).sc 0 = (redInp x τ).len := hF.1.1
  have s0 : Sf1.sc (S + 0) = (redInp x τ).len := by
    rw [hSf1, St.setSc_sc, Function.update_of_ne (by omega)]; exact h0
  have s22 : Sf1.sc (S + 22) = T1 r := by rw [hSf1, St.setSc_sc]; simp
  have hrun : Cmd.run (cntBr r S) Sf =
      ((if Sf1.sc (S + 0) < Sf1.sc (S + 22) then Cmd.run (cntShort r S) Sf1 else Cmd.run (cntLong r S) Sf1).1,
       1 + ((if Sf1.sc (S + 0) < Sf1.sc (S + 22) then Cmd.run (cntShort r S) Sf1 else Cmd.run (cntLong r S) Sf1).2 + 1) + 1) :=
    run_br (cntShort r S) (cntLong r S) (S + 22) (S + 0) (S + 22) (T1 r) Sf
  have hYB := yb4_le V
  have hp1 : 1 ≤ (V + 1) ^ (24 * 200 + 8) := Nat.one_le_pow _ _ (by omega)
  have hp5 : (V + 1) ^ 5 ≤ (V + 1) ^ (24 * 200 + 8) := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [hrun]
  by_cases hlt : (redInp x τ).len < T1 r
  · have hc : Sf1.sc (S + 0) < Sf1.sc (S + 22) := by rw [s0, s22]; exact hlt
    simp only [hc, if_true]
    obtain ⟨o1, o2⟩ := cntShort_run r S hS x τ hG Sf1 hF2 hlt
    exact ⟨o1, fin_short _ _ _ _ o2 hp1⟩
  · have hc : ¬ Sf1.sc (S + 0) < Sf1.sc (S + 22) := by rw [s0, s22]; exact hlt
    simp only [hc, if_false]
    obtain ⟨o1, o2⟩ := cntLong_run r hr S hS V x τ hG (by omega) hU Sf1 hF2
    exact ⟨o1, fin_long (shortB r) _ _ _ _ _ hp1 hp5 hYB o2⟩

end ECDLP.L132
end
