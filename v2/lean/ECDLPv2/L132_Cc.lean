import ECDLPv2.L132_Ora

/-!
# L115 / Cc: the guarded counting call `ccCmd = lenCmd; ifZero 3 zeroOut cntOra` meets `CCSpec (r+1)`
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
namespace ECDLP.L132
open ECDLP.L115 ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L78 ECDLP.L80 ECDLP.L92
  Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

def ccCmd (r S : ℕ) : Cmd := .seq (lenCmd (r + 1)) (.ifZero 3 zeroOut (cntOra r S))

theorem run_lenif (A Z C : Cmd) (st : St) : Cmd.run (Cmd.seq A (Cmd.ifZero 3 Z C)) st =
    ((if (Cmd.run A st).1.sc 3 = 0 then Cmd.run Z (Cmd.run A st).1 else Cmd.run C (Cmd.run A st).1).1,
     (Cmd.run A st).2 + ((if (Cmd.run A st).1.sc 3 = 0 then Cmd.run Z (Cmd.run A st).1 else Cmd.run C (Cmd.run A st).1).2 + 1) + 1) := by
  rw [Cmd.run_seq, Cmd.run_ifZero]

theorem cc_spec (r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : 1400 ≤ S) :
    ∃ T : ℕ → ℕ, CCSpec (r + 1) (ccCmd r S) T ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k) := by
  classical
  obtain ⟨Tc, hTc, hsub⟩ := cntOra_spec r hr S hS
  have hg := lspec_len (r + 1) (by omega)
  refine ⟨fun L => Tl (r + 1) L + Tc L + 10, fun x st hGx hconf => ?_, fun k hk => ?_⟩
  · have hok : okInst (r + 1) x (pre x) := ⟨List.prefix_refl _, le_max_right _ _⟩
    obtain ⟨gv, gc⟩ := hg.spec x st (pre x) hconf hok hGx
    obtain ⟨h0, hA, h2, hbits⟩ := hconf
    have k0 := hg.keep.sc st 0 (by norm_num) (by norm_num)
    have k2 := hg.keep.sc st 2 (by norm_num) (by norm_num)
    have a0 := hg.keep.ar st 0 (by norm_num)
    have a1 := hg.keep.ar st 1 (by norm_num)
    unfold ccCmd
    rw [run_lenif]
    generalize hr1 : Cmd.run (lenCmd (r + 1)) st = r1 at gv gc k0 k2 a0 a1
    by_cases hG : (pre x).length ≤ nlen (r + 1) x
    · have hGood : Good (r + 1) x (pre x) := (good_iff (r + 1) x (pre x)).2 ⟨hGx, hG⟩
      have hz : r1.1.sc 3 ≠ 0 := by rw [gv]; simp [hG]
      have hconf' : Conf x (pre x) r1.1 := ⟨by rw [k0, h0], by rw [a0, hA], by rw [k2, h2], fun j hj => by rw [a1]; exact hbits j hj⟩
      obtain ⟨o1, o2⟩ := hTc x r1.1 (pre x) hconf' hGood
      simp only [hz, if_false]
      refine ⟨o1, ?_⟩
      omega
    · have hz : r1.1.sc 3 = 0 := by rw [gv]; simp [hG]
      have hZ : Zc (r + 1) x (pre x) = 0 := by
        by_contra hne
        exact hG (Zc_pos_len (r + 1) x (pre x) (Nat.pos_of_ne_zero hne))
      simp only [hz, if_true]
      obtain ⟨o1, o2⟩ := zeroOut_run r1.1
      rw [hZ, encodeNat_zero]
      exact ⟨o1, by omega⟩
  · obtain ⟨C1, h1⟩ := Tl_subexp (r + 1) k hk
    obtain ⟨C2, h2⟩ := hsub k hk
    refine ⟨C1 + C2 + 10, fun L => ?_⟩
    have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    have := h1 L
    have := h2 L
    nlinarith

end ECDLP.L132
end
