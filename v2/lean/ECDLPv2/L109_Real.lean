import ECDLPv2.L109_Res

/-!
# L109 / Real: the REAL engine's residue register
`real_residue`: for every `r ≥ 1`, every `Good` instance/prefix with `len ≥ T1 r` and every `FrameIn` state `s`, after `setup` the real
engine's `modBodyR` run for the modulus `j ≥ 2` leaves in scalar 308 the residue `(deepMult · Zc : ZMod j).val` -- the number of generic
decompositions with the prefix, times the engine's known multiplier, modulo `j`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000
noncomputable section
namespace ECDLP.L109
open Finset Factoring.Aux Ex ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L96 ECDLP.L92 ECDLP.L104 ECDLP.L104R ECDLP.L61 ECDLP
  ECDLP.L85A ECDLP.L85B ECDLP.L88 ECDLP.L60 Factoring.Aux.Copied Factoring.Aux.Copied.PLib Uni

/-- the real engine's parts -/
abbrev realU (r : ℕ) : UParts :=
  UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv (Ereal2 r) (gEreal2 r) (btReal2 r)) (ECDLP.L85B.tabMv (Ereal2 r) (gEreal2 r) (btReal2 r))

theorem engCmd_real (r : ℕ) : ECDLP.L84.engCmd r (Ereal2 r) (gEreal2 r) (btReal2 r) = uniC (realU r) := rfl

theorem real_residue (r : ℕ) (hr : 1 ≤ r) (x : ECDLP.Inst) (τ : List Bool) (hG : Good (r + 1) x τ)
    (hT : T1 r ≤ (redInp x τ).len) (s : St) (hF : FrameIn r (redInp x τ) s) (j : ℕ) (hj : 2 ≤ j) :
    (Cmd.run (modBodyR (realU r)) ((Cmd.run (setup (realU r)) s).1.setSc 300 j)).1.sc 308 =
      (((deepMult K0u (ellOf (redInp x τ).len) ((famH r).Ltop (Kb K0u (ellOf (redInp x τ).len))
          (Gs K0u (ellOf (redInp x τ).len)) (redInp x τ).len) : ℕ) : ZMod j) * ((Zc (r + 1) x τ : ℕ) : ZMod j)).val := by
  have : Fact (100 ≤ 200) := ECDLP.L85.fact200
  have hPfr : ∀ (x : ECDLP.Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      PL r (redInp x τ).len s.ar := fun x τ hG hT s hF => pl_of_frame r x τ hG hT s hF
  have hnet := engine_value_mod_real r hr
  have hI := ECDLP.L104A.topIfaceF_edgeH r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r)
  let SD := ECDLP.L104A.shapeDataF_edgeH r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r)
  have h0 : s.sc 0 = (redInp x τ).len := hF.1
  have h2 : s.sc 2 = 0 := hF.2.1
  have hlen : 1 ≤ (redInp x τ).len := by unfold EdgeInp.len; omega
  have hPs : PL r (s.sc 0) s.ar := by rw [h0]; exact hPfr x τ hG hT s hF
  obtain ⟨s11, s307, s316, s12, s303, s310, stok, sfr, sar⟩ := ECDLP.L104A.setupF_spec' hI s
  generalize hb : (Cmd.run (setup (realU r)) s).1 = b1 at s11 s307 s316 s12 s303 s310 stok sfr sar ⊢
  have sar' : b1.ar = s.ar := sar
  have b0 : b1.sc 0 = s.sc 0 := sfr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2' : b1.sc 2 = s.sc 2 := sfr 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hkn : s.sc 2 < s.sc 0 := by omega
  have := modBodyR_spec' (L0X := ECDLP.L85B.edgeL0v r) SD b1 j (n := s.sc 0) (k := s.sc 2) (ℓ := ellOf (s.sc 0)) (cnt := Zc (r + 1) x τ)
    (by rw [sar']; exact hPs) s11 b0 b2' hkn s307 s316 s12 s303 stok hj
    (by
      have e : SD.D j (s.sc 0) (s.sc 2) b1.ar = SD.D j (s.sc 0) (s.sc 2) s.ar := SD.hcong j _ _ _ _ (fun a _ => by rw [sar'])
      rw [e, h0, h2]
      exact hnet x τ hG hT s hF j (by omega))
  rw [this.1, h0]

end ECDLP.L109
end
#print axioms ECDLP.L109.real_residue
