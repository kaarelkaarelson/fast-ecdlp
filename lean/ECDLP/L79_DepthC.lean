import ECDLP.L79_KindC
import ECDLP.L79_IbKindC
import ECDLP.L79_Depth

/-!
# L79 / DepthC: depth of the repaired mid kind (shallow digit)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (kParams2 kParams pfaKE midIn)

section
variable {u : ℕ}

theorem dp_midYD (D pfaE : Ex) : Ex.dp (midYD (u := u) D pfaE) = max (Ex.dp pfaE) (Ex.dp D) + 1 := by
  simp only [midYD, Ex.dp]

/-- depth of the guarded repaired mid expression, in terms of `dp` of the four oracles (with `dp digCmid = 5`):
`midDepthC` equals the formula of `dp_midKindE` with `Dd := 5` -/
theorem dp_midKindEC (nE epsE lE rE : Ex) :
    Ex.dp (guardE u (midKindEC (u := u) nE epsE lE rE)) =
      max (max (Ex.dp nE) (max (Ex.dp epsE) (max (max (max (Ex.dp lE) (max 6 5 + 1 + 1) + 1) 5 + 3)
        (max (max (Ex.dp rE) (max 6 5 + 1 + 1) + 1) 5 + 3) + 2) + 2) + 1) 5 + 13 := by
  have h1 := dpT_pos nE
  have h2 := dpT_pos epsE
  have h3 := dpT_pos lE
  have h4 := dpT_pos rE
  simp only [guardE, midKindEC, kParams2, kParams, midOutLD, midIn, dp_midYD, dp_midE_var, dp_pfaKE, dp_digCmid, Ex.dp]
  omega

/-- if the oracles have depth `<= d >= 8`, the guarded repaired mid expression has depth `<= d + 25` -/
theorem dp_midKindEC_le {d : ℕ} (hd : 8 ≤ d) (nE epsE lE rE : Ex) (h1 : Ex.dp nE ≤ d) (h2 : Ex.dp epsE ≤ d)
    (h3 : Ex.dp lE ≤ d) (h4 : Ex.dp rE ≤ d) : Ex.dp (guardE u (midKindEC (u := u) nE epsE lE rE)) ≤ d + 25 := by
  rw [dp_midKindEC]; omega

/-- depth of the repaired guarded fa expression: `max 20 (3 + 9) (dp phiE + 10) = max 20 (dp phiE + 10)` -/
theorem dp_faKindEC (phiE : Ex) :
    Ex.dp (guardE u (faKindEC (u := u) phiE)) = max 20 (Ex.dp phiE + 10) := by
  have h1 := dpT_pos phiE
  simp only [guardE, faKindEC, kParams, faOutLD, faInD, ECDLP.L68.faE, ECDLP.L74.faUE, ECDLP.L68.natE, ECDLP.L68.mulE,
    ECDLP.L68.pwE, ECDLP.L68.sumE, nprod, dp_digCfa, Ex.dp]
  omega

/-- depth of the repaired `ib` expression: `max (dp digCib + 9) 14 = 16` -/
theorem dp_ibOutIC : Ex.dp (ibOutIC (u := u)) = 16 := by
  simp only [ibOutIC, ECDLP.L75.e0I, ECDLP.L75.tEI, ECDLP.L75.kEI, ECDLP.L75.pmidEI, ibOutL2D, ECDLP.L75.ibE2, ibBodyD,
    ECDLP.L68.mulE, ECDLP.L68.hatE, ECDLP.L68.sumE, ECDLP.L68.pwE, dp_digCib, Ex.dp]
  omega


end

section carbound
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- **NEGATIVE, independent of the gate kinds.**  The car branch of L73's dispatch contains two `digE` reads under six binders, so for EVERY choice of the fa / mid / ib
kinds (in particular the repaired shallow ones) `dp outEx >= 61` (`15` decode binders, `1` for `u+20`, `4` dispatch tests, `6` binders in `carIn'`, `35` for `digE`).
Hence `dp E.l >= 69` and L72's `ExSyn` budget `60` is violated until the car gate is also repaired. -/
theorem dp_outEx_ge_61 (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) :
    61 ≤ Ex.dp (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) := by
  have h1 := dp_decodeE_ge I (u + 5) (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd)
  have h2 := dp_digE_pex0_ge (F := F) (ok := ok) (m := m) I Ph hu u (u + 1)
  have h3 := dp_carIn_ge L (pex0 (F := F) (ok := ok) (m := m) I Ph hu) (u + 92) (u + 93) (u + 94) (carJ I) (carPC (u := u)) (carPIB I)
    (carOutE (u + 10) (u + 11) (u + 92) (u + 93) (u + 94))
  have h4 : Ex.dp (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) ≥ Ex.dp (carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) + 5 := by
    simp only [outBody, outChain, Ex.dp]; omega
  have e : outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd = decodeE I (u + 5) (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) := rfl
  have e2 : carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) =
      carIn' (pex0 (F := F) (ok := ok) (m := m) I Ph hu) (u + 92) (u + 93) (u + 94) (carJ I) (carPC (u := u)) (carPIB I)
        (carOutE (u + 10) (u + 11) (u + 92) (u + 93) (u + 94)) := rfl
  rw [e2] at h4
  rw [e]
  omega

end carbound

end ECDLP.L79
end
