import ECDLP.L96_Core
import ECDLP.L96_Real2
import ECDLP.L94_Final
import ECDLP.L95_Syn
import ECDLP.L92_Hr3

/-!
# L96 / Final: the real network (L95's repaired instance `instEx2`, clamped dispatch) as an `EdgeCore 200`, and the capstone

`btReal2 r`: L94's `btEx` of the repaired instance.  Proved here for the real expressions `(Ereal2 r, gEreal2 r, btReal2 r)`:
`exSyn_real2` (L95 `exSyn200_real2C` + L94 `Sy_btEx/dp_btEx`), `noRdAll_real2`, `frameRep_real2`, `hbtE_real2` (L94 `eval_btEx`), `wtBnd_real` (L94 `wt_hmax/wt_htot`),
`realRep_real2`.  Remaining hypotheses of the capstone: `FrameBnd` and `OffFrame`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51 ECDLP.L85B

theorem readsR_of_frD {r n m k : ℕ} {B : ℕ → ℕ → ℕ} {d : FrData} (hB3 : ∀ j, B 3 j = 0) (hD : FrD r n B d) :
    ReadsR (CtxM m n k) B r d.p d.a d.b d.xR d.yR d.τ := by
  obtain ⟨hp0, hodd, ha, hb, hx, hy, hn, hRd, -⟩ := hD
  intro σ₁ hC1
  have h1 := reads72_zero3 (reads72n_congr0 hRd (show σ₁ 0 = (fun _ => n) 0 from hC1.2.2.1))
  rw [zero3_of_clear hB3] at h1
  exact h1

/-- the dummy reads hypothesis (empty context) -/
theorem dummyR (r : ℕ) : ReadsR (fun _ : ℕ → ℕ => False) (fun _ _ => 0) r 3 0 0 0 0 [] := fun _ h => h.elim

/-- **the weight expression of the real (repaired) network** -/
def btReal2 (r : ℕ) : Ex :=
  ECDLP.L94.btEx (rInst2 r 3 0 0 0 0 [] (dummyR r)) (rPhi2 r 3 0 0 0 0 [] (dummyR r)) 20

theorem hbtE_real2 (r : ℕ) : HbtE r (btReal2 r) := by
  intro d m n k B σ₀ hB3 hD hC σ hσ j hj
  have hR := readsR_of_frD (m := m) (k := k) hB3 hD
  exact ECDLP.L94.eval_btEx (rInst2 r d.p d.a d.b d.xR d.yR d.τ hR) (rPhi2 r d.p d.a d.b d.xR d.yR d.τ hR)
    (by norm_num : 13 ≤ 16) hC hσ (NParE (Nat.size d.p)).toPar.A_pos (by norm_num) hj

theorem wtBnd_real (r : ℕ) : WtBnd r := by
  intro d m n hp hn
  exact ⟨fun j => ECDLP.L94.wt_hmax (n := r) (ℓ := ell d.p r) (π := d.τ) (p := d.p) n hn _ j,
    ECDLP.L94.wt_htot (n := r) (ℓ := ell d.p r) (π := d.τ) (p := d.p) n hn _⟩

theorem noRd_bt2 (r : ℕ) : NoRd Out (btReal2 r) :=
  ECDLP.L94.NoRd_btEx (ECDLP.L95.instNoRd_real2 (n := r) (by norm_num) (dummyR r))
    (ECDLP.L90.NoRd_phiExInst (n := r) (B := 13) (by norm_num) (dummyR r)) 20

theorem noRdAll_real2 (r : ℕ) : NoRdAll (Ereal2 r) (gEreal2 r) (btReal2 r) := by
  have hN := realPNoRd2 (Ctx := fun _ => False) (A := fun _ _ => 0) r 3 0 0 0 0 [] 2 (by norm_num)
    (fun _ h => h.elim) (by norm_num)
  obtain ⟨n1, n2, n3, n4, n5⟩ := NoRd_Efields hN
  exact ⟨n1, n2, n3, n4, n5, NoRd_gOf hN, noRd_bt2 r⟩


/-- **`ExSyn 200` for the real clamped network with the real `btE`** (L95 `exSyn200_real2C` + L94 `Sy_btEx`, `dp_btEx` for the repaired instance) -/
theorem exSyn_real2 (r : ℕ) : ExSyn 200 (Ereal2 r) (gEreal2 r) (btReal2 r) := by
  have hR := dummyR r
  have hI := ECDLP.L95.instSy_real2 (n := r) (B := 13) (by norm_num) hR
  have hP : ECDLP.L91.Sy (rPhi2 r 3 0 0 0 0 [] hR).phiE := ECDLP.L91.Sy_phiEx r
  have hb : ECDLP.L91.Sy (btReal2 r) := ECDLP.L94.Sy_btEx (rInst2 r 3 0 0 0 0 [] hR) (rPhi2 r 3 0 0 0 0 [] hR) hI hP (by norm_num)
  have hdb : Ex.dp (btReal2 r) ≤ 40 :=
    ECDLP.L94.dp_btEx (rInst2 r 3 0 0 0 0 [] hR) (rPhi2 r 3 0 0 0 0 [] hR) 20
      (by show Ex.dp (ECDLP.L95.AEx2 16) ≤ 21; have := ECDLP.L95.dp_AEx2 16; omega)
      (by show Ex.dp (ECDLP.L95.hEx2 16) ≤ 21; have := ECDLP.L95.dp_hEx2 16; omega)
      (by show Ex.dp (ECDLP.L95.pbEx2 16) ≤ 21; have := ECDLP.L95.dp_pbEx2 16; omega)
      (by simp [rInst2, ECDLP.L95.instEx2, Ex.dp]) (by simp [rInst2, ECDLP.L95.instEx2, Ex.dp])
      (by show Ex.dp (ECDLP.L83.ncEx r 16) ≤ 21; rw [ECDLP.L83.dp_ncEx])
      (by show Ex.dp (ECDLP.L95.MEx2 16) ≤ 21; have := ECDLP.L95.dp_MEx2 16; omega)
      (by show Ex.dp (ECDLP.L95.bEx2 16) ≤ 21; have := ECDLP.L95.dp_bEx2 16; omega)
      (by show Ex.dp (ECDLP.L83.phiEx r (16 + 22) (16 + 23)) ≤ 21; rw [ECDLP.L83.dp_phiEx])
  exact ECDLP.L95.exSyn200_real2C (n := r) (B := 13) (by norm_num) hR (by norm_num) (m := 2) (by norm_num)
    (okR r 3 0 0 0 0 []) (rKinds2 r 3 0 0 0 0 [] 2 hR) rfl rfl rfl (rSrc2 r 3 0 0 0 0 [] 2 (by norm_num) hR (by norm_num)) rfl
    (btReal2 r) hb hdb

/-- **`EdgeCore 200` for the real clamped network of the repaired instance** from the two remaining hypotheses. -/
def edgeCore200_real2 (r : ℕ) (hb : FrameBnd r (Ereal2 r) (gEreal2 r) (btReal2 r))
    (Hj : OffFrame r (Ereal2 r) (gEreal2 r) (btReal2 r)) : EdgeCore 200 r (Ereal2 r) (gEreal2 r) (btReal2 r) :=
  edgeCore200_real (exSyn_real2 r) (noRdAll_real2 r) (frameRep_real2 r) (hbtE_real2 r) (wtBnd_real r) hb Hj

/-- **Capstone**: L35's `subexponentialRate (r+1)` for `r >= 1`, from `FrameBnd` and `OffFrame` only. -/
theorem subexp_real2 (r : ℕ) (hr1 : 1 ≤ r) (hb : FrameBnd r (Ereal2 r) (gEreal2 r) (btReal2 r))
    (Hj : OffFrame r (Ereal2 r) (gEreal2 r) (btReal2 r)) : (ECDLP.SubexponentialRateStmt (r + 1)) :=
  ECDLP.L92.subexponentialRate_L92H r (edgeCore200_real2 r hb Hj)
    (ECDLP.L93.edgeNetValue_of_core r hr1 (edgeCore200_real2 r hb Hj) (realRep_real2 r))

end ECDLP.L96
end
