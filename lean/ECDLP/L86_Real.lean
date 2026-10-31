import ECDLP.L86_Budget

/-!
# L86 / Real: the REAL dispatch (L73's `outEx`, `wtEx`, `pexEdge`; car via `digE`) has all five `E` fields of depth `<= 160`

L85's `ExSyn 200` asks `Ex.dp E.f + 40 <= 200` for `f` in `sz, W, c, l, r`.  Here `E` = the `NEx` of L73's `edge_nrep` (unchanged: `outEx`, `wtEx`, `carOutX`
with `digE`, L73's linear dispatch).  Hypotheses are depth bounds on the instance data only: the eight `InstEx` expressions `<= dI`, the fa index oracle `phiE`,
the source weight `srcE`, and the three kind expressions `Kd.fa.outE`, `Kd.mid.outE`, `Kd.ib.outE`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

theorem dp_carJ_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) : Ex.dp (carJ I) ≤ max (dI + 16) 21 := by
  have h := dp_decodeE_le I (u + 5) (.var (u + 16)) h1 h2 h3 h4 h5 h6 h7 h8
  have e : Ex.dp (Ex.var (u + 16)) = 1 := rfl
  rw [e] at h
  unfold carJ
  omega

theorem dp_carPIB_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) : Ex.dp (carPIB I) ≤ max (dI + 16) 21 := by
  have h := dp_decodeE_le I (u + 5)
    (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.add (.var (u + 12)) (.mod (.var (u + 16)) (.var (u + 12)))))
    h1 h2 h3 h4 h5 h6 h7 h8
  have e : Ex.dp (Ex.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.add (.var (u + 12)) (.mod (.var (u + 16)) (.var (u + 12))))) = 4 := by
    simp [Ex.dp]
  rw [e] at h
  unfold carPIB
  omega

theorem dp_carPC : Ex.dp (carPC (u := u)) = 2 := by simp [carPC, Ex.dp]

theorem dp_carOutE_eq : Ex.dp (carOutE (u + 10) (u + 11) (u + 92) (u + 93) (u + 94)) = 11 := by
  simp [carOutE, tE, Ex.dp]

theorem dp_carWE_eq : Ex.dp (carWE (u + 10) (u + 11) (u + 92) (u + 28) (u + 93) (u + 94)) = 13 := by
  simp [carWE, tE, Ex.dp]

theorem dp_carOutX_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (carOutX I X) ≤ max (max (dI + 16) 21) (Ex.dp (digE X u (u + 1)) + 1) + 5 := by
  have hj := dp_carJ_le I h1 h2 h3 h4 h5 h6 h7 h8
  have hp := dp_carPIB_le I h1 h2 h3 h4 h5 h6 h7 h8
  have hc := dp_carPC (u := u)
  have ho := dp_carOutE_eq (u := u)
  have hd := dpT_pos (digE X u (u + 1))
  unfold carOutX carOutL' carIn'
  simp only [Ex.dp]
  rw [hc, ho]
  omega

theorem dp_carWX_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (carWX I X) ≤ max (max (dI + 16) 21) (Ex.dp (digE X u (u + 1)) + 1) + 6 := by
  have hj := dp_carJ_le I h1 h2 h3 h4 h5 h6 h7 h8
  have hp := dp_carPIB_le I h1 h2 h3 h4 h5 h6 h7 h8
  have hc := dp_carPC (u := u)
  have ho := dp_carWE_eq (u := u)
  have hd := dpT_pos (digE X u (u + 1))
  unfold carWX carWL' carIn'
  simp only [Ex.dp]
  rw [hc, ho]
  omega

theorem dp_outEx_real (Kd : Kinds (w := w) (m := m) X) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (outEx I X Kd) ≤ max (max (dI + 16) 25) (max (max (Ex.dp Kd.fa.outE + 3) (Ex.dp Kd.mid.outE + 4))
      (max (Ex.dp Kd.ib.outE + 5) (Ex.dp (carOutX I X) + 5)) + 15 + 1) := by
  have h := dp_decodeE_le I (u + 5) (outBody I X Kd) h1 h2 h3 h4 h5 h6 h7 h8
  have := dpT_pos Kd.fa.outE
  have := dpT_pos Kd.mid.outE
  have := dpT_pos Kd.ib.outE
  have := dpT_pos (carOutX I X)
  have e : outEx I X Kd = decodeE I (u + 5) (outBody I X Kd) := rfl
  rw [e]
  simp only [outBody, outChain, dp_dqE, Ex.dp] at h ⊢
  omega

theorem dp_wtEx_real (Sw : SrcWt (w := w) X) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (wtEx I X Sw) ≤ max (max (dI + 16) 25)
      (max (Ex.dp Sw.srcE + 1) (Ex.dp (carWX I X) + 3) + 15) := by
  have h := dp_decodeE_le I (u + 4) (wtChain I X Sw) h1 h2 h3 h4 h5 h6 h7 h8
  have := dpT_pos Sw.srcE
  have := dpT_pos (carWX I X)
  have e : wtEx I X Sw = decodeE I (u + 4) (wtChain I X Sw) := rfl
  rw [e]
  simp only [wtChain, Ex.dp] at h ⊢
  omega

end

end ECDLP.L86
end
