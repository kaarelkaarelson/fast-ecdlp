import ECDLP.L79_MidB
import ECDLP.L73_Asm
import ECDLP.L75_IbKindB

/-!
# L79 / Depth: exact nesting depths (`Ex.dp`) of the gate-kind expressions
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (midOutL midKindE kParams2 kParams pfaKE faKindE midIn midY faOutL faIn faUE)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

theorem dp_par2 (p c : ℕ) : Ex.dp (par2 X p c) = Ex.dp X.parE + 2 := by
  have := dpT_pos X.parE
  simp only [par2, Ex.dp]; omega

theorem dp_un1 (t : ℕ) (b : Ex) : Ex.dp (un1 X t b) = Ex.dp b + 1 := by
  have := dpT_pos b
  simp only [un1, Ex.dp]; omega

/-- **depth of the digit expression** -/
theorem dp_digE (fr tt : ℕ) :
    Ex.dp (digE X fr tt) = max (max (Ex.dp X.nfE + 4) (Ex.dp X.parE + 6)) (Ex.dp X.nmE + 5) := by
  have h1 := dpT_pos X.parE
  have h2 := dpT_pos X.nmE
  have h3 := dpT_pos X.nfE
  simp only [digE, ppE, nAE, nprod, dp_par2, dp_un1, Ex.dp]
  omega

theorem dp_pfaKE : Ex.dp (pfaKE (u := u)) = 6 := by
  simp only [pfaKE, Ex.dp]; omega

/-- depth of the guarded fa expression: `max 20 (Dd + 9) (dp phiE + 10)`, `Dd = dp digE` -/
theorem dp_faKindE (phiE : Ex) :
    Ex.dp (guardE u (faKindE (m := m) (φ := φ) (F := F) (ok := ok) L X phiE)) =
      max (max 20 (Ex.dp (digE X u (u + 1)) + 9)) (Ex.dp phiE + 10) := by
  have h1 := dpT_pos phiE
  simp only [guardE, faKindE, kParams, faOutL, faIn, faE, faUE, natE, mulE, pwE, sumE, nprod, Ex.dp]
  omega

section stages
open ECDLP.L68

theorem dp_faE_var (vq vA x1 v0 vr vk : ℕ) (u : Ex) :
    Ex.dp (faE vq vA x1 (.var v0) (.var vr) (.var vk) u) = max (Ex.dp u) 5 + 5 := by
  have := dpT_pos u
  simp only [faE, mulE, pwE, sumE, Ex.dp]; omega

theorem dp_hatE_var (vq vA x1 v0 vk : ℕ) (u : Ex) :
    Ex.dp (hatE vq vA x1 (.var v0) (.var vk) u) = max (Ex.dp u) 5 + 3 := by
  have := dpT_pos u
  simp only [hatE, mulE, pwE, sumE, Ex.dp]; omega

theorem dp_hatYE_var (vq vA x3 vI vS v0 vk : ℕ) (idx y : Ex) :
    Ex.dp (hatYE vq vA x3 vI vS (.var v0) (.var vk) idx y) = max (max (Ex.dp idx) (Ex.dp y + 1) + 1) 5 + 3 := by
  have := dpT_pos y
  have := dpT_pos idx
  simp only [hatYE, dp_hatE_var, Ex.dp]; omega

theorem dp_midE_var (vq vA x1 x2 x3 vI vS v0 vw vK vJ : ℕ) (nE epsE lE rE yE : Ex) :
    Ex.dp (midE vq vA x1 x2 x3 vI vS (.var v0) (.var vw) (.var vK) (.var vJ) nE epsE lE rE yE) =
      max (max (Ex.dp nE) (max (Ex.dp epsE) (max (max (max (Ex.dp lE) (Ex.dp yE + 1) + 1) 5 + 3)
        (max (max (Ex.dp rE) (Ex.dp yE + 1) + 1) 5 + 3) + 2) + 2) + 1) 5 + 5 := by
  have := dpT_pos yE
  have := dpT_pos nE
  have := dpT_pos epsE
  have := dpT_pos lE
  have := dpT_pos rE
  simp only [midE, dp_faE_var, sumE, mulE, dp_hatYE_var, Ex.dp]
  omega

end stages

theorem dp_midY (pfaE : Ex) : Ex.dp (midY X pfaE) = max (Ex.dp pfaE) (Ex.dp (digE X u (u + 1))) + 1 := by
  simp only [midY, Ex.dp]

/-- depth of the guarded mid expression -/
theorem dp_midKindE (nE epsE lE rE : Ex) :
    Ex.dp (guardE u (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE)) =
      max (max (Ex.dp nE) (max (Ex.dp epsE) (max (max (max (Ex.dp lE) (max 6 (Ex.dp (digE X u (u + 1))) + 1 + 1) + 1) 5 + 3)
        (max (max (Ex.dp rE) (max 6 (Ex.dp (digE X u (u + 1))) + 1 + 1) + 1) 5 + 3) + 2) + 2) + 1) 5 + 13 := by
  have h1 := dpT_pos nE
  have h2 := dpT_pos epsE
  have h3 := dpT_pos lE
  have h4 := dpT_pos rE
  have h5 := dpT_pos (digE X u (u + 1))
  simp only [guardE, midKindE, kParams2, kParams, midOutL, midIn, dp_midY, dp_midE_var, dp_pfaKE, Ex.dp]
  omega

/-! ### depth of the decode (L73) -/
section decode
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)

theorem dp_lett_succ {x : ℕ} {e b : Ex} {n : ℕ} {d : ℕ} (h : d + n ≤ Ex.dp b) : d + (n + 1) ≤ Ex.dp (.lett x e b) := by
  simp only [Ex.dp]; omega

/-- the decode is a chain of 15 `lett`s around the body: depth at least `dp body + 15` -/
theorem dp_decodeE_ge (xs : ℕ) (body : Ex) : Ex.dp body + 15 ≤ Ex.dp (decodeE I xs body) := by
  unfold decodeE
  repeat refine dp_lett_succ ?_
  exact le_rfl

/-- the depth bound of the decode when all instance expressions have depth `<= dI` -/
theorem dp_decodeE_le (xs : ℕ) (body : Ex) {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (decodeE I xs body) ≤ max (max (dI + 16) 21) (Ex.dp body + 15) := by
  have := dpT_pos I.AE
  have := dpT_pos I.nIE
  have := dpT_pos I.ncE
  have := dpT_pos I.KE
  dp_tac [decodeE, kcodeE, djE, dsE, offE, blkLoop, nsum, nprod]

variable {φ : ∀ c, ιc c → ι} (Ph : PhiEx L φ B Ctx A u)

/-- the body of `parEx` (copied from L73_Disp1; `parEx_eq` is `rfl`) -/
def parBody {L : Lay ι ιc} {u : ℕ} (phiE : Ex) : Ex :=
  (.ifLt (.var (u + 21)) (.lit 1) (.lit 0)
    (.ifLt (.var (u + 21)) (.lit 2)
      (.lett (u + 22) (.var (u + 15)) (.lett (u + 23) (.var (u + 16))
        (ECDLP.L73.eqE (.var (u + 5)) (.add (.mul phiE (.var (u + 12))) (.var (u + 17))))))
      (.ifLt (.var (u + 21)) (.lit 3)
        (.ifLt (.var (u + 5)) (.var (u + 18)) (.lit 0)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 1) (.lit 0)))
        (.ifLt (.var (u + 21)) (.lit 4)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 0)
            (.ifLt (.var (u + 5)) (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.lit 1) (.lit 0)))
          (.ifLt (.lit 0)
            (ECDLP.L73.eqE (.var (u + 5)) (.add (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.mod (.var (u + 16)) (.var (u + 12)))))
            (.lit 1)
            (.ifLt (.lit 0) (.var (u + 16))
              (ECDLP.L73.eqE (.add (.var (u + 5)) (.lit 1)) (.add (.add (.add (.add (.var (u + 18))
                (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12))) (.var (u + 12))) (.var (u + 16))))
              (.lit 0)))))))

theorem parEx_eq (Ph : PhiEx L φ B Ctx A u) : parEx I φ Ph = decodeE I (u + 6) (parBody (L := L) (u := u) Ph.phiE) := rfl

theorem dp_parBody (Ph : PhiEx L φ B Ctx A u) :
    Ex.dp (parBody (L := L) (u := u) Ph.phiE) = max (Ex.dp Ph.phiE + 8) 14 := by
  have := dpT_pos Ph.phiE
  simp only [parBody, ECDLP.L73.eqE, Ex.dp]
  omega

theorem dp_parEx_ge : 29 ≤ Ex.dp (parEx I φ Ph) := by
  have h := dp_decodeE_ge I (u + 6) (parBody (L := L) (u := u) Ph.phiE)
  rw [dp_parBody] at h
  rw [parEx_eq]
  omega

theorem dp_parEx_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (parEx I φ Ph) ≤ max (max (dI + 16) (Ex.dp Ph.phiE + 23)) 29 := by
  have h := dp_decodeE_le I (u + 6) (parBody (L := L) (u := u) Ph.phiE) h1 h2 h3 h4 h5 h6 h7 h8
  rw [dp_parBody] at h
  rw [parEx_eq]
  omega

theorem dp_nfEx_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (nfEx I) ≤ max (dI + 16) 21 := by
  have h := dp_decodeE_le I (u + 4) (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10))) (.lit 1))
    h1 h2 h3 h4 h5 h6 h7 h8
  unfold nfEx
  simp only [nprod, Ex.dp] at h ⊢
  omega

theorem dp_nmEx_le {dI : ℕ} (h1 : Ex.dp I.AE ≤ dI) (h2 : Ex.dp I.hE ≤ dI)
    (h3 : Ex.dp I.pbE ≤ dI) (h4 : Ex.dp I.nIE ≤ dI) (h5 : Ex.dp I.KE ≤ dI) (h6 : Ex.dp I.ncE ≤ dI)
    (h7 : Ex.dp I.MeE ≤ dI) (h8 : Ex.dp I.bE ≤ dI) :
    Ex.dp (nmEx I) ≤ max (dI + 16) 21 := by
  have h := dp_decodeE_le I (u + 4) (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 11)) (.lit 1)) (.mul (.lit 8) (.var (u + 11))))) h1 h2 h3 h4 h5 h6 h7 h8
  unfold nmEx
  simp only [nprod, Ex.dp] at h ⊢
  omega

end decode

section outer
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- the digit expression over the real structural expressions (`pex0`) has depth at least `35`
(`dp parEx >= 29`, `dp digE = max (...) (dp parE + 6)`) -/
theorem dp_digE_pex0_ge (fr tt : ℕ) : 35 ≤ Ex.dp (digE (pex0 (F := F) (ok := ok) (m := m) I Ph hu) fr tt) := by
  rw [dp_digE]
  have := dp_parEx_ge I Ph
  show 35 ≤ max (max _ (Ex.dp (parEx I φ Ph) + 6)) _
  omega

/-- **NEGATIVE (budget).**  With the dispatch of L73 (`outEx`) and a mid kind of the form `midKindE`, the depth of the
message-code expression is at least `77`, above L72's `ExSyn` budget `dl, dr <= 60` (the expression `outEx` is a subexpression of
`E.l`, `E.r`). -/
theorem dp_outEx_ge_77 (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (nE epsE lE rE : Ex)
    (hmid : Kd.mid.outE = midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
      nE epsE lE rE) :
    77 ≤ Ex.dp (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) := by
  have h1 := dp_decodeE_ge I (u + 5) (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd)
  have h2 := dp_midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu) nE epsE lE rE
  have h3 := dp_digE_pex0_ge (F := F) (ok := ok) (m := m) I Ph hu u (u + 1)
  have h4 : Ex.dp (guardE u (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
      nE epsE lE rE)) = Ex.dp (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
      nE epsE lE rE) + 1 := by
    have := dpT_pos (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu) nE epsE lE rE)
    simp only [guardE, Ex.dp]; omega
  have h5 : Ex.dp (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) ≥ Ex.dp Kd.mid.outE + 4 := by
    simp only [outBody, outChain, Ex.dp]; omega
  rw [hmid] at h5
  have e : outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd = decodeE I (u + 5) (outBody I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd) := rfl
  rw [e]
  omega

end outer

/-- depth of the `ib` kind expression of L75 (`ibOutI`): `max (Dd + 9) 14` -/
theorem dp_ibOutI : Ex.dp (ECDLP.L75.ibOutI L X) = max (Ex.dp (digE X u (u + 1)) + 9) 14 := by
  have := dpT_pos (digE X u (u + 1))
  simp only [ECDLP.L75.ibOutI, ECDLP.L75.e0I, ECDLP.L75.tEI, ECDLP.L75.kEI, ECDLP.L75.pmidEI, ECDLP.L75.ibOutL2,
    ECDLP.L75.ibE2, ECDLP.L75.ibBody, mulE, hatE, sumE, pwE, Ex.dp]
  omega

/-- the car expression of L73 contains two `digE` under six binders: depth at least `Dd + 6` -/
theorem dp_carIn_ge (vj vc vr : ℕ) (jE pcE pibE body : Ex) :
    Ex.dp (digE X u (u + 1)) + 6 ≤ Ex.dp (carIn' X vj vc vr jE pcE pibE body) := by
  simp only [carIn', Ex.dp]
  omega


section msg
open ECDLP.L64 in
/-- **the factor expression `E.l` of L73's `edge_nrep` contains `outE` under 8 more levels** -/
theorem dp_msgTest_ge {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {P : ECDLP.L56.PForced (ZMod m) ι'} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
    {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e' : ι' ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u' : ℕ}
    (Xp : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e' u') (cE : Ex) :
    Ex.dp Xp.outE + 8 ≤ Ex.dp (msgTest (ECDLP.L64.mMsg Xp u' (u' + 1)) cE (u' + 3) (u' + 9)) := by
  have := dpT_pos cE
  simp only [msgTest, ifEq, ECDLP.L64.mMsg, ECDLP.L64.par2, pow2, Ex.dp]
  omega
end msg


section edgeL
open ECDLP.L64 in
/-- **NEGATIVE (budget, final form).**  The left factor expression of L73's `edge_nrep` (`msgTest (mMsg (pexEdge ..) u (u+1)) ..`)
has depth at least `85` when the mid kind has the form `midKindE`; L72's `ExSyn` asks `dp E.l <= 60`. -/
theorem dp_edge_l_ge_85 {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
    {N0 : NPar} {w : Fin K → ℕ}
    [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
    {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
    {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) (hm1 : 1 < m)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (nE epsE lE rE : Ex)
    (hmid : Kd.mid.outE = midKindE (m := m) (φ := φ) (F := F) (ok := ok) L (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
      nE epsE lE rE) :
    haveI := edge_free_nonempty (w := w) φ F ok m
    85 ≤ Ex.dp (msgTest (ECDLP.L64.mMsg (pexEdge I Ph hu hm1 Kd Sw) u (u + 1))
      (cEx (pexEdge I Ph hu hm1 Kd Sw)) (u + 3) (u + 9)) := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  show 85 ≤ _
  have h1 := dp_msgTest_ge (pexEdge I Ph hu hm1 Kd Sw) (cEx (pexEdge I Ph hu hm1 Kd Sw))
  have h2 := dp_outEx_ge_77 I Ph hu Kd nE epsE lE rE hmid
  have : (pexEdge I Ph hu hm1 Kd Sw).outE = outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Kd := rfl
  rw [this] at h1
  omega
end edgeL


end
end ECDLP.L79
end
