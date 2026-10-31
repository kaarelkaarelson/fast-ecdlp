import ECDLP.L85_B_Cbdd
import ECDLP.L85_B_Width

/-!
# L72 / Syn: literal-free copies of the top search and table, their variable bounds and the depth budget
(items 2 and 4), for ANY network expressions `E gE btE` meeting the syntactic conditions `ExSyn`

`cpM E gE btE g` (cluster map `clusM (lit g)`) has the literal-free copy `cpMv E gE btE` (`clusM (var 6)`).
`searchMv`, `tabMv`: the copies of `GroupEx.searchE (gsM K g) 13 14`, `GroupEx.tab (gsM K g)` with `K, g, 2g+1, K^g`
read from the variables `5, 6, 8, 9` (Rudich's `UniTopV` for a general network).
* `searchM_LS`, `tabM_LS`: the relation `LS (topOk K g)` (same value and cost when the literal variables hold their
  values, `LS.eval_cost`);
* `searchMv_vb`, `tabMv_vb`: every variable below `1000`;
* `searchM_dp`, `tabM_dp`: `Ex.dp <= 100` from the stated depths of `E`, `gE`, `btE` (`ExSyn`).
-/
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB

/-- the group step with the literal cluster map -/
def gsM (E : NEx) (gE btE : Ex) (K g : ℕ) : GS := ⟨26, 10, 15, 12, g, K, CoarsenEx.nex (cpM E gE btE g)⟩

def cpMv (E : NEx) (gE btE : Ex) : CP := ⟨16, 26, 10, E, gE, clusM (.var 6) gE btE⟩
def gsMv (E : NEx) (gE btE : Ex) : GSv := ⟨26, 10, 15, 12, 5, 6, 8, 9, CoarsenEx.nex (cpMv E gE btE)⟩
def searchMv (E : NEx) (gE btE : Ex) : Ex := GroupV.searchE (gsMv E gE btE) 13 14
def tabMv (E : NEx) (gE btE : Ex) : Ex := GroupV.tab (gsMv E gE btE)

/-- **Syntactic conditions on the network expressions**: binders `>= 10` (so that none is a literal variable), variables
below `1000`, and depths within the budget. -/
structure ExSyn (DB : ℕ) (E : NEx) (gE btE : Ex) : Prop where
  bsz : BGe 10 E.sz
  bW : BGe 10 E.W
  bc : BGe 10 E.c
  bl : BGe 10 E.l
  br : BGe 10 E.r
  bg : BGe 10 gE
  bb : BGe 10 btE
  vE : E.VB 990
  vg : VB 990 gE
  vb : VB 990 btE
  dsz : Ex.dp E.sz + 40 ≤ DB
  dW : Ex.dp E.W + 40 ≤ DB
  dc : Ex.dp E.c + 40 ≤ DB
  dl : Ex.dp E.l + 40 ≤ DB
  dr : Ex.dp E.r + 40 ≤ DB
  dg : Ex.dp gE ≤ 40
  db : Ex.dp btE ≤ 40
  /-- arrays are read only through the test `0 < A a i` (so cost bounds may assume cells `<= 1`) -/
  rdE : NEx.Rd E
  rdg : RdN false gE
  rdb : RdN false btE

variable {E : NEx} {gE btE : Ex}

theorem clusM_dp (gx : Ex) (hgx : Ex.dp gx ≤ 1) (hg : Ex.dp gE ≤ 40) (hb : Ex.dp btE ≤ 40) :
    Ex.dp (clusM gx gE btE) ≤ 50 := by
  simp only [clusM, accM, totM, nsum, Ex.dp]
  omega

theorem clusM_vb {t : ℕ} (ht : 990 ≤ t) (gx : Ex) (hgx : VB t gx) (hg : VB t gE) (hb : VB t btE) :
    VB t (clusM gx gE btE) := by
  simp only [clusM, accM, totM, nsum, VB, and_true, true_and, and_self, hgx, hg, hb]
  omega

theorem ExSyn.vE' (S : ExSyn DB E gE btE) : E.VB 1000 :=
  ⟨VB_mono (by omega) _ S.vE.1, VB_mono (by omega) _ S.vE.2.1, VB_mono (by omega) _ S.vE.2.2.1,
    VB_mono (by omega) _ S.vE.2.2.2.1, VB_mono (by omega) _ S.vE.2.2.2.2⟩

theorem cpM_nex_LS (S : ExSyn DB E gE btE) (K g : ℕ) :
    NLS (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) (CoarsenEx.nex (cpM E gE btE g))
      (CoarsenEx.nex (cpMv E gE btE)) := by
  have h6 : topOk K g 6 g := TopV.ok6
  have hnb : ∀ x, 10 ≤ x → ∀ k, ¬ topOk K g x k := fun x hx => topOk_nb hx
  have hnb2 : ∀ x, 10 ≤ x → (fun x => ∀ k, ¬ topOk K g x k) x := fun x hx => topOk_nb hx
  have rg : LSB (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) gE gE := LSB.refl_ge hnb2 _ S.bg
  have rb : LSB (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) btE btE := LSB.refl_ge hnb2 _ S.bb
  have hχ : LSB (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) (clusM (.lit g) gE btE) (clusM (.var 6) gE btE) := by
    simp only [clusM, accM, totM, nsum]
    repeat ls_step
  have hE : NLS (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) E E :=
    ⟨LSB.refl_ge hnb2 _ S.bsz, LSB.refl_ge hnb2 _ S.bW, LSB.refl_ge hnb2 _ S.bc, LSB.refl_ge hnb2 _ S.bl,
      LSB.refl_ge hnb2 _ S.br⟩
  exact coarsen_LS 16 26 10 hE rg hχ (fun x hx => topOk_nb (by omega)) (fun x hx => topOk_nb (by omega))

theorem searchM_LS (S : ExSyn DB E gE btE) (K g : ℕ) :
    LS (topOk K g) (GroupEx.searchE (gsM E gE btE K g) 13 14) (searchMv E gE btE) :=
  GroupV.searchE_LS (gsM E gE btE K g) (E' := CoarsenEx.nex (cpMv E gE btE)) (cpM_nex_LS S K g)
    TopV.ok5 TopV.ok6 TopV.ok8 TopV.ok9
    (fun x hx => topOk_nb (by simp only [gsM] at hx; omega)) (topOk_nb (by simp only [gsM]; omega))
    (topOk_nb (by omega)) (topOk_nb (by omega))

theorem tabM_LS (S : ExSyn DB E gE btE) (K g : ℕ) :
    LS (topOk K g) (GroupEx.tab (gsM E gE btE K g)) (tabMv E gE btE) :=
  GroupV.tab_LS (gsM E gE btE K g) (E' := CoarsenEx.nex (cpMv E gE btE)) (cpM_nex_LS S K g) TopV.ok5 TopV.ok6
    (fun x hx => topOk_nb (by simp only [gsM] at hx; omega))

theorem cpM_vb (S : ExSyn DB E gE btE) (g : ℕ) : (CoarsenEx.nex (cpM E gE btE g)).VB 1000 :=
  coarsen_vb (P := cpM E gE btE g) S.vE' (VB_mono (by omega) _ S.vg)
    (clusM_vb (t := 1000) (by omega) (.lit g) trivial (VB_mono (by omega) _ S.vg) (VB_mono (by omega) _ S.vb))
    (by norm_num [cpM]) (by norm_num [cpM]) (by norm_num [cpM])

theorem cpM_vb990 (S : ExSyn DB E gE btE) (g : ℕ) : (CoarsenEx.nex (cpM E gE btE g)).VB 990 :=
  coarsen_vb (P := cpM E gE btE g) S.vE S.vg (clusM_vb (t := 990) (by omega) (.lit g) trivial S.vg S.vb)
    (by norm_num [cpM]) (by norm_num [cpM]) (by norm_num [cpM])

theorem searchMv_vb (S : ExSyn DB E gE btE) : VB 1000 (searchMv E gE btE) :=
  LS.VB (searchM_LS S 0 0)
    (group_search_vb (S := gsM E gE btE 0 0) (t := 1000) (cpM_vb S 0) (by simp only [gsM]; omega)
      (by simp only [gsM]; omega) (by simp only [gsM]; omega) (by simp only [gsM]; omega) (vx := 13) (vs := 14)
      (by omega) (by omega))
    (fun _ _ h => by have := topOk_lt h; omega)

theorem tabMv_vb (S : ExSyn DB E gE btE) : VB 990 (tabMv E gE btE) :=
  LS.VB (tabM_LS S 0 0)
    (group_tab_vb (S := gsM E gE btE 0 0) (t := 990) (cpM_vb990 S 0) (by simp only [gsM]; omega)
      (by simp only [gsM]; omega) (by simp only [gsM]; omega) (by simp only [gsM]; omega))
    (fun _ _ h => by have := topOk_lt h; omega)

theorem cpM_rd (S : ExSyn DB E gE btE) (g : ℕ) : NEx.Rd (CoarsenEx.nex (cpM E gE btE g)) :=
  coarsen_rdn (P := cpM E gE btE g) S.rdE S.rdg (by
    simp only [cpM, clusM, accM, totM, nsum, RdN, and_true, S.rdg, S.rdb])

/-- **The depth budget** (`Ex.dp <= DB`) of the top table, from the depths in `ExSyn DB`. -/
theorem tabM_dp (S : ExSyn DB E gE btE) (K g : ℕ) : Ex.dp (GroupEx.tab (gsM E gE btE K g)) ≤ DB := by
  have hD : 100 ≤ DB := Fact.out
  have dχ := clusM_dp (.lit g) (by simp [Ex.dp]) S.dg S.db
  have h1 := dpT_coarsen_sz (P := cpM E gE btE g) (n := DB - 29) (by simp only [cpM]; have := S.dsz; omega)
    (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  have h2 := dpT_coarsen_W (P := cpM E gE btE g) (n := DB - 12) (by simp only [cpM]; have := S.dsz; omega)
    (by simp only [cpM]; have := S.dW; omega) (by simp only [cpM]; have := S.dc; omega)
    (by simp only [cpM]; have := S.dl; omega) (by simp only [cpM]; have := S.dr; omega)
    (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  have h3 := dpT_coarsen_c (P := cpM E gE btE g) (n := DB - 25) (by simp only [cpM]; have := S.dc; omega)
    (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  have h4 := dpT_coarsen_l (P := cpM E gE btE g) (n := DB - 22) (by simp only [cpM]; have := S.dsz; omega)
    (by simp only [cpM]; have := S.dc; omega) (by simp only [cpM]; have := S.dl; omega)
    (by simp only [cpM]; have := S.dr; omega) (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  have h5 := dpT_coarsen_r (P := cpM E gE btE g) (n := DB - 23) (by simp only [cpM]; have := S.dsz; omega)
    (by simp only [cpM]; have := S.dc; omega) (by simp only [cpM]; have := S.dl; omega)
    (by simp only [cpM]; have := S.dr; omega) (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  exact dpT_group_tab (S := gsM E gE btE K g) (n := DB) (by omega) (by simp only [gsM]; omega)
    (by simp only [gsM]; omega) (by simp only [gsM]; omega) (by simp only [gsM]; omega) (by simp only [gsM]; omega)

/-- the depth budget of the top search -/
theorem searchM_dp (S : ExSyn DB E gE btE) (K g : ℕ) (vx vs : ℕ) :
    Ex.dp (GroupEx.searchE (gsM E gE btE K g) vx vs) ≤ DB := by
  have hD : 100 ≤ DB := Fact.out
  have dχ := clusM_dp (.lit g) (by simp [Ex.dp]) S.dg S.db
  have h3 := dpT_coarsen_c (P := cpM E gE btE g) (n := DB - 25) (by simp only [cpM]; have := S.dc; omega)
    (by simp only [cpM]; have := S.dg; omega) (by simp only [cpM]; omega)
  exact dpT_group_search (S := gsM E gE btE K g) vx vs (by omega) (by simp only [gsM]; omega)

end ECDLP.L85B
