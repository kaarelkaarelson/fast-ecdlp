import ECDLP.L79_Asm
import ECDLP.L79_Phi
import ECDLP.L75_IbKindB
import ECDLP.L73_Asm
import ECDLP.L81_SrcSlot

/-!
# L84 / NoRd: syntactic read-set of expressions (`hcong`)

`NoRd a e`: the expression `e` contains no read `.rd a _` of the array `a`.  `eval_congr_arr`: then its value does not depend on
the array `a` of the table `A` (so for `a = 3`, the engine's table).  We prove `NoRd 3` for the dispatch expressions of L73
(given `NoRd 3` for the instance expressions) and for the kind expressions of L68, L74, L75, L79 (given it for the oracle arguments).
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L84
open Finset Factoring.Aux Ex

/-- no read of an array `b` with `P b` -/
def NoRd (a : ℕ → Prop) : Ex → Prop
  | .lit _ => True
  | .var _ => True
  | .rd b i => ¬ a b ∧ NoRd a i
  | .add e f => NoRd a e ∧ NoRd a f
  | .sub e f => NoRd a e ∧ NoRd a f
  | .mul e f => NoRd a e ∧ NoRd a f
  | .div e f => NoRd a e ∧ NoRd a f
  | .mod e f => NoRd a e ∧ NoRd a f
  | .ifLt e f u v => NoRd a e ∧ NoRd a f ∧ NoRd a u ∧ NoRd a v
  | .lett _ e b => NoRd a e ∧ NoRd a b
  | .sum _ n m b => NoRd a n ∧ NoRd a m ∧ NoRd a b
  | .prod _ n m b => NoRd a n ∧ NoRd a m ∧ NoRd a b
  | .blk _ e => NoRd a e
  | .iter _ _ n i b => NoRd a n ∧ NoRd a i ∧ NoRd a b

theorem eval_congr_arr {a : ℕ → Prop} {A A' : ℕ → ℕ → ℕ} (h : ∀ b, ¬ a b → A' b = A b) :
    ∀ (e : Ex), NoRd a e → ∀ σ : ℕ → ℕ, Ex.eval σ A' e = Ex.eval σ A e
  | .lit _, _, _ => rfl
  | .var _, _, _ => rfl
  | .rd b i, hv, σ => by
      simp only [Ex.eval]
      rw [h b hv.1, eval_congr_arr h i hv.2 σ]
  | .add e f, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2]
  | .sub e f, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2]
  | .mul e f, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2]
  | .div e f, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2]
  | .mod e f, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2]
  | .ifLt e f u v, hv, σ => by
      simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2.1, eval_congr_arr h u hv.2.2.1,
        eval_congr_arr h v hv.2.2.2]
  | .lett x e b, hv, σ => by
      simp only [Ex.eval, eval_congr_arr h e hv.1, eval_congr_arr h b hv.2]
  | .sum x n m b, hv, σ => by
      simp only [Ex.eval, eval_congr_arr h n hv.1, eval_congr_arr h m hv.2.1, fun j => eval_congr_arr h b hv.2.2 (Function.update σ x j)]
  | .prod x n m b, hv, σ => by
      simp only [Ex.eval, eval_congr_arr h n hv.1, eval_congr_arr h m hv.2.1, fun j => eval_congr_arr h b hv.2.2 (Function.update σ x j)]
  | .blk _ e, hv, σ => by simp only [Ex.eval, eval_congr_arr h e hv]
  | .iter x y n i b, hv, σ => by
      simp only [Ex.eval, eval_congr_arr h n hv.1, eval_congr_arr h i hv.2.1,
        fun j s => eval_congr_arr h b hv.2.2 (Function.update (Function.update σ x j) y s)]


/-- the value bounds (`Bdd`) do not depend on arrays that `e` does not read -/
theorem Bdd_congr_arr {a : ℕ → Prop} {A A' : ℕ → ℕ → ℕ} (h : ∀ b, ¬ a b → A' b = A b) {V : ℕ} :
    ∀ (e : Ex), NoRd a e → ∀ σ : ℕ → ℕ, (Bdd V σ A' e ↔ Bdd V σ A e)
  | .lit _, _, _ => Iff.rfl
  | .var _, _, _ => Iff.rfl
  | .rd b i, hv, σ => by
      simp only [Bdd, eval_congr_arr h i hv.2 σ, h b hv.1, Bdd_congr_arr h i hv.2 σ]
  | .add e f, hv, σ => by
      simp only [Bdd, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h f hv.2 σ]
  | .sub e f, hv, σ => by
      simp only [Bdd, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h f hv.2 σ]
  | .mul e f, hv, σ => by
      simp only [Bdd, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h f hv.2 σ]
  | .div e f, hv, σ => by
      simp only [Bdd, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h f hv.2 σ]
  | .mod e f, hv, σ => by
      simp only [Bdd, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h f hv.2 σ]
  | .ifLt e f u v, hv, σ => by
      simp only [Bdd, eval_congr_arr h e hv.1, eval_congr_arr h f hv.2.1, Bdd_congr_arr h e hv.1 σ,
        Bdd_congr_arr h f hv.2.1 σ, Bdd_congr_arr h u hv.2.2.1 σ, Bdd_congr_arr h v hv.2.2.2 σ]
  | .lett x e b, hv, σ => by
      simp only [Bdd, eval_congr_arr h e hv.1, Bdd_congr_arr h e hv.1 σ, Bdd_congr_arr h b hv.2 (Function.update σ x _)]
  | .sum x n m b, hv, σ => by
      simp only [Bdd, eval_congr_arr h n hv.1, eval_congr_arr h m hv.2.1, Bdd_congr_arr h n hv.1 σ,
        Bdd_congr_arr h m hv.2.1 σ, fun j => eval_congr_arr h b hv.2.2 (Function.update σ x j)]
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
        (forall_congr' fun j => imp_congr_right fun _ => Bdd_congr_arr h b hv.2.2 _) Iff.rfl))
  | .prod x n m b, hv, σ => by
      simp only [Bdd, eval_congr_arr h n hv.1, eval_congr_arr h m hv.2.1, Bdd_congr_arr h n hv.1 σ,
        Bdd_congr_arr h m hv.2.1 σ, fun j => eval_congr_arr h b hv.2.2 (Function.update σ x j)]
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
        (forall_congr' fun j => imp_congr_right fun _ => Bdd_congr_arr h b hv.2.2 _) Iff.rfl))
  | .blk _ e, hv, σ => by simp only [Bdd, Bdd_congr_arr h e hv σ]
  | .iter x y n i b, hv, σ => by
      simp only [Bdd, eval_congr_arr h n hv.1, eval_congr_arr h i hv.2.1, Bdd_congr_arr h n hv.1 σ,
        Bdd_congr_arr h i hv.2.1 σ]
      have hF : (fun j s => eval (Function.update (Function.update σ x j) y s) A' b) =
          (fun j s => eval (Function.update (Function.update σ x j) y s) A b) := by
        funext j s; exact eval_congr_arr h b hv.2.2 _
      rw [hF]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun j hj => (Bdd_congr_arr h b hv.2.2 _).1 (h3 j hj)⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun j hj => (Bdd_congr_arr h b hv.2.2 _).2 (h3 j hj)⟩

theorem NoRd_nsum {a : ℕ → Prop} {x : ℕ} {n b : Ex} (hn : NoRd a n) (hb : NoRd a b) : NoRd a (nsum x n b) := by
  simp [nsum, NoRd, hn, hb]
theorem NoRd_nprod {a : ℕ → Prop} {x : ℕ} {n b : Ex} (hn : NoRd a n) (hb : NoRd a b) : NoRd a (nprod x n b) := by
  simp [nprod, NoRd, hn, hb]

section dispatch
open ECDLP.L73 ECDLP.L68 ECDLP.L64 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

theorem NoRd_eqE73 {a : ℕ → Prop} {x y : Ex} (hx : NoRd a x) (hy : NoRd a y) : NoRd a (ECDLP.L73.eqE x y) := by
  simp [ECDLP.L73.eqE, NoRd, hx, hy]

variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ}

/-- the instance expressions do not read array `a` -/
structure InstNoRd (a : ℕ → Prop) (I : InstEx L N0 w B Ctx A u) : Prop where
  nI : NoRd a I.nIE
  K' : NoRd a I.KE
  A' : NoRd a I.AE
  h' : NoRd a I.hE
  pb : NoRd a I.pbE
  b' : NoRd a I.bE
  nc : NoRd a I.ncE
  Me : NoRd a I.MeE

variable {a : ℕ → Prop} {I : InstEx L N0 w B Ctx A u} (hI : InstNoRd a I)
include hI

theorem NoRd_blkLoop : NoRd a (blkLoop I) := by
  simp [blkLoop, NoRd, hI.nc]

theorem NoRd_offE {t : Ex} (ht : NoRd a t) : NoRd a (offE I t) :=
  NoRd_nsum ht (NoRd_blkLoop hI)

theorem NoRd_kcodeE (xs : ℕ) : NoRd a (kcodeE I xs) := by
  simp [kcodeE, NoRd, hI.nI]

theorem NoRd_djE (xs : ℕ) : NoRd a (djE I xs) := by
  simp [djE, NoRd, hI.nI]

theorem NoRd_dsE (xs : ℕ) : NoRd a (dsE I xs) := by
  simp [dsE, NoRd, hI.nI]

theorem NoRd_decodeE (xs : ℕ) {body : Ex} (hb : NoRd a body) : NoRd a (decodeE I xs body) := by
  simp only [decodeE, NoRd, hI.A', hI.h', hI.pb, hI.nI, hI.K', hI.Me, hI.nc, hI.b', hb, NoRd_kcodeE hI, NoRd_djE hI,
    NoRd_dsE hI, true_and, and_true]
  refine ⟨NoRd_nsum hI.K' ?_, NoRd_nprod trivial trivial, NoRd_offE hI trivial⟩
  simp only [NoRd, NoRd_offE hI (t := .add (.var (u + 91)) (.lit 1)) (by simp [NoRd])]
  simp [NoRd]


theorem NoRd_gEx : NoRd a (gEx I) := by
  simp only [gEx, NoRd, hI.A', hI.nI, NoRd_offE hI hI.K', true_and]

theorem NoRd_nfEx : NoRd a (nfEx I) :=
  NoRd_decodeE hI _ (by simp [NoRd, nprod])

theorem NoRd_nmEx : NoRd a (nmEx I) :=
  NoRd_decodeE hI _ (by simp [NoRd, nprod])

theorem NoRd_wEx : NoRd a (wEx I) :=
  NoRd_decodeE hI _ (by simp [NoRd])

variable {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  {Ph : PhiEx L φ B Ctx A u} (hP : NoRd a Ph.phiE)
include hP

theorem NoRd_parEx : NoRd a (parEx I φ Ph) := by
  refine NoRd_decodeE hI _ ?_
  simp [NoRd, hP, ECDLP.L73.eqE]

end dispatch

section kinds
open ECDLP.L73 ECDLP.L68 ECDLP.L64 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u) {a : ℕ → Prop}

/-- the node expressions `digE` uses do not read array `a` -/
structure XNoRd (a : ℕ → Prop) : Prop where
  nf : NoRd a X.nfE
  nm : NoRd a X.nmE
  par : NoRd a X.parE

variable {X}

theorem NoRd_digE (hX : XNoRd X a) (fr tt : ℕ) : NoRd a (ECDLP.L68.digE X fr tt) := by
  simp [ECDLP.L68.digE, ECDLP.L68.ppE, ECDLP.L68.nAE, ECDLP.L68.par2, ECDLP.L68.un1, nprod, NoRd, hX.nf, hX.nm, hX.par]

theorem NoRd_carIn' (hX : XNoRd X a) {vj vc vr : ℕ} {jE pcE pibE body : Ex} (hj : NoRd a jE) (hpc : NoRd a pcE)
    (hpib : NoRd a pibE) (hb : NoRd a body) : NoRd a (carIn' X vj vc vr jE pcE pibE body) := by
  simp [carIn', NoRd, hj, hpc, hpib, hb, NoRd_digE hX]

theorem NoRd_tE (vb vM vj vc vr : ℕ) : NoRd a (ECDLP.L68.tE vb vM vj vc vr) := by
  simp [ECDLP.L68.tE, NoRd]
theorem NoRd_carOutE (vb vM vj vc vr : ℕ) : NoRd a (ECDLP.L68.carOutE vb vM vj vc vr) := by
  simp [ECDLP.L68.carOutE, NoRd, NoRd_tE]
theorem NoRd_carWE (vb vM vj vA2 vc vr : ℕ) : NoRd a (ECDLP.L68.carWE vb vM vj vA2 vc vr) := by
  simp [ECDLP.L68.carWE, NoRd, NoRd_tE]

theorem NoRd_carOutL' (hX : XNoRd X a) (vb vM vj vc vr : ℕ) {jE pcE pibE : Ex} (hj : NoRd a jE) (hpc : NoRd a pcE)
    (hpib : NoRd a pibE) : NoRd a (carOutL' X vb vM vj vc vr jE pcE pibE) :=
  NoRd_carIn' hX hj hpc hpib (NoRd_carOutE _ _ _ _ _)

theorem NoRd_carWL' (hX : XNoRd X a) (vb vM vj vA2 vc vr : ℕ) {jE pcE pibE : Ex} (hj : NoRd a jE) (hpc : NoRd a pcE)
    (hpib : NoRd a pibE) : NoRd a (carWL' X vb vM vj vA2 vc vr jE pcE pibE) := by
  simp only [carWL', NoRd, true_and]
  exact NoRd_carIn' hX hj hpc hpib (NoRd_carWE _ _ _ _ _ _)

theorem NoRd_mulE {vq : ℕ} {x y : Ex} (hx : NoRd a x) (hy : NoRd a y) : NoRd a (mulE vq x y) := by
  simp [mulE, NoRd, hx, hy]
theorem NoRd_sumE {vq x : ℕ} {n b : Ex} (hn : NoRd a n) (hb : NoRd a b) : NoRd a (sumE vq x n b) := by
  simp [sumE, NoRd, hn, hb]
theorem NoRd_pwE {vq x : ℕ} {n : Ex} (hn : NoRd a n) : NoRd a (pwE vq x n) := by
  simp [pwE, NoRd, hn]
theorem NoRd_addE {vq : ℕ} {x y : Ex} (hx : NoRd a x) (hy : NoRd a y) : NoRd a (addE vq x y) := by
  simp [addE, NoRd, hx, hy]
theorem NoRd_natE {vq : ℕ} {x : Ex} (hx : NoRd a x) : NoRd a (natE vq x) := by
  simp [natE, NoRd, hx]


section fam
variable (L : Lay ι ιc) {X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u}

theorem NoRd_faKindE (hX : XNoRd X a) {phiE : Ex} (hphi : NoRd a phiE) :
    NoRd a (ECDLP.L74.faKindE (m := m) (φ := φ) (F := F) (ok := ok) L X phiE) := by
  simp [ECDLP.L74.faKindE, ECDLP.L74.kParams, ECDLP.L74.faOutL, ECDLP.L74.faIn, ECDLP.L68.faE, ECDLP.L74.faUE,
    mulE, pwE, sumE, natE, nprod, NoRd, hphi, NoRd_digE hX]

theorem NoRd_midKindE (hX : XNoRd X a) {nE epsE lE rE : Ex} (hn : NoRd a nE) (he : NoRd a epsE) (hl : NoRd a lE)
    (hr : NoRd a rE) :
    NoRd a (ECDLP.L74.midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE) := by
  simp [ECDLP.L74.midKindE, ECDLP.L74.kParams2, ECDLP.L74.kParams, ECDLP.L74.midOutL, ECDLP.L74.midIn,
    ECDLP.L74.midY, ECDLP.L68.midE, ECDLP.L68.faE, ECDLP.L68.hatYE, ECDLP.L68.hatE, ECDLP.L74.pfaKE,
    mulE, pwE, sumE, natE, nprod, NoRd, hn, he, hl, hr, NoRd_digE hX]

theorem NoRd_ibOutI (hX : XNoRd X a) :
    NoRd a (ECDLP.L75.ibOutI (m := m) (φ := φ) (F := F) (ok := ok) L X) := by
  simp [ECDLP.L75.ibOutI, ECDLP.L75.ibOutL2, ECDLP.L75.ibE2, ECDLP.L75.ibBody, ECDLP.L75.e0I, ECDLP.L75.tEI,
    ECDLP.L75.kEI, ECDLP.L75.pmidEI, ECDLP.L68.hatE, mulE, pwE, sumE, natE, nprod, NoRd, NoRd_digE hX]

theorem NoRd_guardE {E : Ex} (h : NoRd a E) : NoRd a (ECDLP.L79.guardE u E) := by
  simp [ECDLP.L79.guardE, NoRd, h]

end fam

section disp
variable {L : Lay ι ιc} {I : InstEx L N0 w B Ctx A u} {Ph : PhiEx L φ B Ctx A u} {hu : B ≤ u}
  (hI : InstNoRd a I) (hP : NoRd a Ph.phiE)

include hI hP in
theorem XNoRd_pex0 : XNoRd (pex0 (F := F) (ok := ok) (m := m) I Ph hu) a :=
  ⟨NoRd_nfEx hI, NoRd_nmEx hI, NoRd_parEx hI hP⟩

variable {X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u}
  (hX : XNoRd X a)
include hI

theorem NoRd_carJ : NoRd a (carJ I) := NoRd_decodeE hI _ (by simp [NoRd])
omit hI in
theorem NoRd_carPC : NoRd a (carPC (u := u)) := by simp [carPC, NoRd]
theorem NoRd_carPIB : NoRd a (carPIB I) := NoRd_decodeE hI _ (by simp [NoRd])

omit hI in
theorem NoRd_dqE : NoRd a (dqE (u := u)) := by simp [dqE, NoRd]

include hX in
theorem NoRd_carOutX : NoRd a (carOutX I X) :=
  NoRd_carOutL' hX _ _ _ _ _ (NoRd_carJ hI) NoRd_carPC (NoRd_carPIB hI)

include hX in
theorem NoRd_carWX : NoRd a (carWX I X) :=
  NoRd_carWL' hX _ _ _ _ _ _ (NoRd_carJ hI) NoRd_carPC (NoRd_carPIB hI)

include hX in
theorem NoRd_outEx (Kd : Kinds (w := w) (m := m) X) (h1 : NoRd a Kd.fa.outE) (h2 : NoRd a Kd.mid.outE)
    (h3 : NoRd a Kd.ib.outE) : NoRd a (outEx I X Kd) := by
  refine NoRd_decodeE hI _ ?_
  simp only [outBody, outChain, NoRd]
  simp [NoRd, NoRd_dqE, h1, h2, h3, NoRd_carOutX hI hX]

include hX in
theorem NoRd_wtEx (Sw : SrcWt (w := w) X) (hs : NoRd a Sw.srcE) : NoRd a (wtEx I X Sw) := by
  refine NoRd_decodeE hI _ ?_
  simp only [wtChain, NoRd]
  simp [NoRd, hs, NoRd_carWX hI hX]

end disp

end kinds

section src
/-- the arrays the engine may overwrite or that are scratch: array 3 and all arrays `>= 12` (the instance lives in `0..11`) -/
def Out (b : ℕ) : Prop := b = 3 ∨ 12 ≤ b
open ECDLP.L76 ECDLP.L81 ECDLP.L44 ECDLP.L51

theorem NoRd_valE_lay (t x y : ℕ) (ht : ¬ Out t) : NoRd Out (valE (.var 0) t x y) := by
  simp [valE, nbitW, bitRd, NoRd, ht]

theorem NoRd_cvBitE (c : Cst) (j : Ex) (hj : NoRd Out j) : NoRd Out (cvBitE lay72 c j) := by
  cases c <;> simp [cvBitE, nbit, nbitW, lay72, Out, bitRd, c0B, NoRd, hj]


theorem NoRd_bWE : NoRd Out bWE := by
  simp [bWE, NoRd_valE_lay, Out]

theorem NoRd_sgE (i : Ex) (hi : NoRd Out i) : NoRd Out (sgE lay72 i) := by
  simp [sgE, pidx, lay72, Out, NoRd, hi, NoRd_valE_lay]

theorem NoRd_xcDefE (i jj : Ex) (hi : NoRd Out i) (hj : NoRd Out jj) : NoRd Out (xcDefE lay72 i jj) := by
  simp [xcDefE, pfDef, pidx, qOf, lay72, Out, NoRd, hi, hj, NoRd_valE_lay]

theorem NoRd_xcBitE (i jj : Ex) (hi : NoRd Out i) (hj : NoRd Out jj) : NoRd Out (xcBitE lay72 i jj) := by
  simp [xcBitE, pfBit, pidx, qOf, lay72, Out, bitRd, NoRd, hi, hj, NoRd_valE_lay]

theorem NoRd_badE (u n : ℕ) : NoRd Out (badE u n) := by
  have hc : ∀ c jj nb, NoRd Out jj → NoRd Out nb → NoRd Out (cstIn c jj nb) := fun c jj nb hj hn => by
    simp [cstIn, NoRd, hj, hn, NoRd_bWE, NoRd_cvBitE c jj hj, ECDLP.L81.eqE]
  have h32 : NoRd Out (Ex.var (u + 32)) := trivial
  have hnb : NoRd Out ((Ex.lit 1).sub (Ex.var (u + 33))) := by simp [NoRd]
  have hq : NoRd Out ((Ex.var (u + 16)).sub (Ex.lit 11)) := by simp [NoRd]
  have hq' : NoRd Out ((Ex.var (u + 16)).sub (Ex.lit (12 + n))) := by simp [NoRd]
  simp [badE, cstDisp, hc _ _ _ h32 hnb, tgIn, xIn, ECDLP.L81.eqE, NoRd, NoRd_bWE, NoRd_sgE _ hq,
    NoRd_xcDefE _ _ hq' h32, NoRd_xcBitE _ _ hq' h32]

theorem NoRd_srcE (u n : ℕ) : NoRd Out (srcE u (badE u n)) := by
  simp [srcE, srcCell, pw2, NoRd, NoRd_badE]

end src

end ECDLP.L84
end
