import ECDLP.L64_Code

/-!
# L64 / PEx: expressions for a `PForced` network from gate-level expressions

The OBLIGATIONS (`PEx`) are the gate-specific expressions: node count, free/message counts of a node, message
width, the parent relation, the code of the message a node sends to a child, and the weight.  From them
`nrep_pforced` builds the five network expressions (size, weight, width, left/right factor) and proves the
`NRep` of `(P.toGNet).toNet e` with the coding `pfCoding`.  Scratch variables: `u+4 .. u+9`
(`u..u+3` are the argument variables `a b z q`).
-/
noncomputable section
namespace ECDLP.L64
open Factoring.Aux Finset Ex ECDLP.L56

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (P : PForced (ZMod m) ι)
  (E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))) (EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i)))
  (e : ι ≃ Fin g) [hF : ∀ i, Nonempty (P.Free i)] (u : ℕ)

/-- The gate-level obligations: expressions (scratch slots `u+4` node, `u+5` parent, `u+6` child, `u+7` code)
with their meaning. -/
structure PEx where
  gE : Ex
  nfE : Ex
  nmE : Ex
  wE : Ex
  parE : Ex
  outE : Ex
  wtE : Ex
  hg : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A gE = g
  hnf : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k →
    Ex.eval σ A nfE = Fintype.card (P.Free (e.symm k))
  hnm : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k →
    Ex.eval σ A nmE = Fintype.card (P.Msg (e.symm k))
  hw : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Ex.eval σ A wE = P.w (e.symm k)
  hpar : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ p c : Fin g, σ (u + 5) = p → σ (u + 6) = c →
    Ex.eval σ A parE = if e.symm p ∈ P.pa (e.symm c) then 1 else 0
  hout : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, ∀ z : P.S (e.symm a), e.symm a ∈ P.pa (e.symm b) →
    σ (u + 5) = a → σ (u + 6) = b → σ (u + 7) = (pfCoding P E EF e).e a z →
    Ex.eval σ A outE = (E (e.symm a) (P.out (e.symm a) z (e.symm b)) : ℕ)
  hwt : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ (a : Fin g) (z : P.S (e.symm a)), σ (u + 4) = a → σ (u + 7) = (pfCoding P E EF e).e a z →
    Ex.eval σ A wtE = if P.W (e.symm a) z = 1 then 1 else 0

variable {P E EF e u}
variable (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- `P` at (parent slot, child slot) -/
def par2 (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) (p c : ℕ) : Ex :=
  .lett (u + 5) (.var p) (.lett (u + 6) (.var c) X.parE)
/-- a unary node function at slot `t` -/
def un1 (_X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) (t : ℕ) (body : Ex) : Ex := .lett (u + 4) (.var t) body
/-- radix of position `u+8` in node `fr` -/
def nAE (fr : ℕ) : Ex :=
  .ifLt (.lit 0) (par2 X (u + 8) fr) (un1 X (u + 8) X.nmE) (.lit 1)
/-- `pp (nA fr)` up to the node in slot `tt` -/
def ppE (fr tt : ℕ) : Ex := nprod (u + 8) (.var tt) (nAE X fr)
/-- the digit of the setting code of `fr` at the node `tt` -/
def digE (fr tt : ℕ) : Ex :=
  .mod (.div (.div (.var (u + 2)) (un1 X fr X.nfE)) (ppE X fr tt)) (un1 X tt X.nmE)
/-- the message from the node in slot `fr` tt the node in slot `tt` (code of `fr` in `u+2`) -/
def mMsg (fr tt : ℕ) : Ex :=
  .ifLt (.lit 0) (par2 X tt fr) (.add (digE X fr tt) (.lit 1))
    (.ifLt (.lit 0) (par2 X fr tt)
      (.add (.lett (u + 5) (.var fr) (.lett (u + 6) (.var tt) (.lett (u + 7) (.var (u + 2)) X.outE))) (.lit 1))
      (.lit 0))
/-- size -/
def szEx : Ex := .mul (nprod (u + 8) X.gE (nAE X u)) (un1 X u X.nfE)
/-- weight -/
def WEx : Ex := .lett (u + 4) (.var u) (.lett (u + 7) (.var (u + 2)) X.wtE)
/-- width -/
def cEx : Ex :=
  .ifLt (.lit 0) (par2 X (u + 1) u) (.add (un1 X (u + 1) X.wE) (.lit 1))
    (.ifLt (.lit 0) (par2 X u (u + 1)) (.add (un1 X u X.wE) (.lit 1)) (.lit 0))

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem eval_par2 {p c : ℕ} (hc : c ≠ u + 5) {pk ck : Fin g} (hp : σ p = pk) (hcv : σ c = ck) :
    Ex.eval σ A (par2 X p c) = if e.symm pk ∈ P.pa (e.symm ck) then 1 else 0 := by
  simp only [par2, Ex.eval]
  refine X.hpar σ₀ hC _ ((hσ.upd (by omega) _).upd (by omega) _) pk ck ?_ ?_
  · simp [Function.update_apply, hp]
  · simp [Function.update_apply, hc, hcv]

theorem eval_nf {t : ℕ} {k : Fin g} (hk : σ t = k) :
    Ex.eval σ A (un1 X t X.nfE) = Fintype.card (P.Free (e.symm k)) := by
  simp only [un1, Ex.eval]
  exact X.hnf σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk])

theorem eval_nm {t : ℕ} {k : Fin g} (hk : σ t = k) :
    Ex.eval σ A (un1 X t X.nmE) = Fintype.card (P.Msg (e.symm k)) := by
  simp only [un1, Ex.eval]
  exact X.hnm σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk])

theorem eval_w {t : ℕ} {k : Fin g} (hk : σ t = k) :
    Ex.eval σ A (un1 X t X.wE) = P.w (e.symm k) := by
  simp only [un1, Ex.eval]
  exact X.hw σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk])

theorem eval_nAE {fr : ℕ} (hfr : fr < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ (u + 8) = k) :
    Ex.eval σ A (nAE X fr) = nA P e a k := by
  simp only [nAE, Ex.eval]
  rw [eval_par2 X hu hC hσ (p := u + 8) (c := fr) (by omega) hk ha]
  by_cases h : e.symm k ∈ P.pa (e.symm a)
  · simp [Ex.eval, h, eval_nm X hu hC hσ hk, nA_par P e h]
  · simp [Ex.eval, h, nA_npar P e h]

theorem eval_ppE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) : Ex.eval σ A (ppE X fr tt) = pp (nA P e a) k := by
  simp only [ppE, eval_nprod, Ex.eval, hk]
  refine pp_congr fun i hi => ?_
  have hig : i < g := lt_trans hi k.2
  have := eval_nAE X hu hC (hσ.upd (show B ≤ u + 8 by omega) i) hfr (a := a) (k := ⟨i, hig⟩)
    (by simp [Function.update_apply, ha]; omega) (by simp)
  rw [this]

theorem eval_digE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) (hpk : e.symm k ∈ P.pa (e.symm a)) (z : P.S (e.symm a))
    (hz : σ (u + 2) = (pfCoding P E EF e).e a z) :
    Ex.eval σ A (digE X fr tt) = (E (e.symm k) (z.2 ⟨e.symm k, hpk⟩) : ℕ) := by
  have hd := code_digit P E EF e a z.1 z.2 k hpk
  unfold dgx at hd
  rw [nA_par P e hpk] at hd
  simp only [digE, Ex.eval, eval_nf X hu hC hσ ha, eval_ppE X hu hC hσ hfr htt ha hk, eval_nm X hu hC hσ hk, hz]
  exact hd

theorem eval_mMsg {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a b : Fin g} (ha : σ fr = a)
    (hb : σ tt = b) (z : P.S (e.symm a)) (hz : σ (u + 2) = (pfCoding P E EF e).e a z) :
    Ex.eval σ A (mMsg X fr tt) = (toGNetE P E).v (e.symm a) (e.symm b) z := by
  simp only [mMsg, Ex.eval]
  rw [eval_par2 X hu hC hσ (p := tt) (c := fr) (by omega) hb ha]
  by_cases h1 : e.symm b ∈ P.pa (e.symm a)
  · have hv : (toGNetE P E).v (e.symm a) (e.symm b) z = (E (e.symm b) (z.2 ⟨e.symm b, h1⟩) : ℕ) + 1 := by
      simp [toGNetE, h1]
    rw [hv, if_pos h1]
    simp only [if_true, Nat.zero_lt_one, Ex.eval]
    rw [eval_digE X hu hC hσ hfr htt ha hb h1 z hz]
  · rw [if_neg h1]
    simp only [lt_irrefl, if_false]
    rw [eval_par2 X hu hC hσ (p := fr) (c := tt) (by omega) ha hb]
    by_cases h2 : e.symm a ∈ P.pa (e.symm b)
    · have hv : (toGNetE P E).v (e.symm a) (e.symm b) z = (E (e.symm a) (P.out (e.symm a) z (e.symm b)) : ℕ) + 1 := by
        simp [toGNetE, h1, h2]
      rw [hv, if_pos h2]
      simp only [if_true, Nat.zero_lt_one, Ex.eval]
      congr 1
      refine X.hout σ₀ hC _ (((hσ.upd (show B ≤ u + 5 by omega) _).upd (show B ≤ u + 6 by omega) _).upd
        (show B ≤ u + 7 by omega) _) a b z h2 ?_ ?_ ?_
      · simp [Function.update_apply, ha]
      · simp [Function.update_apply, hb]; omega
      · simp [Function.update_apply, hz]
    · have hv : (toGNetE P E).v (e.symm a) (e.symm b) z = 0 := by
        simp [toGNetE, h1, h2]
      rw [hv, if_neg h2]
      simp

theorem eval_szEx {a : Fin g} (ha : σ u = a) : Ex.eval σ A (szEx X) = sN P e a := by
  simp only [szEx, Ex.eval, eval_nprod, X.hg σ₀ hC σ hσ, eval_nf X hu hC hσ ha]
  have : pp (fun i => Ex.eval (Function.update σ (u + 8) i) A (nAE X u)) g = pp (nA P e a) g := by
    refine pp_congr fun i hi => ?_
    exact eval_nAE X hu hC (hσ.upd (show B ≤ u + 8 by omega) i) (by omega) (a := a) (k := ⟨i, hi⟩)
      (by simp [ha]) (by simp)
  rw [this]
  simp [sN, nfN, a.2]

theorem eval_WEx {a : Fin g} (ha : σ u = a) (z : P.S (e.symm a)) (hz : σ (u + 2) = (pfCoding P E EF e).e a z) :
    Ex.eval σ A (WEx X) = if P.W (e.symm a) z = 1 then 1 else 0 := by
  simp only [WEx, Ex.eval]
  exact X.hwt σ₀ hC _ ((hσ.upd (show B ≤ u + 4 by omega) _).upd (show B ≤ u + 7 by omega) _) a z
    (by simp [Function.update_apply, ha]) (by simp [Function.update_apply, hz])

theorem eval_cEx {a b : Fin g} (ha : σ u = a) (hb : σ (u + 1) = b) :
    Ex.eval σ A (cEx X) = (toGNetE P E).c (e.symm a) (e.symm b) := by
  simp only [cEx, Ex.eval]
  rw [eval_par2 X hu hC hσ (p := u + 1) (c := u) (by omega) hb ha]
  by_cases h1 : e.symm b ∈ P.pa (e.symm a)
  · have hv : (toGNetE P E).c (e.symm a) (e.symm b) = P.w (e.symm b) + 1 := by simp [toGNetE, h1]
    rw [hv, if_pos h1]
    simp [eval_w X hu hC hσ hb]
  · rw [if_neg h1]
    simp only [lt_irrefl, if_false]
    rw [eval_par2 X hu hC hσ (p := u) (c := u + 1) (by omega) ha hb]
    by_cases h2 : e.symm a ∈ P.pa (e.symm b)
    · have hv : (toGNetE P E).c (e.symm a) (e.symm b) = P.w (e.symm a) + 1 := by simp [toGNetE, h1, h2]
      rw [hv, if_pos h2]
      simp [eval_w X hu hC hσ ha]
    · have hv : (toGNetE P E).c (e.symm a) (e.symm b) = 0 := by simp [toGNetE, h1, h2]
      rw [hv, if_neg h2]
      simp

end

/-- **`NRep` of the network of a forced gate network from the gate-level expressions.** -/
theorem nrep_pforced {m B g : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PForced (ZMod m) ι) (E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i)))
    (EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))) (e : ι ≃ Fin g) [hF : ∀ i, Nonempty (P.Free i)] (u vm : ℕ)
    (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) (hu : B ≤ u) (hC : Ctx σ₀) (hm : σ₀ vm = m) (hm1 : 1 < m)
    (hP01 : ∀ i z, P.W i z = 0 ∨ P.W i z = 1) :
    NRep m vm B σ₀ A (NVars.std u) ⟨szEx X, WEx X, cEx X, msgTest (mMsg X u (u + 1)) (cEx X) (u + 3) (u + 9),
      msgTest (mMsg X (u + 1) u) (cEx X) (u + 3) (u + 9)⟩ ((toGNetE P E).toNet e) (pfCoding P E EF e) :=
  nrep_gnet (NVars.std u) (u + 9) (toGNetE P E) e (pfCoding P E EF e) hm hm1 hP01 (szEx X) (WEx X) (cEx X)
    (mMsg X u (u + 1)) (mMsg X (u + 1) u)
    (fun σ hσ a ha => eval_szEx X hu hC hσ ha)
    (fun σ hσ a z ha hz => eval_WEx X hu hC hσ ha z hz)
    (fun σ hσ a b _ ha hb => eval_cEx X hu hC hσ ha hb)
    (fun σ hσ a b _ z ha hb hz => eval_mMsg X hu hC hσ (fr := u) (tt := u + 1) (by omega) (by omega) ha hb z hz)
    (fun σ hσ a b _ z ha hb hz => eval_mMsg X hu hC hσ (fr := u + 1) (tt := u) (by omega) (by omega) hb ha z hz)

end ECDLP.L64
