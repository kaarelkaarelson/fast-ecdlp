import ECDLP.L64_PEx

/-!
# L68 / PEx0: the part of the gate-level obligations that does not mention the message / weight expressions

`digE` (the digit of a setting code) depends only on `nfE, nmE, parE`; so the `outE`/`wtE` expressions can use it
without circularity.  `PEx0` = `(gE, nfE, nmE, wE, parE)` with their meanings; `PEx0.toPEx` adds `outE`, `wtE`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L68
open Factoring.Aux Finset Ex ECDLP.L56 ECDLP.L64

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (P : PForced (ZMod m) ι)
  (E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))) (EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i)))
  (e : ι ≃ Fin g) [hF : ∀ i, Nonempty (P.Free i)] (u : ℕ)

structure PEx0 where
  gE : Ex
  nfE : Ex
  nmE : Ex
  wE : Ex
  parE : Ex
  hg : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A gE = g
  hnf : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k →
    Ex.eval σ A nfE = Fintype.card (P.Free (e.symm k))
  hnm : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k →
    Ex.eval σ A nmE = Fintype.card (P.Msg (e.symm k))
  hw : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Ex.eval σ A wE = P.w (e.symm k)
  hpar : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ p c : Fin g, σ (u + 5) = p → σ (u + 6) = c →
    Ex.eval σ A parE = if e.symm p ∈ P.pa (e.symm c) then 1 else 0

variable {P E EF e u}
variable (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u)

/-- `P` at (parent slot, child slot) -/
def par2 (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u) (p c : ℕ) : Ex :=
  .lett (u + 5) (.var p) (.lett (u + 6) (.var c) X.parE)
/-- a unary node function at slot `t` -/
def un1 (_X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u) (t : ℕ) (body : Ex) : Ex := .lett (u + 4) (.var t) body
/-- radix of position `u+8` in node `fr` -/
def nAE (fr : ℕ) : Ex :=
  .ifLt (.lit 0) (par2 X (u + 8) fr) (un1 X (u + 8) X.nmE) (.lit 1)
/-- `pp (nA fr)` up to the node in slot `tt` -/
def ppE (fr tt : ℕ) : Ex := nprod (u + 8) (.var tt) (nAE X fr)
/-- the digit of the setting code of `fr` at the node `tt` -/
def digE (fr tt : ℕ) : Ex :=
  .mod (.div (.div (.var (u + 2)) (un1 X fr X.nfE)) (ppE X fr tt)) (un1 X tt X.nmE)
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

end
end ECDLP.L68
end
