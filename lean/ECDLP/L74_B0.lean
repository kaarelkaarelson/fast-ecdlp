import ECDLP.L69_Bdd
import ECDLP.L68_PEx0

/-!
# L74 / B0: value bounds of the digit expression `digE` over `PEx0` (copy of L69's lemmas for `PEx`)

`PExB0 X V`: the part of L69's `PExB` that `digE` needs (node count, setting counts, `nfE`, `nmE`, `parE`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Factoring.Aux Finset Ex SB ECDLP.L56 ECDLP.L68 UCost ECDLP.L69
open ECDLP.L64 (sN nA nfN nA_pos nA_par nA_npar)

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : ECDLP.L56.PForced (ZMod m) ι} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u)

structure PExB0 (V : ℕ) : Prop where
  hV : 8 ≤ V
  hgV : g ≤ V
  hsN : ∀ a : ℕ, sN P e a ≤ V
  bnf : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nfE
  bnm : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nmE
  bpar : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ p c : Fin g, σ (u + 5) = p → σ (u + 6) = c → Bdd V σ A X.parE

variable {V : ℕ} (H : PExB0 X V) {σ : ℕ → ℕ}
variable (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

theorem slotV {t : ℕ} {k : Fin g} (hk : σ t = k) : σ t ≤ V := by rw [hk]; exact le_trans k.2.le H.hgV

theorem bdd_par2 {p c : ℕ} (hc : c ≠ u + 5) {pk ck : Fin g} (hp : σ p = pk) (hcv : σ c = ck) :
    Bdd V σ A (par2 X p c) := by
  have hcv' : Function.update σ (u + 5) (σ p) c = ck := by rw [Function.update_of_ne hc]; exact hcv
  refine ⟨slotV X H hu hC hσ hp, ?_, ?_⟩
  · show Function.update σ (u + 5) (σ p) c ≤ V
    rw [hcv']; exact le_trans ck.2.le H.hgV
  · exact H.bpar σ₀ hC _ ((hσ.upd (by omega) _).upd (by omega) _) pk ck (by simp [Ex.eval, hp])
      (by simp [Ex.eval, hcv'])

theorem bdd_un1 {t : ℕ} {k : Fin g} (hk : σ t = k) {body : Ex}
    (hb : Bdd V (Function.update σ (u + 4) (σ t)) A body) : Bdd V σ A (un1 X t body) :=
  ⟨slotV X H hu hC hσ hk, hb⟩

theorem bdd_nf {t : ℕ} {k : Fin g} (hk : σ t = k) : Bdd V σ A (un1 X t X.nfE) :=
  bdd_un1 X H hu hC hσ hk (H.bnf σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk]))

theorem bdd_nm {t : ℕ} {k : Fin g} (hk : σ t = k) : Bdd V σ A (un1 X t X.nmE) :=
  bdd_un1 X H hu hC hσ hk (H.bnm σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk]))

theorem bdd_nAE {fr : ℕ} (hfr : fr < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ (u + 8) = k) :
    Bdd V σ A (nAE X fr) :=
  B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := u + 8) (c := fr) (by omega) hk ha)
    (fun _ => bdd_nm X H hu hC hσ (t := u + 8) hk) (fun _ => B_lit (by have := H.hV; omega))

theorem pp_nA_le {fr : ℕ} (hfr : fr < u + 4) {a : Fin g} (ha : σ fr = a) {j : ℕ} (hj : j ≤ g) :
    pp (fun i => eval (Function.update σ (u + 8) i) A (nAE X fr)) j ≤ V := by
  have h1 : pp (fun i => eval (Function.update σ (u + 8) i) A (nAE X fr)) j = pp (nA P e a) j := by
    refine pp_congr fun i hi => ?_
    have hig : i < g := lt_of_lt_of_le hi hj
    exact eval_nAE X hu hC (hσ.upd (show B ≤ u + 8 by omega) i) hfr (a := a) (k := ⟨i, hig⟩)
      (by simp [Function.update_apply, ha]; omega) (by simp)
  rw [h1]
  exact le_trans (pp_mono_le (fun i => nA_pos P e a i) hj) (le_trans (pp_le_sN P e a) (by
    have := H.hsN a.1; simpa using this))

theorem bdd_ppE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k) :
    Bdd V σ A (ppE X fr tt) := by
  refine B_nprodV (B_var (slotV X H hu hC hσ hk)) (fun j hj => ?_) (fun j hj => ?_)
  · have hjk : j < g := lt_trans (by simpa [Ex.eval, hk] using hj) k.2
    exact bdd_nAE X H hu (hC) (hσ.upd (show B ≤ u + 8 by omega) j) hfr (a := a) (k := ⟨j, hjk⟩)
      (by simp [Function.update_apply, ha]; omega) (by simp)
  · have : j ≤ k := by simpa [Ex.eval, hk] using hj
    exact pp_nA_le X H hu hC hσ hfr ha (le_trans this k.2.le)

theorem bdd_digE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) (hz : σ (u + 2) ≤ V) : Bdd V σ A (digE X fr tt) :=
  B_mod (B_div (B_div (B_var hz) (bdd_nf X H hu hC hσ ha)) (bdd_ppE X H hu hC hσ hfr htt ha hk))
    (bdd_nm X H hu hC hσ hk)

theorem digE_lt_nm {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) : eval σ A (digE X fr tt) < Fintype.card (P.Msg (e.symm k)) := by
  simp only [digE, Ex.eval]
  rw [eval_nm X hu hC hσ hk]
  exact Nat.mod_lt _ (Fintype.card_pos)


end
end ECDLP.L74
end
