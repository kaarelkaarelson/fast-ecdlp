import ECDLP.L64_PEx
import ECDLP.L57_Cluster

/-!
# L64 / Clus: the cluster map of L57 as an expression, and `CoarsenHyp` for a forced gate network

`clusE`: the expression of `ECDLP.L57.clus` (cumulative weights) given an expression `btE` for the node weights.
`coarsenHyp_pforced`: `CoarsenHyp` (Rudich's hypothesis bundle of `coarsen_rep`) for `(P.toGNet).toNet e`,
the coding `pfCoding` and the cluster map `clus wt g' _`.
-/
noncomputable section
namespace ECDLP.L64
open Factoring.Aux Finset Ex ECDLP.L56

section
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
  {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- accumulated weight of the nodes before node `u` -/
def accE (btE : Ex) : Ex := nsum (u + 8) (.var u) (un1 X (u + 8) btE)
/-- total weight -/
def totE (btE : Ex) : Ex := nsum (u + 8) X.gE (un1 X (u + 8) btE)
/-- the cluster of node `u`, `g'` clusters -/
def clusE (btE : Ex) (g' : ℕ) : Ex :=
  .ifLt (.lit (g' - 1)) (.div (.mul (.lit g') (accE X btE)) (totE X btE)) (.lit (g' - 1))
    (.div (.mul (.lit g') (accE X btE)) (totE X btE))

variable {σ₀ : ℕ → ℕ} {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {btE : Ex} {wt : Fin g → ℕ}
  (hbt : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Ex.eval σ A btE = wt k)
include hu hC hσ hbt

theorem eval_wtSlot (j : ℕ) (hj : j < g) (σ' : ℕ → ℕ) (hσ' : Ag B σ₀ σ') (hs : σ' (u + 8) = j) :
    Ex.eval σ' A (un1 X (u + 8) btE) = ECDLP.L57.wf wt j := by
  simp only [un1, Ex.eval]
  rw [hbt σ₀ hC _ (hσ'.upd (by omega) _) ⟨j, hj⟩ (by simp [hs])]
  simp [ECDLP.L57.wf, hj]

theorem eval_accE {a : Fin g} (ha : σ u = a) :
    Ex.eval σ A (accE X btE) = ∑ j ∈ range a.val, ECDLP.L57.wf wt j := by
  simp only [accE, eval_nsum, Ex.eval, ha]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  exact eval_wtSlot X hu hC hσ hbt j (lt_trans hj' a.2) _ (hσ.upd (by omega) _) (by simp)

theorem eval_totE : Ex.eval σ A (totE X btE) = ∑ i, wt i := by
  simp only [totE, eval_nsum, X.hg σ₀ hC σ hσ]
  have h1 : ∑ x ∈ range g, Ex.eval (Function.update σ (u + 8) x) A (un1 X (u + 8) btE) =
      ∑ x ∈ range g, ECDLP.L57.wf wt x :=
    sum_congr rfl fun j hj => eval_wtSlot X hu hC hσ hbt j (mem_range.1 hj) _ (hσ.upd (by omega) _) (by simp)
  rw [h1, ← Fin.sum_univ_eq_sum_range (ECDLP.L57.wf wt) g]
  exact sum_congr rfl fun i _ => by simp [ECDLP.L57.wf]

theorem eval_clusE {a : Fin g} (ha : σ u = a) (g' : ℕ) (hg' : 0 < g') :
    Ex.eval σ A (clusE X btE g') = (ECDLP.L57.clus wt g' hg' a).val := by
  simp only [clusE, Ex.eval, eval_accE X hu hC hσ hbt ha, eval_totE X hu hC hσ hbt]
  simp only [ECDLP.L57.clus]
  split_ifs with h <;> omega


end

section
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
  {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) {σ₀ : ℕ → ℕ}

/-- The network expressions built from the gate-level obligations. -/
def netEx : NEx :=
  ⟨szEx X, WEx X, cEx X, msgTest (mMsg X u (u + 1)) (cEx X) (u + 3) (u + 9),
    msgTest (mMsg X (u + 1) u) (cEx X) (u + 3) (u + 9)⟩

/-- **`CoarsenHyp` for a forced gate network** (Rudich's hypothesis bundle of `coarsen_rep`), for the coding
`pfCoding` and the cluster map `clus wt g'` of L57. -/
theorem coarsenHyp_pforced {vm w : ℕ} (hm : σ₀ vm = m) (hm1 : 1 < m) (hu : B ≤ u) (hC : Ctx σ₀)
    (hP01 : ∀ i z, P.W i z = 0 ∨ P.W i z = 1) (hg0 : 0 < g) (hw : u + 4 ≤ w) (g' : ℕ) (hg' : 0 < g')
    {btE : Ex} {wt : Fin g → ℕ}
    (hbt : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Ex.eval σ A btE = wt k) :
    CoarsenHyp m B σ₀ A ⟨u, w, vm, netEx X, X.gE, clusE X btE g'⟩ ((toGNetE P E).toNet e) (pfCoding P E EF e)
      (ECDLP.L57.clus wt g' hg') where
  rep := nrep_pforced P E EF e u vm X hu hC hm hm1 hP01
  hg := hg0
  gE σ hσ := X.hg σ₀ hC σ hσ
  χE σ hσ a ha := eval_clusE X hu hC hσ hbt ha g' hg'
  hu := hu
  hw := hw
  hm := hm1

end
end ECDLP.L64
