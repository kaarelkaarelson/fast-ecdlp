import ECDLP.L85_B_Clus

/-!
# L72 / Cbdd: `CoarsenHyp` and `CoarsenBddHyp` for the cluster map `clusM` (item 1)

From the inner network's expression bounds (`NBdd`, `gE`, the weight expression `btE`) and the weight data
(`rowsum <= wt`, `s a <= 2^(wt a)`, `wt <= wmax`, `W/g + wmax <= Pc`, `2^Pc <= V`) we get, for the clusters
`clus wt g'` of L57 and the data `CP := <16, 26, 10, E, gE, clusM (lit g') gE btE>`:
`coarsenHyp_of_cluster` (the representation) and `coarsenBdd_of_cluster` (all of `CoarsenBddHyp`: the cluster map's
bound, the coarse sizes `sz`, the coarse widths `cw`, the inner widths `cin`).
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Ex SB ECDLP.L57 ECDLP.L56 ECDLP.L64 ECDLP.L58

/-- the clustering data of a network (`TopShape.cp` shape) with the cluster map `clusM` -/
def cpM (E : NEx) (gE btE : Ex) (g' : ℕ) : CP := ⟨16, 26, 10, E, gE, clusM (.lit g') gE btE⟩

variable {m gI g' : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {E : NEx} {gE btE : Ex} {N : Net (ZMod m) gI}
  {κ : Coding N} {wt : Fin gI → ℕ}

/-- **The representation** (`CoarsenHyp`) of the coarsened network for the cluster map `clusM`. -/
theorem coarsenHyp_of_cluster (rep : NRep m 10 13 σ₀ A (NVars.std 16) E N κ) (hgI : 0 < gI) (hg' : 0 < g')
    (Hcl : ClusHyp 13 gI σ₀ A gE btE wt) (hm : 1 < m) :
    CoarsenHyp m 13 σ₀ A (cpM E gE btE g') N κ (clus wt g' hg') where
  rep := rep
  hg := hgI
  gE σ hσ := Hcl.hgE σ hσ
  χE σ hσ a ha := by
    show Ex.eval σ A (clusM (.lit g') gE btE) = _
    exact eval_clusM Hcl hσ (gx := .lit g') (g' := g') rfl hg' ha
  hu := show 13 ≤ 16 by norm_num
  hw := show 16 + 4 ≤ 26 by norm_num
  hm := hm

theorem cluster_fits_total (hg' : 0 < g') (hrow : ∀ a, ∑ b, N.cc a b ≤ wt a) (wmax : ℕ) (hmax : ∀ a, wt a ≤ wmax) :
    (N.coarsen (clus wt g' hg')).Fits ((∑ a, wt a) / g' + wmax) ∧
      (N.coarsen (clus wt g' hg')).total ≤ ∑ a, wt a :=
  clus_fits N wt hrow wmax hmax g' hg'

/-- **The value bounds** (`CoarsenBddHyp`) for the cluster map `clusM`. -/
theorem coarsenBdd_of_cluster {V : ℕ} (hg' : 0 < g') (Hcl : ClusHyp 13 gI σ₀ A gE btE wt)
    (hEb : NBdd V 13 σ₀ A (NVars.std 16) E gI)
    (hgb : ∀ σ, Ag 13 σ₀ σ → Bdd V σ A gE)
    (hbb : ∀ σ, Ag 13 σ₀ σ → ∀ k : Fin gI, σ 20 = k → Bdd V σ A btE)
    (hmm : m * m ≤ V) (hg'V : g' ≤ V) (hgg : gI * gI ≤ V) (hV1 : 1 ≤ V)
    (hW : ∑ i, wt i ≤ V) (hgW : g' * ∑ i, wt i ≤ V)
    (hrow : ∀ a, ∑ b, N.cc a b ≤ wt a) (hheld : ∀ a : Fin gI, κ.s a ≤ 2 ^ wt a) (wmax : ℕ) (hmax : ∀ a, wt a ≤ wmax)
    (Pc : ℕ) (hPc : (∑ a, wt a) / g' + wmax ≤ Pc) (hVP : 2 ^ Pc ≤ V) :
    CoarsenBddHyp V m 13 σ₀ A (cpM E gE btE g') N κ (clus wt g' hg') where
  E := hEb
  gE := hgb
  χE σ hσ hu := by
    show Bdd V σ A (clusM (.lit g') gE btE)
    have hgI : gI ≤ V := le_trans (Nat.le_mul_self gI) hgg
    exact bdd_clusM Hcl hσ (V := V) (gx := .lit g') (g' := g') rfl (B_lit hg'V) hV1 hgI hbb (hgb σ hσ) hW hgW
      (a := ⟨σ 16, hu⟩) rfl
  mm := hmm
  KV := hg'V
  gg := hgg
  sz γ := by
    refine le_trans (coarsen_s_le κ (clus wt g' hg') γ wt (fun a _ => hheld a)) (le_trans ?_ hVP)
    exact Nat.pow_le_pow_right (by norm_num) (le_trans (clus_wt_sum_le wt wmax hmax g' hg' γ) hPc)
  cw γ γ' h := by
    have hf := (cluster_fits_total hg' hrow wmax hmax).1
    have := Net.c_le_fits _ hf γ γ' h
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (le_trans this hPc)) hVP
  cin a b h _ := by
    have hf : N.Fits wmax := fun a => le_trans (hrow a) (hmax a)
    have := Net.c_le_fits N hf a b h
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (le_trans this (le_trans (Nat.le_add_left _ _) hPc))) hVP

end ECDLP.L85B
