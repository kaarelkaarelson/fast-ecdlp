import ECDLP.L64_Clus
import ECDLP.L64_Val
import ECDLP.L58_Edge
import ECDLP.L57_Width
import ECDLP.L57_Edge

/-!
# L64 / Edge: `EdgeTopData` for `edgeNet` from the gate-level obligations

`clus_fits`: L57's `exists_cluster` with the witness exposed (the explicit cumulative-weight cluster map, which the
engine needs as an EXPRESSION).  `edgeTopData_of_pex`: from gate-level expressions `PEx` of `edgeNetM` and the
parameter inequalities, build Rudich-style `EdgeTopData` (L58) -- hence `top_rep_edge`/`zero_edge`.
-/
noncomputable section
namespace ECDLP.L64
open Finset Factoring.Aux Ex ECDLP.L57 ECDLP.L56 ECDLP.L58

variable {R : Type*} [CommRing R] {n : ℕ}

theorem clus_fits (N : Net R n) (wt : Fin n → ℕ) (hrow : ∀ a, ∑ b, N.cc a b ≤ wt a) (wmax : ℕ)
    (hmax : ∀ a, wt a ≤ wmax) (g : ℕ) (hg : 0 < g) :
    (N.coarsen (clus wt g hg)).Fits ((∑ a, wt a) / g + wmax) ∧
      (N.coarsen (clus wt g hg)).total ≤ ∑ a, wt a := by
  refine ⟨?_, ?_⟩
  · intro γ
    refine (Net.coarsen_rowsum_le N (clus wt g hg) γ).trans ?_
    set W := ∑ a, wt a with hWdef
    have hWn : W = ∑ i ∈ range n, wf wt i := by
      rw [hWdef, ← Fin.sum_univ_eq_sum_range (wf wt) n]
      refine sum_congr rfl fun a _ => ?_
      simp [wf]
    have hfmax : ∀ i, wf wt i ≤ wmax := by
      intro i; unfold wf; split_ifs with h
      · exact hmax _
      · exact Nat.zero_le _
    -- step 1: replace row sums by weights
    have s1 : ∑ a, (if clus wt g hg a = γ then ∑ b, N.cc a b else 0) ≤
        ∑ a : Fin n, (if clus wt g hg a = γ then wt a else 0) :=
      sum_le_sum fun a _ => by split_ifs; exacts [hrow a, le_rfl]
    -- step 2: the nonzero-weight members have the exact floor
    have s2 : ∑ a : Fin n, (if clus wt g hg a = γ then wt a else 0) =
        ∑ i ∈ (range n).filter (fun i => wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i := by
      rw [sum_filter, ← Fin.sum_univ_eq_sum_range
        (fun i => if wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val then wf wt i else 0) n]
      refine sum_congr rfl fun a _ => ?_
      have hwa : wf wt a.val = wt a := by simp [wf]
      rw [hwa]
      by_cases h0 : wt a = 0
      · simp [h0]
      · have hlt : (∑ j ∈ range a.val, wf wt j) < W := by
          have h1 : ∑ j ∈ range (a.val + 1), wf wt j ≤ ∑ i ∈ range n, wf wt i :=
            sum_le_sum_of_subset (range_mono (by omega))
          rw [sum_range_succ, hwa] at h1
          have := Nat.pos_of_ne_zero h0
          omega
        have hfl : g * (∑ j ∈ range a.val, wf wt j) / W < g := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          exact Nat.mul_lt_mul_of_pos_left hlt hg
        have hcl : (clus wt g hg a).val = g * (∑ j ∈ range a.val, wf wt j) / W := by
          unfold clus; simp only; rw [← hWdef]; omega
        have : (clus wt g hg a = γ) ↔ (g * (∑ j ∈ range a.val, wf wt j) / W = γ.val) := by
          rw [Fin.ext_iff, hcl]
        simp only [this, ne_eq, h0, not_false_eq_true, true_and]
    have s3 := cluster_sum (wf wt) n g wmax W hg hWn hfmax γ.val
    have s4 : (∑ i ∈ (range n).filter (fun i => wf wt i ≠ 0 ∧ g * (∑ j ∈ range i, wf wt j) / W = γ.val), wf wt i)
        ≤ W / g + wmax := by
      rw [← Nat.add_mul_div_left W wmax hg, Nat.le_div_iff_mul_le hg]
      linarith
    exact s1.trans (s2 ▸ s4)
  · refine (Net.coarsen_total_le N _).trans ?_
    exact sum_le_sum fun a _ => hrow a


section rowsum
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ιι : Type} [Fintype ιι] [DecidableEq ιι]
  {P : PForced (ZMod m) ιι} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
  {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e : ιι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- the shared bits of the node in slot `u+4`: `Σ_b cc a b` -/
def rowE : Ex := nsum (u + 9) X.gE (.lett u (.var (u + 4)) (.lett (u + 1) (.var (u + 9)) (cEx X)))

theorem eval_rowE {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {k : Fin g} (hk : σ (u + 4) = k) :
    Ex.eval σ A (rowE X) = ∑ b, ((toGNetE P E).toNet e).cc k b := by
  simp only [rowE, eval_nsum, X.hg σ₀ hC σ hσ]
  rw [Finset.sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [show ((toGNetE P E).toNet e).cc k j = (toGNetE P E).c (e.symm k) (e.symm j) from
    ECDLP.L57.PForcedW.cc_eq P e k j]
  simp only [Ex.eval]
  exact eval_cEx X hu hC (((hσ.upd (show B ≤ u + 9 by omega) _).upd (show B ≤ u by omega) _).upd
    (show B ≤ u + 1 by omega) _) (a := k) (b := j) (by simp [Function.update_apply, hk]) (by simp)

end rowsum

section edge
open ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54

variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem edge_P01 (m : ℕ) : ∀ (i : CG ι ιc N0.A) z, (edgeNetM (w := w) φ F ok m).W i z = 0 ∨
    (edgeNetM (w := w) φ F ok m).W i z = 1 := by
  intro i z
  rcases WE_01 (w := w) φ F ok i z with h | h
  · left; show Int.castRingHom (ZMod m) ((edgeNet (w := w) φ F ok).W i z) = 0; rw [h]; simp
  · right; show Int.castRingHom (ZMod m) ((edgeNet (w := w) φ F ok).W i z) = 1; rw [h]; simp

theorem edge_free_nonempty (m : ℕ) (i : CG ι ιc N0.A) : Nonempty ((edgeNetM (w := w) φ F ok m).Free i) := by
  cases i with
  | src i s => exact ⟨fun _ => ⟨0, by positivity⟩⟩
  | gt c g => exact ⟨()⟩

/-- the context in which the engine evaluates the network expressions -/
def CtxE (T : TopShape) (m n k : ℕ) : (ℕ → ℕ) → Prop :=
  fun σ₀ => σ₀ 10 = m ∧ σ₀ 11 = T.sF n ∧ σ₀ 0 = n ∧ σ₀ 2 = k

/-- Gate-level data for `edgeNetM m` at one modulus: explicit codings `E`, `EF` of messages and free values (the
Mathlib `Fintype.equivFin` used by `PForced.enc` is a non-canonical choice, so nothing can be computed from it), the
gate-level expressions `X` (variables `16..25`), their use in the shape `T`, and the bounds on the shared bits. -/
structure EdgeGateData (T : TopShape) (m n k : ℕ) (A : ℕ → ℕ → ℕ) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) where
  [hF : ∀ i, Nonempty ((edgeNetM (w := w) φ F ok m).Free i)]
  E : ∀ i, (edgeNetM (w := w) φ F ok m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Msg i))
  EF : ∀ i, (edgeNetM (w := w) φ F ok m).Free i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Free i))
  X : PEx (B := 13) (Ctx := CtxE T m n k) (A := A) (edgeNetM (w := w) φ F ok m) E EF e 16
  hE : T.E = netEx X
  hgE : T.gE = X.gE
  hχ : ∀ g', T.χE g' = clusE X (rowE X) g'
  hm1 : 1 < m
  hg0 : 0 < g
  wmax : ℕ
  hmax : ∀ a, ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b) ≤ wmax
  hfit : ∀ (g' : ℕ) (_ : 0 < g'),
    (∑ a, ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b)) / g' + wmax ≤ T.P0 (T.sF n) g'
  htot : ∑ a, ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b) ≤ T.U0 (T.sF n)

/-- **The engine interface (`TopNet`) for the edge family from gate-level data.** -/
def EdgeGateData.toTopNet {T : TopShape} {m n k : ℕ} {A : ℕ → ℕ → ℕ} {g : ℕ} {e : CG ι ιc N0.A ≃ Fin g}
    (D : EdgeGateData (w := w) φ F ok T m n k A e) (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b) :
    TopNet T m n k A (edgeCount φ F ok) :=
  haveI := D.hF
  { gI := g
    inner := (toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e
    κ := pfCoding (edgeNetM (w := w) φ F ok m) D.E D.EF e
    cl := fun g' hg => clus (fun a => ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e).cc a b)) g' hg
    hyp := fun g' hg σ₀ h10 h11 h0 h2 => by
      have := coarsenHyp_pforced D.X (σ₀ := σ₀) (vm := 10) (w := 26) h10 D.hm1 (by norm_num) ⟨h10, h11, h0, h2⟩
        (edge_P01 (w := w) φ F ok m) D.hg0 (by norm_num) g' hg (btE := rowE D.X)
        (wt := fun a => ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e).cc a b))
        (fun σ₀ hC σ hσ k hk => eval_rowE D.X (by norm_num) hC hσ hk)
      show CoarsenHyp m 13 σ₀ A ⟨16, 26, 10, T.E, T.gE, T.χE g'⟩ _ _ _
      rw [D.hE, D.hgE, D.hχ]
      exact this
    fits := fun g' hg a =>
      ((clus_fits ((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e)
        (fun a => ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e).cc a b)) (fun a => le_rfl) D.wmax D.hmax
        g' hg).1 a).trans (D.hfit g' hg)
    total := fun g' hg =>
      ((clus_fits ((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e)
        (fun a => ∑ b, (((toGNetE (edgeNetM (w := w) φ F ok m) D.E).toNet e).cc a b)) (fun a => le_rfl) D.wmax D.hmax
        g' hg).2).trans D.htot
    value := fun g' hg => by
      rw [Net.value_coarsen, value_toGNetE _ D.E e (edge_P01 (w := w) φ F ok m)]
      exact edge_value_zmod (w := w) φ F ok m D.hm1 hS hb e }

end edge

end ECDLP.L64
