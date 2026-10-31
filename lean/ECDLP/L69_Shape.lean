import ECDLP.L69_Uni
import ECDLP.L58_Glue

/-!
# L69 / Shape: `TopIface` from a network shape (`TopShape` of L58) and its representation / bound data

Rudich's `top_search_bdd`, `top_tab_bdd`, `top_search`, `top_tab_rep` (UniCostTop, UniTopSpec), re-run for a general
`TopShape T` (the expressions that name a family) with the instance data `ShapeData`.  `ShapeData` bundles, for
every memory `A`, the network `D m n k A` the top expressions represent (its `NRep`/`CoarsenHyp` in every context,
its `Fits`/`total` bounds), its value bounds in Rudich's `CoarsenBddHyp` form (the analogue of `cluster_bdd`), and the
extraction of the numeric requirements from `F.FamOK`.  `topIface_of_shape` then gives `TopIface` for the
literal-free copies `SX, TX` of the top search and table.
-/
namespace ECDLP.L69
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost Finset SB ECDLP.L60 ECDLP.L58

/-- the network a memory encodes (data part) -/
structure RepNet (m : ℕ) where
  gI : ℕ
  inner : Net (ZMod m) gI
  κ : Coding inner
  cl : ∀ g : ℕ, 0 < g → Fin gI → Fin g

/-- **Instance data of a network shape for the cost proof.** -/
structure ShapeData (F : NetFamily) (T : TopShape) (SX TX : Ex) where
  hsF : ∀ n, T.sF n = sOf n
  hLtop : ∀ K g n, F.Ltop K g n = (K * T.U0 (sOf n) + g * T.P0 (sOf n) g) / K ^ 3
  hSX : ∀ K, LS (topOk K (3 * K ^ 8)) (GroupEx.searchE (T.gs K (3 * K ^ 8)) 13 14) SX
  hTX : ∀ K, LS (topOk K (3 * K ^ 8)) (GroupEx.tab (T.gs K (3 * K ^ 8))) TX
  hRd : ∀ g, (CoarsenEx.nex (T.cp g)).Rd
  dpS : ∀ K g, Ex.dp (GroupEx.searchE (T.gs K g) 13 14) ≤ 100
  dpT : ∀ K g, Ex.dp (GroupEx.tab (T.gs K g)) ≤ 100
  /-- the network of the instance in memory `A` -/
  D : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → RepNet m
  /-- it does not depend on array `3` (the engine's table) -/
  hcong : ∀ m n k A A', (∀ a, a ≠ 3 → A' a = A a) → D m n k A' = D m n k A
  hyp : ∀ m n k A g (hg : 0 < g) σ₀, 1 < m → k ≤ n → σ₀ 10 = m → σ₀ 11 = sOf n → σ₀ 0 = n → σ₀ 2 = k →
    CoarsenHyp m 13 σ₀ A (T.cp g) (D m n k A).inner (D m n k A).κ ((D m n k A).cl g hg)
  fits : ∀ m n k A g (hg : 0 < g), ((D m n k A).inner.coarsen ((D m n k A).cl g hg)).Fits (T.P0 (sOf n) g)
  total : ∀ m n k A g (hg : 0 < g), ((D m n k A).inner.coarsen ((D m n k A).cl g hg)).total ≤ T.U0 (sOf n)
  /-- width of a cluster's settings (bits) -/
  Wc : ℕ → ℕ → ℕ
  csz : ∀ m n k A g (hg : 0 < g) (γ : Fin g),
    ((D m n k A).κ.coarsen ((D m n k A).cl g hg)).s γ ≤ 2 ^ Wc n g
  /-- value bounds of the coarsened network, memory with cells `≤ 1` (Rudich `cluster_bdd`) -/
  bdd : ∀ V m ℓ n k A, F.FamOK V m K0u ℓ n → 1 < m → k ≤ n → (∀ a j, A a j ≤ 1) → ∀ σ₀ : ℕ → ℕ,
    σ₀ 10 = m → σ₀ 11 = sOf n → σ₀ 0 = n → σ₀ 2 = k → (hg : 0 < Gs K0u ℓ) →
    CoarsenBddHyp V m 13 σ₀ A (T.cp (Gs K0u ℓ)) (D m n k A).inner (D m n k A).κ ((D m n k A).cl (Gs K0u ℓ) hg)
  /-- numeric requirements -/
  ok_mm : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → m * m ≤ V
  ok_Kg : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → Kb K0 ℓ ^ Gs K0 ℓ ≤ V
  ok_gg : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → Gs K0 ℓ * Gs K0 ℓ ≤ V
  ok_KG : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → Kb K0 ℓ * Gs K0 ℓ ≤ V
  ok_g1 : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 * Gs K0 ℓ + 1 ≤ V
  ok_U0 : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → T.U0 (sOf n) ≤ V
  ok_P0 : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 ^ T.P0 (sOf n) (Gs K0 ℓ) ≤ V
  ok_grp : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 ^ (Wc n (Gs K0 ℓ) * (2 * Gs K0 ℓ / Kb K0 ℓ)) ≤ V
  ok_LK : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 ^ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n * Kb K0 ℓ) ≤ V
  ok_m1 : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 1 < m
  ok_hn : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 16 * n + 4 ≤ V
  ok_deep : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → DeepReq V m K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n)
  vS : VB 1000 SX
  vT : VB 990 TX

theorem Gs_pos (K0 ℓ : ℕ) (h : 2 ≤ K0) : 0 < Gs K0 ℓ := by
  have := Kb_ge K0 h ℓ
  show 0 < 3 * Kb K0 ℓ ^ 8
  have := Nat.pow_pos (n := 8) (show 0 < Kb K0 ℓ by omega); omega

section Lemmas
variable {F : NetFamily} {T : TopShape} {SX TX : Ex} (SD : ShapeData F T SX TX)
include SD

/-- The top search's values (Rudich `top_search_bdd`). -/
theorem SD_search_bdd {V m n k ℓ : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (R : F.FamOK V m K0u ℓ n) (hm : 1 < m)
    (hA : ∀ a j, A a j ≤ 1) (h10 : σ 10 = m) (h11 : σ 11 = sOf n) (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n)
    (h12 : σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) :
    Bdd V σ A (GroupEx.searchE (T.gs (Kb K0u ℓ) (Gs K0u ℓ)) 13 14) := by
  set K := Kb K0u ℓ
  set g := Gs K0u ℓ
  set L := F.Ltop K g n
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := Gs_pos K0u ℓ (by norm_num)
  have hL1 : L + 1 ≤ V := le_trans Nat.lt_two_pow_self
    (two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) (SD.ok_LK R))
  have H2 := SD.hyp m n k A g hg σ hm hkn h10 h11 h0 h2
  have Hb2 := SD.bdd V m ℓ n k A R hm hkn hA σ h10 h11 h0 h2 hg
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  have hE2 := coarsen_bdd H2 Hb2 (show 10 < 13 by norm_num)
  have hcw : ∀ x < K ^ g, ∀ γ γ' : Fin K, γ < γ' →
      (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl g hg)).coarsen (chiOf K g x hK0)).c γ γ' ≤ V :=
    fun _ _ γ γ' h => le_trans (Net.coarsen_c_le_total _ _ γ γ' h) (le_trans (SD.total m n k A g hg) (SD.ok_U0 R))
  exact GroupEx.search_bdd (S := T.gs K g) hK0 hg hm hr2 hE2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) h12
    (SD.ok_Kg R) (SD.ok_gg R) (SD.ok_KG R) (SD.ok_g1 R) hL1 hcw (Ag.refl _ _)

/-- the existence of a good grouping (Rudich `good_exists` at the family's parameters) -/
theorem SD_good {m n k ℓ : ℕ} (A : ℕ → ℕ → ℕ) :
    ∃ x < Kb K0u ℓ ^ Gs K0u ℓ, okG (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ)
      (Gs_pos K0u ℓ (by norm_num))))) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
      (by have := Kb_ge K0u (by norm_num) ℓ; omega) x := by
  have hg := Gs_pos K0u ℓ (by norm_num)
  rw [SD.hLtop]
  exact good_exists _ (T.P0 (sOf n) (Gs K0u ℓ)) (T.U0 (sOf n)) (SD.fits m n k A _ hg) (SD.total m n k A _ hg)
    (Kb_ge K0u (by norm_num) ℓ) rfl

/-- The top search's value (Rudich `top_search`). -/
theorem SD_search {m n k ℓ : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hm : 1 < m) (h10 : σ 10 = m) (h11 : σ 11 = sOf n)
    (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n) (h12 : σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) :
    eval σ A (GroupEx.searchE (T.gs (Kb K0u ℓ) (Gs K0u ℓ)) 13 14) =
      firstGood (okG (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ)
        (Gs_pos K0u ℓ (by norm_num))))) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
        (by have := Kb_ge K0u (by norm_num) ℓ; omega)) (Kb K0u ℓ ^ Gs K0u ℓ) (Kb K0u ℓ ^ Gs K0u ℓ) := by
  have hg := Gs_pos K0u ℓ (by norm_num)
  have hK2 : 2 ≤ Kb K0u ℓ := Kb_ge K0u (by norm_num) ℓ
  have H2 := SD.hyp m n k A _ hg σ hm hkn h10 h11 h0 h2
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  exact GroupEx.eval_searchE (S := T.gs (Kb K0u ℓ) (Gs K0u ℓ)) (L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (show 0 < Kb K0u ℓ by omega) hg hm hr2
    (show 10 < 13 by norm_num) (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num)
    (show 13 ≤ 15 by norm_num) (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num)
    (show (14 : ℕ) ≠ 15 by norm_num) (show 13 < 26 by norm_num) (show 14 < 26 by norm_num)
    (show 15 < 26 by norm_num) h12 (Ag.refl _ _)

/-- The top table's representation (Rudich `top_tab_rep`). -/
theorem SD_tab_rep {m n k ℓ : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hm : 1 < m) (h10 : σ 10 = m) (h11 : σ 11 = sOf n)
    (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n) (h12 : σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) {xf : ℕ}
    (h15 : σ 15 = xf) :
    TRep m 16 σ A 82 83 (GroupEx.tab (T.gs (Kb K0u ℓ) (Gs K0u ℓ)))
      ((((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ) (Gs_pos K0u ℓ (by norm_num)))).coarsen
        (chiOf (Kb K0u ℓ) (Gs K0u ℓ) xf (by have := Kb_ge K0u (by norm_num) ℓ; omega))).toClique
          (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)) := by
  have hg := Gs_pos K0u ℓ (by norm_num)
  have H3 := SD.hyp m n k A _ hg σ hm hkn h10 h11 h0 h2
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  exact GroupEx.group_rep (S := T.gs (Kb K0u ℓ) (Gs K0u ℓ)) (x := xf) (L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (show 0 < Kb K0u ℓ by have := Kb_ge K0u (by norm_num) ℓ; omega) hg hm
    hr3 (show 10 < 16 by norm_num) (show 15 < 16 by norm_num) (show 12 < 16 by norm_num)
    (show 16 ≤ 26 by norm_num) h15 h12

/-- The top table's values at the search's choice (Rudich `top_tab_bdd`). -/
theorem SD_tab_bdd {V m n k ℓ : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (R : F.FamOK V m K0u ℓ n) (hm : 1 < m)
    (hA : ∀ a j, A a j ≤ 1) (h10 : σ 10 = m) (h11 : σ 11 = sOf n) (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n)
    (h12 : σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (h15 : σ 15 = firstGood (okG (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ)
        (Gs_pos K0u ℓ (by norm_num))))) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
        (by have := Kb_ge K0u (by norm_num) ℓ; omega)) (Kb K0u ℓ ^ Gs K0u ℓ) (Kb K0u ℓ ^ Gs K0u ℓ)) :
    TBdd V 16 σ A 82 83 (GroupEx.tab (T.gs (Kb K0u ℓ) (Gs K0u ℓ))) (Kb K0u ℓ) := by
  set K := Kb K0u ℓ
  set g := Gs K0u ℓ
  set L := F.Ltop K g n
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := Gs_pos K0u ℓ (by norm_num)
  have hLK1 : 2 ^ L ≤ V := two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) (SD.ok_LK R)
  have H3 := SD.hyp m n k A g hg σ hm hkn h10 h11 h0 h2
  have Hb3 := SD.bdd V m ℓ n k A R hm hkn hA σ h10 h11 h0 h2 hg
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hE3 := (coarsen_bdd H3 Hb3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  set CN := (SD.D m n k A).inner.coarsen ((SD.D m n k A).cl g hg)
  set xf := firstGood (okG CN K L hK0) (K ^ g) (K ^ g)
  obtain ⟨x0, hx0, hok⟩ := SD_good SD (m := m) (n := n) (k := k) (ℓ := ℓ) A
  have hsp := firstGood_spec (okG CN K L hK0) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  refine GroupEx.tab_bdd (S := T.gs K g) (x := xf) (L := L) hK0 hg hm hr3 hE3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) h15 h12
    (le_trans hsp.1.le (SD.ok_Kg R)) (SD.ok_Kg R) (SD.ok_gg R) (SD.ok_mm R) (fun γ => ?_)
    (fun γ γ' h => two_pow_le_of (hsp.2.2 γ γ' h) hLK1)
    (fun a b h _ => two_pow_le_of (Net.c_le_fits _ (SD.fits m n k A g hg) a b h) (SD.ok_P0 R)) (SD.ok_LK R)
  refine le_trans (coarsen_s_le_unif _ _ γ (SD.Wc n g) (2 * g / K) (fun a => SD.csz m n k A g hg a) ?_)
    (SD.ok_grp R)
  rw [Nat.le_div_iff_mul_le hK0, mul_comm]
  exact hsp.2.1 γ

end Lemmas

/-- **`TopIface` from a network shape.**  `L0X` is the (literal-free) top width expression, with its value and cost. -/
theorem topIface_of_shape {F : NetFamily} {T : TopShape} {SX TX : Ex} (SD : ShapeData F T SX TX) (L0X : Ex)
    (vl0 : VB 1000 L0X)
    (l0_eval : ∀ (K n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ v k, topOk K (3 * K ^ 8) v k → σ v = k) →
      σ 11 = sOf n → σ 0 = n → eval σ A L0X = F.Ltop K (3 * K ^ 8) n)
    (l0_cost : ∀ (V ℓ n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), F.FamOK (Wv V) 2 K0u ℓ n →
      (∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) → σ 11 = sOf n → σ 0 = n →
      cost σ A L0X ≤ PB V) :
    TopIface F L0X SX TX where
  vl0 := vl0
  vts := SD.vS
  vtt := SD.vT
  ok_hn := SD.ok_hn
  ok_KG := SD.ok_KG
  ok_LK := SD.ok_LK
  ok_deep := SD.ok_deep
  l0_eval := l0_eval
  l0_cost := l0_cost
  s_cost V m ℓ n k σ A R hkn tk h10 h11 h0 h2 h12 := by
    have hm := SD.ok_m1 R
    have hK2 : 2 ≤ Kb K0u ℓ := Kb_ge K0u (by norm_num) ℓ
    have hS := group_search_rdn (S := T.gs (Kb K0u ℓ) (Gs K0u ℓ)) (SD.hRd (Gs K0u ℓ)) 13 14
    obtain ⟨e1, c1⟩ := LS.eval_cost (SD.hSX (Kb K0u ℓ)) tk (σ := σ) (A := A)
    rw [c1]
    show cost σ A (GroupEx.searchE (T.gs (Kb K0u ℓ) (Gs K0u ℓ)) 13 14) ≤ PB V
    rw [(eval_cost_normA hS σ A).2]
    exact cost_le_PB (SD_search_bdd SD R hm (normA_le A) h10 h11 h0 h2 hkn h12) (SD.dpS _ _)
  tab_spec V m ℓ n k σ₀ A R hm hkn tk h10 h11 h0 h2 h12 := by
    set K := Kb K0u ℓ with hKdef
    set g := Gs K0u ℓ with hgdef
    set L := F.Ltop K g n with hLdef
    have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
    have hK0 : 0 < K := by omega
    have hg : 0 < g := Gs_pos K0u ℓ (by norm_num)
    have hS := group_search_rdn (S := T.gs K g) (SD.hRd g) 13 14
    have hTb := group_tab_rdn (S := T.gs K g) (SD.hRd g)
    have hLK := SD.ok_LK R
    refine ⟨((((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl g hg)).coarsen
        (chiOf K g (eval σ₀ A SX) hK0)).toClique L), ?_⟩
    intro σ A' hσ h15 hA' h82 h83
    have xs : eval σ₀ A SX = eval σ₀ A (GroupEx.searchE (T.gs K g) 13 14) := (LS.eval_cost (SD.hSX K) tk (σ := σ₀) (A := A)).1
    have sA := SD_search SD (A := A) hm h10 h11 h0 h2 hkn h12
    have tkσ : ∀ v k', topOk K (3 * K ^ 8) v k' → σ v = k' := fun v k' h => by
      have := topOk_lt h; rw [hσ v (by omega) (by omega), tk v k' h]
    have hγ : σ 82 < K := h82
    refine ⟨?_, ?_⟩
    · -- value
      rw [(LS.eval_cost (SD.hTX K) tkσ (σ := σ) (A := A')).1]
      have hR := SD_tab_rep SD (σ := σ) (A := A') hm (by rw [hσ 10 (by norm_num) (by norm_num), h10])
        (by rw [hσ 11 (by norm_num) (by norm_num), h11]) (by rw [hσ 0 (by norm_num) (by norm_num), h0])
        (by rw [hσ 2 (by norm_num) (by norm_num), h2]) hkn (by rw [hσ 12 (by norm_num) (by norm_num), h12])
        (xf := eval σ₀ A SX) h15
      rw [SD.hcong m n k A A' hA'] at hR
      have hcA := SD.hcong m n k A A' hA'
      have z := hR σ (Ag.refl _ _) ⟨σ 82, hγ⟩ (σ 83) rfl rfl
      show eval σ A' (GroupEx.tab (T.gs K g)) = _
      rw [z.eq_val, tabK, dif_pos hγ]
    · -- cost
      rw [(LS.eval_cost (SD.hTX K) tkσ (σ := σ) (A := A')).2]
      show cost σ A' (GroupEx.tab (T.gs K g)) ≤ PB V
      rw [(eval_cost_normA hTb σ A').2]
      have hnn : ∀ a, a ≠ 3 → normA A' a = normA A a := fun a ha => by
        unfold normA; rw [hA' a ha]
      have hnorm := (eval_cost_normA hS σ₀ A).1
      have sN := SD_search SD (A := normA A) hm h10 h11 h0 h2 hkn h12
      have h15' : σ 15 = firstGood (okG (((SD.D m n k (normA A')).inner.coarsen ((SD.D m n k (normA A')).cl g
          (Gs_pos K0u ℓ (by norm_num))))) K L (by omega)) (K ^ g) (K ^ g) := by
        rw [SD.hcong m n k (normA A) (normA A') hnn]
        rw [h15, xs]
        exact hnorm.trans sN
      have hB := SD_tab_bdd SD (σ := σ) (A := normA A') R hm (normA_le _)
        (by rw [hσ 10 (by norm_num) (by norm_num), h10]) (by rw [hσ 11 (by norm_num) (by norm_num), h11])
        (by rw [hσ 0 (by norm_num) (by norm_num), h0]) (by rw [hσ 2 (by norm_num) (by norm_num), h2]) hkn
        (by rw [hσ 12 (by norm_num) (by norm_num), h12]) h15'
      refine cost_le_PB (hB σ (Ag.refl _ _) hγ ?_) (SD.dpT _ _)
      exact le_trans h83.le (by
        have hh := hLK
        exact hh)

end ECDLP.L69
