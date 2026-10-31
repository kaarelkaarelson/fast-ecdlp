import FactoringAux.EngineTop

/-!
# L58: the engine glue, generic in the network

`Factoring.Aux.top_rep` (EngineTop.lean) is the one place where Rudich's counting engine meets the
multiplication network.  Here it is re-proved for an arbitrary network family (`TopShape` = the
expressions that name the family, `TopNet` = the instance data), and the factoring instance is
recovered as a corollary (`top_rep_of_gen`), so the interface is not vacuous.
-/

namespace ECDLP.L58

open Factoring.Aux Finset Ex

/-- The expressions that name a network family at the top of the engine (Rudich: `sE`, `L0E`,
`clPc`).  The variable layout is that of `topE`: `10` modulus, `11` size parameter, `12` top width,
`15` top grouping code, inner network arguments from `16`, clusters' arguments from `26`. -/
structure TopShape where
  /-- size parameter of the family as a function of the input length `n = σ 0` -/
  sF : ℕ → ℕ
  sE : Ex
  eval_sE : ∀ (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), eval σ A sE = sF (σ 0)
  /-- bound on the total shared bits, and on the per-cluster row sum, of the `g`-cluster network -/
  U0 : ℕ → ℕ
  P0 : ℕ → ℕ → ℕ
  /-- expression for the top width `(K * U0 s + g * P0 s g) / K^3` -/
  L0E : ℕ → ℕ → Ex
  eval_L0E : ∀ (K g s : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), σ 11 = s →
    eval σ A (L0E K g) = (K * U0 s + g * P0 s g) / K ^ 3
  /-- inner network expressions (size, weight, width, factors), node count, cluster map -/
  E : NEx
  gE : Ex
  χE : ℕ → Ex

/-- The clustering data (`clPc g` for the multiplication network). -/
def TopShape.cp (T : TopShape) (g : ℕ) : CP := ⟨16, 26, 10, T.E, T.gE, T.χE g⟩

/-- The top group step (`gsTop`). -/
def TopShape.gs (T : TopShape) (K g : ℕ) : GS := ⟨26, 10, 15, 12, g, K, CoarsenEx.nex (T.cp g)⟩

/-- The whole-count expression (`topE`). -/
def TopShape.topE (T : TopShape) (K0 ℓ : ℕ) : Ex :=
  .lett 11 T.sE (.lett 12 (T.L0E (Kb K0 ℓ) (Gs K0 ℓ))
    (.lett 15 (GroupEx.searchE (T.gs (Kb K0 ℓ) (Gs K0 ℓ)) 13 14)
      (deepEx K0 ℓ 100 10 12 82 83 (GroupEx.tab (T.gs (Kb K0 ℓ) (Gs K0 ℓ))))))

/-- **The interface.**  What a network family must provide at one instance (modulus `m`, input
length `n`, position `k`, memory `A`) so that the engine's top step represents the count `cnt`
times the deep multiplier: an inner network on `gI` nodes with its expression-level
representation in every context (`CoarsenHyp`), a cluster map into every `g` clusters, the fit
and total bounds of the clustered network, and its value (the count). -/
structure TopNet (T : TopShape) (m n k : ℕ) (A : ℕ → ℕ → ℕ) (cnt : ℕ) where
  gI : ℕ
  inner : Net (ZMod m) gI
  κ : Coding inner
  cl : ∀ g : ℕ, 0 < g → Fin gI → Fin g
  /-- the expression-level representation, in every context that sets `10, 11, 0, 2` -/
  hyp : ∀ (g : ℕ) (hg : 0 < g) (σ₀ : ℕ → ℕ), σ₀ 10 = m → σ₀ 11 = T.sF n → σ₀ 0 = n → σ₀ 2 = k →
    CoarsenHyp m 13 σ₀ A (T.cp g) inner κ (cl g hg)
  fits : ∀ (g : ℕ) (hg : 0 < g), (inner.coarsen (cl g hg)).Fits (T.P0 (T.sF n) g)
  total : ∀ (g : ℕ) (hg : 0 < g), (inner.coarsen (cl g hg)).total ≤ T.U0 (T.sF n)
  value : ∀ (g : ℕ) (hg : 0 < g), (inner.coarsen (cl g hg)).value = (cnt : ZMod m)

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- **The generic engine glue** (`top_rep` for an arbitrary network family): the top expression
represents `deepMult * cnt` modulo `m`. -/
theorem top_rep_gen (T : TopShape) (K0 ℓ : ℕ) (hK : 2 ≤ K0) {m n k cnt : ℕ} (hm : 1 < m)
    (h10 : σ 10 = m) (hn : σ 0 = n) (hk : σ 2 = k) (D : TopNet T m n k A cnt) :
    ZR m (eval σ A (T.topE K0 ℓ))
      ((deepMult K0 ℓ ((Kb K0 ℓ * T.U0 (T.sF n) + Gs K0 ℓ * T.P0 (T.sF n) (Gs K0 ℓ)) / Kb K0 ℓ ^ 3) : ZMod m) *
        (cnt : ZMod m)) := by
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  set s := T.sF n
  set L := (K * T.U0 s + g * T.P0 s g) / K ^ 3 with hL
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := by show 0 < 3 * K ^ 8; positivity
  have hgK : g = 3 * K ^ 8 := rfl
  rw [TopShape.topE, eval_lett, T.eval_sE, hn]
  set σ1 := Function.update σ 11 s
  have eL : eval σ1 A (T.L0E K g) = L := T.eval_L0E K g s σ1 A (by simp [σ1])
  rw [eval_lett, eL]
  set σ2 := Function.update σ1 12 L
  have H2 := D.hyp g hg σ2 (by simp [σ2, σ1, h10]) (by simp [σ2, σ1, s]) (by simp [σ2, σ1, hn])
    (by simp [σ2, σ1, hk])
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  set CN := D.inner.coarsen (D.cl g hg)
  rw [eval_lett, GroupEx.eval_searchE (S := T.gs K g) (L := L) hK0 hg hm hr2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) (show σ2 12 = L by simp [σ2])
    (Ag.refl _ _)]
  set xf := firstGood (okG CN K L hK0) (K ^ g) (K ^ g)
  set σ3 := Function.update σ2 15 xf
  have H3 := D.hyp g hg σ3 (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2, σ1, s])
    (by simp [σ3, σ2, σ1, hn]) (by simp [σ3, σ2, σ1, hk])
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hT := GroupEx.group_rep (S := T.gs K g) (x := xf) (L := L) hK0 hg hm hr3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) (show σ3 15 = xf by simp [σ3])
    (show σ3 12 = L by simp [σ3, σ2])
  set Ttop : Clique (ZMod m) (Kb K0 ℓ) L := (CN.coarsen (chiOf K g xf hK0)).toClique L
  have hd : ZR m (eval σ3 A (deepEx K0 ℓ 100 10 12 82 83 (GroupEx.tab (T.gs K g)))) (deepVal K0 hK ℓ L Ttop) :=
    deep_rep K0 hK hm ℓ 100 16 10 12 82 83 _ L Ttop σ3 hT (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) σ3 (Ag.refl _ _)
  rw [deepVal_eq K0 hK ℓ L Ttop] at hd
  obtain ⟨x0, hx0, hok⟩ := good_exists CN (T.P0 s g) (T.U0 s) (D.fits g hg) (D.total g hg) hK2 hgK
  have hspec := firstGood_spec (okG CN K L hK0) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  rw [okG_value CN hK0 hspec.2, D.value g hg] at hd
  exact hd


/-! ### Sanity: Rudich's multiplication network is an instance, and `top_rep` is recovered -/

/-- The factoring family. -/
def factoringShape : TopShape where
  sF := sOf
  sE := Ex.sE
  eval_sE := fun _ _ => eval_sE
  U0 s := 10 * (pA s * pA s) * fw s
  P0 s g := clP s g
  L0E K g := Ex.L0E K g
  eval_L0E _ _ _ _ _ h := eval_L0E h
  E := mulNEx 16 10 11
  gE := Ex.nodesE
  χE g := Ex.clχE g

theorem factoringShape_cp (g : ℕ) : factoringShape.cp g = Ex.clPc g := rfl
theorem factoringShape_topE (K0 ℓ : ℕ) : factoringShape.topE K0 ℓ = Ex.topE K0 ℓ := rfl

/-- The factoring instance of the interface (the hypotheses of `top_rep`). -/
def factoringTopNet {m n k : ℕ} (A : ℕ → ℕ → ℕ) (hm : 1 < m) (hkn : k ≤ n)
    (hnL : n ≤ pL (sOf n) * pL (sOf n)) (hN1 : 1 ≤ numCells (A 0) 1 n) :
    TopNet factoringShape m n k A
      (((numCells (A 0) 1 n).divisors.filter (fun d => d / 2 ^ k = numCells (A 1) k (n - k))).card) where
  gI := mulNodes (sOf n)
  inner := mulNet (sOf n) (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k))
  κ := mulCoding (sOf n) m (numCells (A 0) 1 n) k (numCells (A 1) k (n - k))
  cl g hg := fun a => clMG (sOf n) g hg ((MG.enum (pA (sOf n))).symm a)
  hyp g hg σ₀ h0 hs hn' hk' := clusterHyp (A := A) hm hg h0 hs hn' hk' hkn hnL
  fits g hg := clusterNet_fits (sOf n) _ _ k _ g hg
  total g hg := clusterNet_total_le (sOf n) _ _ k _ g hg
  value g hg := clusterNet_value (sOf n) _ _ k _ g hg hN1
    (lt_of_lt_of_le (numCells_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hnL))


/-- Rudich's `top_rep` (same statement) re-derived from the generic glue `top_rep_gen`. -/
theorem top_rep_of_gen (K0 ℓ : ℕ) (hK : 2 ≤ K0) {m n k : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hm : 1 < m)
    (h10 : σ 10 = m) (hn : σ 0 = n) (hk : σ 2 = k) (hkn : k ≤ n) (hN1 : 1 ≤ numCells (A 0) 1 n) :
    ZR m (eval σ A (Ex.topE K0 ℓ))
      ((deepMult K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) : ZMod m) *
        (((numCells (A 0) 1 n).divisors.filter (fun d => d / 2 ^ k = numCells (A 1) k (n - k))).card : ZMod m)) :=
  top_rep_gen factoringShape K0 ℓ hK hm h10 hn hk
    (factoringTopNet A hm hkn (sOf_spec n) hN1)

end ECDLP.L58
