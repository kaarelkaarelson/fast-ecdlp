import ECDLP.L85_A_Shape
import ECDLP.L85_A_Uni

/-!
# L104 / Iface: the FRAME-RESTRICTED interface `TopIfaceF DB P F ..` and `ShapeDataF DB P F ..`
Copies of L85_A `TopIface`/`ShapeData` in which the memory-dependent fields (`s_cost`, `tab_spec`; `hyp fits total csz bdd`) are required only on memories
satisfying the invariant `P n A` (`n = sc 0`).  `P` must be stable under changes of array `3` (`hPc`) and closed under `normA` (`hPn`).
The A-universal `l0_eval`, `l0_cost`, `VB` fields are unchanged.
-/
namespace ECDLP.L104A
set_option linter.unusedSectionVars false
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

/-- **What the cost proof needs of the family's top expressions.**  `F.FamOK V m K0u ℓ n` is the requirement
on the value bound `V`; `K = Kb K0u ℓ`, `g = 3 K^8`, `L = F.Ltop K g n`. -/
structure TopIfaceF (DB : ℕ) (P : ℕ → (ℕ → ℕ → ℕ) → Prop) (F : NetFamily) (L0X SX TX : Ex) : Prop where
  vl0 : VB 1000 L0X
  vts : VB 1000 SX
  vtt : VB 990 TX
  /-- what a requirement gives -/
  ok_hn : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 16 * n + 4 ≤ V
  ok_KG : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → Kb K0 ℓ * Gs K0 ℓ ≤ V
  ok_LK : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 ^ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n * Kb K0 ℓ) ≤ V
  ok_deep : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → DeepReq V m K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n)
  hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A'
  /-- the top width: value -/
  l0_eval : ∀ (K n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ v k, topOk K (3 * K ^ 8) v k → σ v = k) →
    σ 11 = sOf n → σ 0 = n → eval σ A L0X = F.Ltop K (3 * K ^ 8) n
  /-- the top width: cost -/
  l0_cost : ∀ (V ℓ n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), F.FamOK (Wv V) 2 K0u ℓ n →
    (∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) → σ 11 = sOf n → σ 0 = n →
    cost σ A L0X ≤ PB DB V
  /-- the top search: cost, in a context for modulus `m` -/
  s_cost : ∀ (V m ℓ n k : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), P n A → F.FamOK (Wv V) m K0u ℓ n → k ≤ n →
    (∀ v k', topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k' → σ v = k') → σ 10 = m → σ 11 = sOf n → σ 0 = n →
    σ 2 = k → σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n → cost σ A SX ≤ PB DB V
  /-- the top table: a clique `Tt` (the top clique at the search's choice) whose entries the table expression
  computes, at the search's value, with cost `≤ PB DB V` -/
  tab_spec : ∀ (V m ℓ n k : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), P n A → F.FamOK (Wv V) m K0u ℓ n → 1 < m → k ≤ n →
    (∀ v k', topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k' → σ₀ v = k') → σ₀ 10 = m → σ₀ 11 = sOf n → σ₀ 0 = n →
    σ₀ 2 = k → σ₀ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n →
    ∃ Tt : Clique (ZMod m) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n),
      ∀ (σ : ℕ → ℕ) (A' : ℕ → ℕ → ℕ), (∀ y < 82, y ≠ 15 → σ y = σ₀ y) → σ 15 = eval σ₀ A SX →
        (∀ a, a ≠ 3 → A' a = A a) → σ 82 < Kb K0u ℓ → σ 83 < 2 ^ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n * Kb K0u ℓ) →
        eval σ A' TX = (tabK Tt (σ 82) (σ 83)).val ∧ cost σ A' TX ≤ PB DB V


/-- **Instance data of a network shape for the cost proof.** -/
structure ShapeDataF (DB : ℕ) (P : ℕ → (ℕ → ℕ → ℕ) → Prop) (F : NetFamily) (T : TopShape) (SX TX : Ex) where
  hsF : ∀ n, T.sF n = sOf n
  hLtop : ∀ K g n, F.Ltop K g n = (K * T.U0 (sOf n) + g * T.P0 (sOf n) g) / K ^ 3
  hSX : ∀ K, LS (topOk K (3 * K ^ 8)) (GroupEx.searchE (T.gs K (3 * K ^ 8)) 13 14) SX
  hTX : ∀ K, LS (topOk K (3 * K ^ 8)) (GroupEx.tab (T.gs K (3 * K ^ 8))) TX
  hRd : ∀ g, (CoarsenEx.nex (T.cp g)).Rd
  dpS : ∀ K g, Ex.dp (GroupEx.searchE (T.gs K g) 13 14) ≤ DB
  dpT : ∀ K g, Ex.dp (GroupEx.tab (T.gs K g)) ≤ DB
  /-- the network of the instance in memory `A` -/
  D : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → RepNet m
  /-- it does not depend on array `3` (the engine's table) -/
  hcong : ∀ m n k A A', (∀ a, a ≠ 3 → A' a = A a) → D m n k A' = D m n k A
  /-- the invariant depends only on arrays other than `3` -/
  hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A'
  /-- the invariant is closed under normalising cells -/
  hPn : ∀ n A, P n A → P n (normA A)
  hyp : ∀ m n k A, P n A → ∀ g (hg : 0 < g) σ₀, 1 < m → k ≤ n → σ₀ 10 = m → σ₀ 11 = sOf n → σ₀ 0 = n → σ₀ 2 = k →
    CoarsenHyp m 13 σ₀ A (T.cp g) (D m n k A).inner (D m n k A).κ ((D m n k A).cl g hg)
  fits : ∀ m n k A, P n A → ∀ g (hg : 0 < g), ((D m n k A).inner.coarsen ((D m n k A).cl g hg)).Fits (T.P0 (sOf n) g)
  total : ∀ m n k A, P n A → ∀ g (hg : 0 < g), ((D m n k A).inner.coarsen ((D m n k A).cl g hg)).total ≤ T.U0 (sOf n)
  /-- width of a cluster's settings (bits) -/
  Wc : ℕ → ℕ → ℕ
  csz : ∀ m n k A, P n A → ∀ g (hg : 0 < g) (γ : Fin g),
    ((D m n k A).κ.coarsen ((D m n k A).cl g hg)).s γ ≤ 2 ^ Wc n g
  /-- value bounds of the coarsened network, memory with cells `≤ 1` (Rudich `cluster_bdd`) -/
  bdd : ∀ V m ℓ n k A, P n A → F.FamOK V m K0u ℓ n → 1 < m → k ≤ n → (∀ a j, A a j ≤ 1) → ∀ σ₀ : ℕ → ℕ,
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


end ECDLP.L104A
