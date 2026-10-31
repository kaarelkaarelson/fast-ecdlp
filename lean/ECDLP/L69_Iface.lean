import ECDLP.L60_Fam
import FactoringAux.UniMain

/-!
# L69 / Iface: the interface between a network family and the uniform counting command

`UP' L0X SX TX` is Rudich's `UP` (`FactoringAux/UniInst.lean`) with the three top expressions that name the
network family replaced (top width `l0E`, top search `tsE`, top table `ttE`); the level parts, the literal setter
`tset = topSet 43` and every other command are Rudich's, unchanged.  `TopIface F L0X SX TX` lists exactly what the
cost proof (`L69_Setup`, `L69_Count`, `L69_Uni`) needs of these expressions: variable bounds, the value and cost
of the top width, the cost of the top search, and the value and cost of the top table entries (as entries of a
clique `Tt`).  Nothing else of the factoring network enters the cost proof.
-/
namespace ECDLP.L69
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost ECDLP.L60

/-- Rudich's parts with the top width, top search and top table replaced. -/
def UP' (L0X SX TX : Ex) : UParts := { UP with l0E := L0X, tsE := SX, ttE := TX }

theorem UP'_lset (L0X SX TX : Ex) : (UP' L0X SX TX).lset = UP.lset := rfl
theorem UP'_tset (L0X SX TX : Ex) : (UP' L0X SX TX).tset = UP.tset := rfl
theorem UP'_pathBody (L0X SX TX : Ex) : pathBody (UP' L0X SX TX) = pathBody UP := rfl
theorem UP'_dmLoop (L0X SX TX : Ex) : dmLoop (UP' L0X SX TX) = dmLoop UP := rfl
theorem UP'_sweepBody (L0X SX TX : Ex) : sweepBody (UP' L0X SX TX) = sweepBody UP := rfl

/-- **What the cost proof needs of the family's top expressions.**  `F.FamOK V m K0u ℓ n` is the requirement
on the value bound `V`; `K = Kb K0u ℓ`, `g = 3 K^8`, `L = F.Ltop K g n`. -/
structure TopIface (F : NetFamily) (L0X SX TX : Ex) : Prop where
  vl0 : VB 1000 L0X
  vts : VB 1000 SX
  vtt : VB 990 TX
  /-- what a requirement gives -/
  ok_hn : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 16 * n + 4 ≤ V
  ok_KG : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → Kb K0 ℓ * Gs K0 ℓ ≤ V
  ok_LK : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → 2 ^ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n * Kb K0 ℓ) ≤ V
  ok_deep : ∀ {V m K0 ℓ n}, F.FamOK V m K0 ℓ n → DeepReq V m K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n)
  /-- the top width: value -/
  l0_eval : ∀ (K n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ v k, topOk K (3 * K ^ 8) v k → σ v = k) →
    σ 11 = sOf n → σ 0 = n → eval σ A L0X = F.Ltop K (3 * K ^ 8) n
  /-- the top width: cost -/
  l0_cost : ∀ (V ℓ n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), F.FamOK (Wv V) 2 K0u ℓ n →
    (∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) → σ 11 = sOf n → σ 0 = n →
    cost σ A L0X ≤ PB V
  /-- the top search: cost, in a context for modulus `m` -/
  s_cost : ∀ (V m ℓ n k : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), F.FamOK (Wv V) m K0u ℓ n → k ≤ n →
    (∀ v k', topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k' → σ v = k') → σ 10 = m → σ 11 = sOf n → σ 0 = n →
    σ 2 = k → σ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n → cost σ A SX ≤ PB V
  /-- the top table: a clique `Tt` (the top clique at the search's choice) whose entries the table expression
  computes, at the search's value, with cost `≤ PB V` -/
  tab_spec : ∀ (V m ℓ n k : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), F.FamOK (Wv V) m K0u ℓ n → 1 < m → k ≤ n →
    (∀ v k', topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k' → σ₀ v = k') → σ₀ 10 = m → σ₀ 11 = sOf n → σ₀ 0 = n →
    σ₀ 2 = k → σ₀ 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n →
    ∃ Tt : Clique (ZMod m) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n),
      ∀ (σ : ℕ → ℕ) (A' : ℕ → ℕ → ℕ), (∀ y < 82, y ≠ 15 → σ y = σ₀ y) → σ 15 = eval σ₀ A SX →
        (∀ a, a ≠ 3 → A' a = A a) → σ 82 < Kb K0u ℓ → σ 83 < 2 ^ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n * Kb K0u ℓ) →
        eval σ A' TX = (tabK Tt (σ 82) (σ 83)).val ∧ cost σ A' TX ≤ PB V

end ECDLP.L69
