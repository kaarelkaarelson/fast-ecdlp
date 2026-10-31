import ECDLP.L85_B_Final

/-!
# L85 / Final: the depth-parametric UniCost chain, at the budget `D = 200`

* `Factoring.Aux.UCost85.PB D V = (64 (Wv V + 1)^3)^D`, `cost_le_PBD` (depth `<= D`), `YB_le : YB D V <= 4 * 4096^D * (V+1)^(6 D + 2)`;
* `Factoring.Aux.uniC_cost85 D : exists c, cost <= c (V+1)^(24 D + 8)` (Rudich's `D = 100` gives exponent `2408`);
* `ECDLP.L85A.uniC_cost'` (generic top, `TopIface D`), `tau_edge`, `edge_rate_cmd`;
* `ECDLP.L85B.ExSyn D E gE btE`: the five fields of `E` have `dp + 40 <= D`, `gE, btE` have `dp <= 40`;
  `EdgeCore D r E gE btE`, `tau_edge_core`, `edge_rate_core`.
Here: `D = 200` (E fields `dp <= 160`; the top search/table `dp <= 200`; cost exponent `E = 4808`).
-/
namespace ECDLP.L85
open ECDLP.L85B Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

instance fact200 : Fact (100 ≤ 200) := ⟨by norm_num⟩

/-- the counting command at budget `D = 200`: cost `<= c (V+1)^4808` (Rudich: exponent `2408` at `D = 100`). -/
theorem uniC_cost_200 : ∃ c : ℕ, ∀ (V : ℕ) (st : St), st.sc 2 < st.sc 0 → (∀ j, st.ar 1 j ≤ 1) →
    UniReq85 V (st.sc 0) → (Cmd.run (uniC UP) st).2 ≤ c * (V + 1) ^ 4808 :=
  uniC_cost85 200

/-- `ExSyn` at `D = 200`, unfolded: the five `E` fields have depth `<= 160`, `gE`, `btE` depth `<= 40`. -/
theorem exSyn_200_depths {E : NEx} {gE btE : Ex} (S : ExSyn 200 E gE btE) :
    Ex.dp E.sz ≤ 160 ∧ Ex.dp E.W ≤ 160 ∧ Ex.dp E.c ≤ 160 ∧ Ex.dp E.l ≤ 160 ∧ Ex.dp E.r ≤ 160 ∧
      Ex.dp gE ≤ 40 ∧ Ex.dp btE ≤ 40 :=
  ⟨by have := S.dsz; omega, by have := S.dW; omega, by have := S.dc; omega, by have := S.dl; omega,
   by have := S.dr; omega, S.dg, S.db⟩

/-- top search and table depth `<= 200` from `ExSyn 200` (the budget the cost lemmas consume). -/
theorem top_depth_200 {E : NEx} {gE btE : Ex} (S : ExSyn 200 E gE btE) (K g : ℕ) :
    Ex.dp (GroupEx.tab (gsM E gE btE K g)) ≤ 200 ∧
      ∀ vx vs, Ex.dp (GroupEx.searchE (gsM E gE btE K g) vx vs) ≤ 200 :=
  ⟨tabM_dp S K g, fun vx vs => searchM_dp S K g vx vs⟩

/-- **`tau` for the real edge counting command with ExSyn at `D = 200`** (cost `c (V+1)^E'`). -/
theorem tau_edge_core_200 (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) :
    ∃ c E' : ℕ, ∀ (V : ℕ) (i : ECDLP.L65.EdgeInp), i.adm r → (ECDLP.L65.edgeFamily r).UniReq V i.len →
      (Cmd.run (uniC (ECDLP.L85A.UP' (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE))) (stOf r i)).2 ≤ c * (V + 1) ^ E' :=
  tau_edge_core r hr C

/-- **The rate: the polynomial-in-`V` cost is absorbed into `C_k 2^(len/k)`** at `D = 200`. -/
theorem edge_rate_core_200 (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) :
    ∀ k : ℕ, 1 ≤ k → ∃ C' : ℕ, ∀ i : ECDLP.L65.EdgeInp, i.adm r →
      (Cmd.run (uniC (ECDLP.L85A.UP' (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE))) (stOf r i)).2 ≤ C' * 2 ^ (i.len / k) :=
  edge_rate_core r hr C

end ECDLP.L85
