import ECDLP.L85_B_Init

/-!
# L72 / Final: `tau_edge` and the rate theorem with the gate-level core as the only residual hypothesis

`topIface_edge`: `TopIface DB (edgeFamily r) (edgeL0v r) (searchMv ..) (tabMv ..)` from `EdgeCore` (and `r+1 <= 2^19000`).
`tau_edge_core`: the evaluation-cost hypothesis `tau` of `edge_rate`, for the real counting command
`uniC (UP' (edgeL0v r) (searchMv ..) (tabMv ..))` on the initial state `stOf r i`.
`edge_rate_core`: the rate `C_k 2^(len i / k)` for every `k >= 1`.
Hypotheses: `r + 1 <= 2^19000`, and `EdgeCore DB r E gE btE` (the L68-dependent content; see `L72_Core`).
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L85A

theorem edgeL0v_eval (r : ℕ) (K n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (tk : ∀ v k, topOk K (3 * K ^ 8) v k → σ v = k)
    (h11 : σ 11 = sOf n) (_h0 : σ 0 = n) : eval σ A (edgeL0v r) = (edgeFamily r).Ltop K (3 * K ^ 8) n := by
  rw [(LS.eval_cost (edgeL0_LS r K (3 * K ^ 8)) tk (A := A)).1]
  exact edgeL0_eval_Ltop r K (3 * K ^ 8) n h11

theorem topIface_edge (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    TopIface DB (edgeFamily r) (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE) :=
  topIface_of_shape (shapeData_edge r hr C) (edgeL0v r) (edgeL0v_vb r) (edgeL0v_eval r)
    (fun V ℓ n σ A R tk h11 _ => edgeL0v_cost hr R tk h11)

/-- **`tau` for the edge family**, with the real counting command and the real initial state. -/
theorem tau_edge_core (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    ∃ c E' : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len →
      (Cmd.run (uniC (UP' (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE))) (stOf r i)).2 ≤ c * (V + 1) ^ E' :=
  tau_edge r (topIface_edge r hr C) (stOf r) (stOf_sc0 r) (stOf_sc2 r)

/-- **The rate theorem** for the real counting command: `C_k 2^(len/k)` for every `k >= 1`. -/
theorem edge_rate_core (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    ∀ k : ℕ, 1 ≤ k → ∃ C' : ℕ, ∀ i : EdgeInp, i.adm r →
      (Cmd.run (uniC (UP' (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE))) (stOf r i)).2 ≤ C' * 2 ^ (i.len / k) :=
  edge_rate_cmd r (topIface_edge r hr C) (stOf r) (stOf_sc0 r) (stOf_sc2 r)

end ECDLP.L85B
