import ECDLP.L65_Rate
import ECDLP.L69_Shape
import ECDLP.L69_Bdd

/-!
# L69 / Tau: the hypothesis `tau` of `edge_rate`, conditional on the top interface

`tau_edge`: if the top expressions of the edge family satisfy `TopIface`, the run cost of the counting command
`uniC (UP' L0X SX TX)` on any admissible input is at most `c (V+1)^E` for every `V` meeting the family's `UniReq`.
`edge_rate_cmd`: `edge_rate` with `cost i := (uniC ...).run (stOf i)`: the cost is `C_k 2^(len/k)` for every `k`.
`tau_edge_shape`: the same from `ShapeData` and the top width expression (via `topIface_of_shape`).
-/
namespace ECDLP.L69
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex UCost ECDLP.L65 ECDLP.L60

/-- **`tau` for the edge family** (conditional on `TopIface`). -/
theorem tau_edge (r : ℕ) {L0X SX TX : Ex} (hI : TopIface (edgeFamily r) L0X SX TX) (stOf : EdgeInp → St)
    (hst0 : ∀ i, (stOf i).sc 0 = i.len) (hst2 : ∀ i, (stOf i).sc 2 < (stOf i).sc 0) :
    ∃ c E : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len →
      (Cmd.run (uniC (UP' L0X SX TX)) (stOf i)).2 ≤ c * (V + 1) ^ E := by
  obtain ⟨c, E, h⟩ := uniC_cost' hI (edgeFamily_spec r)
  exact ⟨c, E, fun V i _ R => h V (stOf i) (hst2 i) (by rw [hst0 i]; exact R)⟩

/-- **The rate theorem for the ECDLP edge family with the real counting command** (conditional on `TopIface`
and on the initial state). -/
theorem edge_rate_cmd (r : ℕ) {L0X SX TX : Ex} (hI : TopIface (edgeFamily r) L0X SX TX) (stOf : EdgeInp → St)
    (hst0 : ∀ i, (stOf i).sc 0 = i.len) (hst2 : ∀ i, (stOf i).sc 2 < (stOf i).sc 0) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ i : EdgeInp, i.adm r →
      (Cmd.run (uniC (UP' L0X SX TX)) (stOf i)).2 ≤ C * 2 ^ (i.len / k) :=
  edge_rate r (fun i => (Cmd.run (uniC (UP' L0X SX TX)) (stOf i)).2) (tau_edge r hI stOf hst0 hst2)

/-- The same from instance data of a network shape (`ShapeData`) and the top width expression. -/
theorem edge_rate_shape (r : ℕ) {T : ECDLP.L58.TopShape} {SX TX : Ex} (SD : ShapeData (edgeFamily r) T SX TX)
    (L0X : Ex) (vl0 : VB 1000 L0X)
    (l0_eval : ∀ (K n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ v k, topOk K (3 * K ^ 8) v k → σ v = k) →
      σ 11 = sOf n → σ 0 = n → eval σ A L0X = (edgeFamily r).Ltop K (3 * K ^ 8) n)
    (l0_cost : ∀ (V ℓ n : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (edgeFamily r).FamOK (Wv V) 2 K0u ℓ n →
      (∀ v k, topOk (Kb K0u ℓ) (3 * Kb K0u ℓ ^ 8) v k → σ v = k) → σ 11 = sOf n → σ 0 = n →
      cost σ A L0X ≤ PB V)
    (stOf : EdgeInp → St) (hst0 : ∀ i, (stOf i).sc 0 = i.len) (hst2 : ∀ i, (stOf i).sc 2 < (stOf i).sc 0) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ i : EdgeInp, i.adm r →
      (Cmd.run (uniC (UP' L0X SX TX)) (stOf i)).2 ≤ C * 2 ^ (i.len / k) :=
  edge_rate_cmd r (topIface_of_shape SD L0X vl0 l0_eval l0_cost) stOf hst0 hst2

end ECDLP.L69
