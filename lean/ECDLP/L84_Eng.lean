import ECDLP.L84_NoRdC
import ECDLP.L80_Cap
import ECDLP.L85_Final

/-!
# L84 / Eng: `EngCost` (L80's engine-cost hypothesis) from L85's `EdgeCore 200`
-/
noncomputable section
namespace ECDLP.L84
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80

/-- the real engine command for the edge family (L85's `UP'`, depth budget `D = 200`) -/
def engCmd (r : ℕ) (E : NEx) (gE btE : Ex) : Cmd :=
  uniC (ECDLP.L85A.UP' (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE))

/-- **`EngCost` from `EdgeCore 200`.**  L85's `uniC_cost'` is state-generic (only `sc 2 < sc 0` and `UniReq V (sc 0)` are used),
so the cost bound holds on every state with `sc 0 = len`, `sc 2 < sc 0`, not only on `stOf r i`. -/
theorem engCost_of_core (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : ECDLP.L85B.EdgeCore 200 r E gE btE) : EngCost r (engCmd r E gE btE) := by
  haveI : Fact (100 ≤ 200) := ECDLP.L85.fact200
  obtain ⟨c, h⟩ := ECDLP.L85A.uniC_cost' (ECDLP.L85B.topIface_edge r hr C) (edgeFamily_spec r)
  exact ⟨c, 24 * 200 + 8, fun V i _ R s h0 h2 => h V s h2 (by rw [h0]; exact R)⟩

end ECDLP.L84
end
