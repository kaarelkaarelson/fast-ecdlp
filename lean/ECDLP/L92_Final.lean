import ECDLP.L92_Eng

/-!
# L92 / Final: the capstone with the repaired frame, `hlt` discharged and `hA10` discharged
Remaining hypotheses: `EdgeCore 200 r ..` (the gate-network core), `EdgeNetValue r C` (L88's value link, L93's job),
and `r + 1 <= 2^19000` (item 3, see REPORT).
-/
namespace ECDLP.L92
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80 ECDLP.L84
  ECDLP.L85A ECDLP.L85B ECDLP.L70 ECDLP.L61 ECDLP ECDLP.L51 ECDLP.L88 Computability

theorem subexponentialRate_L92 (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C) :
    (ECDLP.SubexponentialRateStmt (r + 1)) :=
  subexponentialRate_eng_L35' r (engFull r E gE btE) 1400 1 10 le_rfl le_rfl (by norm_num) le_rfl
    (engFull_val r hr C hnet) (engFull_cost r hr C)

end ECDLP.L92
