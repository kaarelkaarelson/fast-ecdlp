import ECDLP.L102_Val
import ECDLP.L92_Merge

/-!
# L102 / Final: `ECDLP.subexponentialRate 1` (m = 1), unconditionally

`eng1` meets L92's engine contracts `EngVal' 0` and `EngCost 0`; then L92's `subexponentialRate_eng_L35'` (L87/L80/L77 pipeline)
gives L35's statement for `m = 1`.
-/
namespace ECDLP.L102
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L92 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem engVal_one : EngVal' 0 eng1 := by
  classical
  intro x τ hg s hF
  obtain ⟨⟨h0, -, hR⟩, -⟩ := hF
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hg' := hg
  obtain ⟨hpr, -, -, hτ⟩ := hg
  have hp2 : 2 ≤ p := hpr.two_le
  have hτ' : τ.length ≤ Nat.size p + 1 := by
    have : nlen 1 (p, a, b, xR, yR, π) = Nat.size p + 1 := by
      simp only [nlen, sInf_one, one_mul]
    simpa [this] using hτ
  simp only [redInp, EdgeInp.len] at h0 hR
  have hlen : Nat.size p + 1 ≤ s.sc 0 := by rw [h0]; omega
  have hv := eng1_val s p (xR % p) (yR % p) τ hR.hp hR.hxR hR.hyR hR.hlen hR.hpi hp2
    (Nat.mod_lt _ hpr.pos) hlen hτ'
  rw [hv, Zc_one _ _ hg']
  split_ifs <;> first | rfl | omega

theorem engCost_one : EngCost 0 eng1 := by
  refine ⟨100, 2, fun V i hi hU s h0 h2 => ?_⟩
  have h1 := eng1_cost s
  have h3 : s.sc 0 ≤ V := by have := hU.small; omega
  calc (Cmd.run eng1 s).2 ≤ 100 * (s.sc 0 + 1) ^ 2 := h1
    _ ≤ 100 * (V + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- **`ECDLP.subexponentialRate 1`**, no hypotheses. -/
theorem subexponentialRate_one : (ECDLP.SubexponentialRateStmt 1) :=
  subexponentialRate_eng_L35' 0 eng1 1400 1 10 le_rfl le_rfl (by norm_num) le_rfl engVal_one engCost_one

end ECDLP.L102
