import ECDLP.L80_Final
import ECDLP.L78_Len
import ECDLP.L77_Final

/-!
# L87 / Merge: L80's capstone with L78's `LSpec` discharged, in both `encB` and L35's `Enc` form
Hypotheses: only `EngVal r eng`, `EngCost r eng` (+ numeric side conditions on the frame constants `S, fl`).
-/
namespace ECDLP.L87
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L78 ECDLP.L80 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

/-- shared data: gate, per-call oracle, with the summed cost -/
theorem merge_data (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal r eng) (H_cost : EngCost r eng) :
    ∃ (c G : Cmd) (T Tg : ℕ → ℕ), GateSpec Gx G fl Tg ∧ ZSpecAt Gx (r + 1) c T ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k)) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) := by
  obtain ⟨Tc, hE, hT⟩ := oracle_spec r S hS eng H_val H_cost
  obtain ⟨Tg, hG, hTg⟩ := gate_hook' S q hS hq1 hqS Gx2 (hookCmd (r + 1)) fl 775 hfl (Th (r + 1)) (hook_spec (r + 1) (by omega))
  have hz := zspecAt_of_wrap (lspec_len (r + 1) (by omega)) hE
  refine ⟨_, _, _, Tg, hG, hz, ?_, hTg (fun k hk => Th_subexp (r + 1) k hk)⟩
  intro k hk
  obtain ⟨C1, h1⟩ := Tl_subexp (r + 1) k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

theorem subexponentialRate_eng (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal r eng) (H_cost : EngCost r eng) : SubexpRate (r + 1) := by
  obtain ⟨c, G, T, Tg, hG, hz, hT, hTg⟩ := merge_data r eng S q fl hS hq1 hqS hfl H_val H_cost
  exact subexponentialRate_gate_strong (r + 1) c G fl T Tg hG hz hT hTg

theorem subexponentialRate_eng_enc (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal r eng) (H_cost : EngCost r eng) : SubexpRateEnc (r + 1) := by
  obtain ⟨c, G, T, Tg, hG, hz, hT, hTg⟩ := merge_data r eng S q fl hS hq1 hqS hfl H_val H_cost
  exact subexponentialRate_gate_strong_enc (r + 1) c G fl T Tg hG hz hT hTg

/-- the statement of L35's `subexponentialRate` (by `rfl`) -/
theorem subexponentialRate_eng_L35 (r : ℕ) (eng : Cmd) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal r eng) (H_cost : EngCost r eng) : (ECDLP.SubexponentialRateStmt (r + 1)) :=
  subexponentialRate_eng_enc r eng S q fl hS hq1 hqS hfl H_val H_cost

end ECDLP.L87
