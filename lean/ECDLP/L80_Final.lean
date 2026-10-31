import ECDLP.L80_Cap

/-!
# L80 / Final: L77's capstone with the one-time gate, the input-layer hook discharged and the per-call oracle built
`subexponentialRate_L80` : `SubexpRate (r+1)` from
* `EngVal r eng`, `EngCost r eng` : the engine's value on layout-satisfying states and its (state-generic) cost,
* `LSpec` : the per-call length test (L78's; not duplicated here).
Discharged here: L77's `HookSpec` (from L76 `checkC_run`), `EVal`/`HLink` (via `oraC = checkC ; frameW ; engine.shift S`), and the polynomial overhead.
-/
namespace ECDLP.L80
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

theorem subexponentialRate_L80 (r : ℕ) (eng lg : Cmd) (Tl : ℕ → ℕ) (S q fl : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_val : EngVal r eng) (H_cost : EngCost r eng)
    (H_len : LSpec (r + 1) lg Tl) (H_lenT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tl L ≤ C * 2 ^ (L / k)) :
    SubexpRate (r + 1) := by
  obtain ⟨Tc, hE, hT⟩ := oracle_spec r S hS eng H_val H_cost
  obtain ⟨Tg, hG, hTg⟩ := gate_hook' S q hS hq1 hqS Gx2 (hookCmd (r + 1)) fl 775 hfl (Th (r + 1)) (hook_spec (r + 1) (by omega))
  have hz := zspecAt_of_wrap H_len hE
  refine subexponentialRate_gate_strong (r + 1) _ _ fl _ Tg hG hz ?_ (hTg (fun k hk => Th_subexp (r + 1) k hk))
  intro k hk
  obtain ⟨C1, h1⟩ := H_lenT k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

end ECDLP.L80
