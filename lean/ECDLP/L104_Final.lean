import ECDLP.L104_Engine
import ECDLP.L104_Real
import ECDLP.L102_Final
import ECDLP.L77_Final

/-!
# L104 / Final: `subexponentialRate_all : forall m, (ECDLP.SubexponentialRateStmt m)` -- no hypotheses
* `PL_norm`: the invariant `PL r` is closed under `normA` (the layout predicate only sees zero / nonzero cells).
* `pl_of_frame`: at every `Good` call state with `T1 r <= len` the invariant holds (L96 `frameIn_fr`).
* `subexp_ge2 r (1 <= r)`: `subexponentialRate (r+1)` from `edgeCoreFL_real2` (no `OffFrame`, no `r+1 <= 2^19000`).
* `m = 0`: L77; `m = 1`: L102.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L104R
open Finset Factoring.Aux Ex ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L96 ECDLP.L92 ECDLP.L104 ECDLP.L61 ECDLP

theorem numCells_normA (B : ℕ → ℕ → ℕ) (a o n : ℕ) : numCells (normA B a) o n = numCells (B a) o n := by
  unfold numCells
  refine Finset.sum_congr rfl fun j _ => ?_
  have := normA_iff B a (o + j)
  by_cases h : B a (o + j) = 0
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

theorem reads72n_normA {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : Reads72n σ A p a b X xR yR π ℓ bW) : Reads72n σ (normA A) p a b X xR yR π ℓ bW where
  hp := by rw [numCells_normA]; exact h.hp
  ha := by rw [numCells_normA]; exact h.ha
  hb := by rw [numCells_normA]; exact h.hb
  hxR := by rw [numCells_normA]; exact h.hxR
  hyR := by rw [numCells_normA]; exact h.hyR
  hOp := by rw [numCells_normA]; exact h.hOp
  hX := by rw [numCells_normA]; exact h.hX
  hlen := by rw [numCells_normA]; exact h.hlen
  hl := by rw [numCells_normA]; exact h.hl
  hbW := by rw [numCells_normA]; exact h.hbW
  hpi q hq := by
    have := normA_iff A 6 (q + 1)
    rw [← h.hpi q hq]
    exact not_congr this.symm

theorem zero3_normA (A : ℕ → ℕ → ℕ) : zero3 (normA A) = normA (zero3 A) := by
  funext a j
  by_cases ha : a = 3
  · subst ha; simp [zero3, normA]
  · simp [zero3, normA, ha]

theorem PL_norm (r : ℕ) : ∀ n A, PL r n A → PL r n (normA A) := by
  intro n A ⟨⟨d, hd⟩, hL⟩
  refine ⟨⟨d, ?_⟩, hL⟩
  rw [zero3_normA]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hR, h9, h10⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6, h7, reads72n_normA hR, h9, h10⟩

theorem pl_of_frame (r : ℕ) (x : Inst) (τ : List Bool) (hG : Good (r + 1) x τ) (hT : T1 r ≤ (redInp x τ).len)
    (s : Factoring.Aux.Copied.PLib.St) (hF : FrameIn r (redInp x τ) s) : PL r (redInp x τ).len s.ar := by
  refine ⟨?_, le_trans (le_max_right _ _) hT⟩
  have := frameIn_fr r x τ hG s hF
  rwa [hF.1] at this

theorem subexp_ge2 (r : ℕ) (hr1 : 1 ≤ r) : (ECDLP.SubexponentialRateStmt (r + 1)) := by
  have C := edgeCoreFL_real2 r
  have hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s, FrameIn r (redInp x τ) s →
      PL r (redInp x τ).len s.ar := fun x τ hG hT s hF => pl_of_frame r x τ hG hT s hF
  have hnet := edgeNetValueF_of_core r hr1 (edgeCoreFL_real2 r) (ECDLP.L96.realRep_real2 r) hPfr
  exact subexponentialRate_engF r (engFullH r (Ereal2 r) (gEreal2 r) (btReal2 r)) 1400 1 10 le_rfl le_rfl (by norm_num) le_rfl
    (engFullHF_val r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r) hnet hPfr)
    (engFullHF_cost r (PL_cong r) (PL_norm r) (edgeCoreFL_real2 r) hPfr)

/-- **THE AUDIT STATEMENT, no hypotheses.** -/
theorem subexponentialRate_all : ∀ m : ℕ, (ECDLP.SubexponentialRateStmt m) := by
  intro m
  match m with
  | 0 => exact ECDLP.L77.subexponentialRate_zero_enc
  | 1 => exact ECDLP.L102.subexponentialRate_one
  | r + 2 => exact subexp_ge2 (r + 1) (by omega)

end ECDLP.L104R
end
