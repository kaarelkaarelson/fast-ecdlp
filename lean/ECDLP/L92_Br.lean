import ECDLP.L92_Eng

/-!
# L92 / Br: the branch command `engBr r T eng = [len < T ? lookup : eng]` for an arbitrary engine `eng` and threshold `T`
`engBr_val` : `EngVal'` from the engine's value on `len >= T`; `engBr_cost` : `EngCost` from the engine's cost on `len >= T`.
-/
noncomputable section
namespace ECDLP.L92
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80 ECDLP.L84
  ECDLP.L85A ECDLP.L85B ECDLP.L70 ECDLP.L61 ECDLP ECDLP.L51 ECDLP.L88 Computability

def engBr (r T : ℕ) (eng : Cmd) : Cmd :=
  .seq (.setK 22 T) (.ifLt 0 22 (lookCmd (r + 1) T) eng)

theorem engBr_val (r T : ℕ) (eng : Cmd) (h : EngValGe r T eng) : EngVal' r (engBr r T eng) := by
  classical
  intro x τ hg s hF
  have h0 : s.sc 0 = (redInp x τ).len := hF.1.1
  have e0 : (s.setSc 22 T).sc 0 = s.sc 0 := by simp [St.setSc, Function.update_of_ne]
  have e22 : (s.setSc 22 T).sc 22 = T := by simp [St.setSc]
  have hF2 : FrameIn' r (redInp x τ) (s.setSc 22 T) :=
    ⟨⟨by rw [e0]; exact hF.1.1, by simpa [St.setSc, Function.update_of_ne] using hF.1.2.1,
      reads72n_sc0 e0 hF.1.2.2⟩, hF.2⟩
  simp only [engBr, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
  by_cases hlt : s.sc 0 < T
  · simp only [hlt, if_true]
    have := (look_spec r T x τ (s.setSc 22 T) hF2.1 (by rw [← h0]; omega)
      (by simp [EdgeInp.len, redInp]; omega)).1
    convert this using 2
  · simp only [hlt, if_false]
    have := h x τ hg (by omega) _ hF2
    convert this using 2

theorem engBr_cost (r T : ℕ) (eng : Cmd) (c E' : ℕ)
    (h : ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len → T ≤ i.len → ∀ s : St, s.sc 0 = i.len →
      s.sc 2 < s.sc 0 → (Cmd.run eng s).2 ≤ c * (V + 1) ^ E') :
    EngCost r (engBr r T eng) := by
  refine ⟨c + 38 * T + 4, E', fun V i hi hU s h0 h2 => ?_⟩
  have e0 : (s.setSc 22 T).sc 0 = s.sc 0 := by simp [St.setSc, Function.update_of_ne]
  have e22 : (s.setSc 22 T).sc 22 = T := by simp [St.setSc]
  have ex : (c + 38 * T + 4) * (V + 1) ^ E' = c * (V + 1) ^ E' + (38 * T + 4) * (V + 1) ^ E' := by ring
  have hp : 1 ≤ (V + 1) ^ E' := Nat.one_le_pow _ _ (by omega)
  have k1 : 38 * T + 4 ≤ (38 * T + 4) * (V + 1) ^ E' := by
    calc 38 * T + 4 = (38 * T + 4) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  simp only [engBr, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
  by_cases hlt : s.sc 0 < T
  · simp only [hlt, if_true]
    have := look_cost (r + 1) T (s.setSc 22 T) (by rw [e0]; exact hlt)
    omega
  · simp only [hlt, if_false]
    have hE := h V i hi hU (by omega) (s.setSc 22 T) (by rw [e0]; exact h0)
      (by simp [St.setSc, Function.update_of_ne]; omega)
    omega

end ECDLP.L92
end
