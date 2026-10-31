import ECDLP.L92_Count
import ECDLP.L88_Eng

/-!
# L92 / Eng: the full engine command `engFull = [len < T0 ? lookup : engCmd]`, with `EngVal'` and `EngCost`

`engVal'_long` : L88's `engVal_of_core` on `FrameIn'` states, with `hA10` read off `FrameIn'` and `hlt` discharged by `zc_lt_len`
for `len >= T0of r` (instead of the unprovable `Zc < 2^len` for every Good input).
`engFull`/`engFull_val`/`engFull_cost` : short inputs go to `lookCmd` (a finite table).
-/
noncomputable section
namespace ECDLP.L92
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80 ECDLP.L84
  ECDLP.L85A ECDLP.L85B ECDLP.L70 ECDLP.L61 ECDLP ECDLP.L51 ECDLP.L88 Computability

open Classical in
/-- `EngVal'` restricted to inputs of length `>= T` -/
def EngValGe (r T : ℕ) (eng : Cmd) : Prop :=
  ∀ (x : Inst) (τ : List Bool), ECDLP.L70.Good (r + 1) x τ → T ≤ (redInp x τ).len → ∀ s : St,
    FrameIn' r (redInp x τ) s → (Cmd.run eng s).1.sc 3 = (if 0 < Zc (r + 1) x τ then 0 else 1)

theorem reads72n_sc0 {σ σ' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : σ' 0 = σ 0) (hr : Reads72n σ A p a b X xR yR π ℓ bW) : Reads72n σ' A p a b X xR yR π ℓ bW :=
  ⟨by rw [h]; exact hr.hp, by rw [h]; exact hr.ha, by rw [h]; exact hr.hb, by rw [h]; exact hr.hxR,
    by rw [h]; exact hr.hyR, by rw [h]; exact hr.hOp, by rw [h]; exact hr.hX, by rw [h]; exact hr.hlen,
    by rw [h]; exact hr.hl, by rw [h]; exact hr.hbW, hr.hpi⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem engVal'_long (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C) :
    EngValGe r (T0of r) (engCmd r E gE btE) := by
  have : Fact (100 ≤ 200) := ECDLP.L85.fact200
  intro x τ hg hT s hF'
  obtain ⟨hF, hA⟩ := hF'
  have h0 : s.sc 0 = (redInp x τ).len := hF.1
  have h2 : s.sc 2 = 0 := hF.2.1
  have hlen : 1 ≤ (redInp x τ).len := by unfold EdgeInp.len; omega
  have hkn : s.sc 2 < s.sc 0 := by omega
  have hD : s.ar 1 (s.sc 2) = 0 := by rw [h2]; exact hA
  have hcx : (if 1 / 2 ^ s.sc 2 = numCells (s.ar 1) (s.sc 2) (s.sc 0 - s.sc 2) then 1 else 0) = 0 := by
    rw [h2, h0]; exact c1_zero_of_cell0 _ _ hlen hA
  have := uniC_val' (topIface_edge r hr C) (shapeData_edge r hr C) s (cnt := Zc (r + 1) x τ) hkn hD hcx
    (by rw [h0]; exact zc_lt_len r x τ hg hT)
    (fun m hm => by
      rw [h0, h2]
      exact hnet x τ hg s hF m hm)
  have e : engCmd r E gE btE = uniC (UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv E gE btE) (ECDLP.L85B.tabMv E gE btE)) := rfl
  rw [e, this]

/-- the full engine command: lookup for short inputs, the counting command otherwise (scalar `22` is the bound) -/
def engFull (r : ℕ) (E : NEx) (gE btE : Ex) : Cmd :=
  .seq (.setK 22 (T0of r)) (.ifLt 0 22 (lookCmd (r + 1) (T0of r)) (engCmd r E gE btE))

theorem engFull_val (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C) : EngVal' r (engFull r E gE btE) := by
  classical
  intro x τ hg s hF
  have h0 : s.sc 0 = (redInp x τ).len := hF.1.1
  have e0 : (s.setSc 22 (T0of r)).sc 0 = s.sc 0 := by simp [St.setSc, Function.update_of_ne]
  have e22 : (s.setSc 22 (T0of r)).sc 22 = T0of r := by simp [St.setSc]
  have hF2 : FrameIn' r (redInp x τ) (s.setSc 22 (T0of r)) :=
    ⟨⟨by rw [e0]; exact hF.1.1, by simpa [St.setSc, Function.update_of_ne] using hF.1.2.1,
      reads72n_sc0 e0 hF.1.2.2⟩, hF.2⟩
  simp only [engFull, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
  by_cases hlt : s.sc 0 < T0of r
  · simp only [hlt, if_true]
    have := (look_spec r (T0of r) x τ (s.setSc 22 (T0of r)) hF2.1 (by rw [← h0]; omega)
      (by simp [EdgeInp.len, redInp]; omega)).1
    convert this using 2
  · simp only [hlt, if_false]
    have := engVal'_long r hr C hnet x τ hg (by omega) _ hF2
    convert this using 2

theorem look_cost (m T0 : ℕ) (st : St) (h : st.sc 0 < T0) : (Cmd.run (lookCmd m T0) st).2 ≤ 38 * T0 + 1 := by
  classical
  have hd := dispatch_run (fun ℓ => dtree (probesL ℓ) (tabAns m ℓ))
    (fun ℓ st => tabAns m ℓ (probeBits st (probesL ℓ))) T0 (35 * T0 + 1)
    (fun ℓ st hℓ => by
      refine ⟨(dtree_run _ _ st).1, le_trans (dtree_run _ _ st).2 ?_⟩
      rw [length_probesL]; omega)
    (fun ℓ st v => rfl) T0 st le_rfl h
  unfold lookCmd
  omega

theorem engFull_cost (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) : EngCost r (engFull r E gE btE) := by
  obtain ⟨c, E', h⟩ := engCost_of_core r hr C
  refine ⟨c + 38 * T0of r + 4, E', fun V i hi hU s h0 h2 => ?_⟩
  have e0 : (s.setSc 22 (T0of r)).sc 0 = s.sc 0 := by simp [St.setSc, Function.update_of_ne]
  have e22 : (s.setSc 22 (T0of r)).sc 22 = T0of r := by simp [St.setSc]
  have hp : 1 ≤ (V + 1) ^ E' := Nat.one_le_pow _ _ (by omega)
  have hE := h V i hi hU (s.setSc 22 (T0of r)) (by rw [e0]; exact h0) (by simp [St.setSc, Function.update_of_ne]; omega)
  simp only [engFull, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
  have ex : (c + 38 * T0of r + 4) * (V + 1) ^ E' = c * (V + 1) ^ E' + (38 * T0of r + 4) * (V + 1) ^ E' := by ring
  have k1 : 38 * T0of r + 4 ≤ (38 * T0of r + 4) * (V + 1) ^ E' := by
    calc 38 * T0of r + 4 = (38 * T0of r + 4) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  by_cases hlt : s.sc 0 < T0of r
  · simp only [hlt, if_true]
    have := look_cost (r + 1) (T0of r) (s.setSc 22 (T0of r)) (by rw [e0]; exact hlt)
    omega
  · simp only [hlt, if_false]
    omega

end ECDLP.L92
end
