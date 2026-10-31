import ECDLP.L92_Hr2
import ECDLP.L92_Br

/-!
# L92 / Hr3: the engine interface and the capstone WITHOUT `r + 1 <= 2^19000`
`topIface_edgeH` (TopIface for `famH r`), `uniReq_famH`, `Ub_le_two_pow_large` (`Ub r n <= 2^Sb n` for `n >= 4 (Uc r)^4`),
`engVal'_longH` (value, no `hr`), `engCost_longH` (cost on `len >= 4 (Uc r)^4`, no `hr`), the engine `engFullH` with threshold
`T1 r = max (T0of r) (4 (Uc r)^4)` and the capstone `subexponentialRate_L92H`.
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A

theorem topIface_edgeH (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    TopIface DB (famH r) (edgeL0v r) (searchMv E gE btE) (tabMv E gE btE) :=
  topIface_of_shape (shapeData_edgeH r C) (edgeL0v r) (edgeL0v_vb r) (edgeL0v_eval r)
    (fun V ℓ n σ A R tk h11 _ => edgeL0v_costH R.1 R.2 tk h11)

theorem uniReq_famH {r V n : ℕ} (h : (edgeFamily r).UniReq V n) (hU : Ub r n ≤ V) : (famH r).UniReq V n :=
  ⟨⟨fun m h1 h2 => ⟨h.main.top m h1 h2, hU⟩, h.main.hM⟩, h.np, h.lv, h.small, h.kb⟩

theorem Ub_le_two_pow_large (r n : ℕ) (hn : 4 * Uc r ^ 4 ≤ n) : Ub r n ≤ 2 ^ Sb n := by
  have h1 : n ≤ 4 * Xs n ^ 4 := Xs_n_le n
  have h2 : Uc r ^ 4 ≤ Xs n ^ 4 := Nat.le_of_mul_le_mul_left (le_trans hn h1) (by norm_num)
  have h3 : Uc r ≤ Xs n := (Nat.pow_le_pow_iff_left (by norm_num)).1 h2
  have hX : Xs n ≤ Xs n ^ 3 := Nat.le_self_pow (by norm_num) _
  refine le_trans (Ub_le_two_pow_extra r n) (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold Sb Scn
  omega

theorem V_ge_Ub {r V n : ℕ} (hn : 4 * Uc r ^ 4 ≤ n) (h : (edgeFamily r).UniReq V n) : Ub r n ≤ V := by
  have hm := h.main.top 2 (le_refl _) (by simp only [NetFamily.Mof]; omega)
  exact le_trans (Ub_le_two_pow_large r n hn) hm.hset

end ECDLP.L85B

namespace ECDLP.L92
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80 ECDLP.L84
  ECDLP.L85A ECDLP.L85B ECDLP.L70 ECDLP.L61 ECDLP ECDLP.L51 ECDLP.L88 Computability

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem engVal'_longH (r : ℕ) {E : NEx} {gE btE : Ex}
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
  have := uniC_val' (topIface_edgeH r C) (shapeData_edgeH r C) s (cnt := Zc (r + 1) x τ) hkn hD hcx
    (by rw [h0]; exact zc_lt_len r x τ hg hT)
    (fun m hm => by
      rw [h0, h2]
      exact hnet x τ hg s hF m hm)
  have e : engCmd r E gE btE = uniC (UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv E gE btE) (ECDLP.L85B.tabMv E gE btE)) := rfl
  rw [e, this]

/-- the threshold of the branch -/
def T1 (r : ℕ) : ℕ := max (T0of r) (4 * Uc r ^ 4)

theorem engCost_longH (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) :
    ∃ c : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len → T1 r ≤ i.len → ∀ s : St,
      s.sc 0 = i.len → s.sc 2 < s.sc 0 → (Cmd.run (engCmd r E gE btE) s).2 ≤ c * (V + 1) ^ (24 * 200 + 8) := by
  haveI : Fact (100 ≤ 200) := ECDLP.L85.fact200
  obtain ⟨c, h⟩ := uniC_cost' (topIface_edgeH r C) (famH_spec r)
  refine ⟨c, fun V i hi hU hT s h0 h2 => ?_⟩
  have hn : 4 * Uc r ^ 4 ≤ i.len := le_trans (le_max_right _ _) hT
  exact h V s h2 (by rw [h0]; exact uniReq_famH hU (V_ge_Ub hn hU))

/-- the full engine command, without the size hypothesis on `r` -/
def engFullH (r : ℕ) (E : NEx) (gE btE : Ex) : Cmd := engBr r (T1 r) (engCmd r E gE btE)

theorem engFullH_val (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C) :
    EngVal' r (engFullH r E gE btE) :=
  engBr_val r (T1 r) _ (fun x τ hg hT s hF => engVal'_longH r C hnet x τ hg (le_trans (le_max_left _ _) hT) s hF)

theorem engFullH_cost (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) :
    EngCost r (engFullH r E gE btE) := by
  obtain ⟨c, h⟩ := engCost_longH r C
  exact engBr_cost r (T1 r) _ c _ h

theorem subexponentialRate_L92H (r : ℕ) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C) :
    (ECDLP.SubexponentialRateStmt (r + 1)) :=
  subexponentialRate_eng_L35' r (engFullH r E gE btE) 1400 1 10 le_rfl le_rfl (by norm_num) le_rfl
    (engFullH_val r C hnet) (engFullH_cost r C)

end ECDLP.L92
end
