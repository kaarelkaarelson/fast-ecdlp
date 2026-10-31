import ECDLP.L88_Uni
import ECDLP.L84_Eng

/-!
# L88 / Eng: `EngVal` for the real engine command `engCmd` from `EdgeCore 200` (twin of L84 `engCost_of_core`)

`uniC_val'` (L88_Uni) is the value theorem of the counting command on the ECDLP top.  Here it is instantiated at
`shapeData_edge` / `topIface_edge` (L85_B), with the three side hypotheses that the command-level statement needs and that
are NOT consequences of L80's `FrameIn`:
* `EdgeNetValue`: the value of the gate network of the memory, over `ZMod m`, is `Zc` (this is the `value` field of L58's
  `TopNet`, which for the real net is `edge_value_zmod` + the count identification; `EdgeCore` has no value field);
* `hlt`: `Zc < 2^len` (the count fits the loop's bit budget `n`);
* `hA10`: cell `0` of array `1` is `0` (otherwise the divisor-1 correction `c1E` of the command is `1` when `a = 0`).
-/
noncomputable section
namespace ECDLP.L88
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex ECDLP.L65 ECDLP.L60 ECDLP.L72 ECDLP.L80 ECDLP.L84
  ECDLP.L85A ECDLP.L85B ECDLP.L70 ECDLP.L61 ECDLP ECDLP.L51 Computability

theorem c1_zero_of_cell0 (f : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (h : f 0 = 0) :
    (if 1 / 2 ^ 0 = numCells f 0 (n - 0) then 1 else 0) = 0 := by
  obtain ⟨n', hn'⟩ : ∃ n', n - 0 = n' + 1 := ⟨n - 1, by omega⟩
  rw [hn', numCells_succ, h]
  simp only [if_true, zero_add, pow_zero, Nat.div_one]
  rw [if_neg]
  omega

/-- the value link: the gate network of a layout-satisfying memory counts `Zc` modulo every `m > 1` -/
def EdgeNetValue (r : ℕ) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE) : Prop :=
  ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → ∀ s : St, FrameIn r (redInp x τ) s → ∀ m, 1 < m →
    (((C.D m (redInp x τ).len 0 s.ar).inner.value : ZMod m)) = ((Zc (r + 1) x τ : ℕ) : ZMod m)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`EngVal` for the real engine, from `EdgeCore 200`** (plus the three side hypotheses above). -/
theorem engVal_of_core (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (hnet : EdgeNetValue r C)
    (hlt : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → Zc (r + 1) x τ < 2 ^ (redInp x τ).len)
    (hA10 : ∀ (i : EdgeInp) (s : St), FrameIn r i s → s.ar 1 0 = 0) :
    EngVal r (engCmd r E gE btE) := by
  have : Fact (100 ≤ 200) := ECDLP.L85.fact200
  intro x τ hg s hF
  have h0 : s.sc 0 = (redInp x τ).len := hF.1
  have h2 : s.sc 2 = 0 := hF.2.1
  have hlen : 1 ≤ (redInp x τ).len := by unfold EdgeInp.len; omega
  have hkn : s.sc 2 < s.sc 0 := by omega
  have hD : s.ar 1 (s.sc 2) = 0 := by rw [h2]; exact hA10 _ s hF
  have hcx : (if 1 / 2 ^ s.sc 2 = numCells (s.ar 1) (s.sc 2) (s.sc 0 - s.sc 2) then 1 else 0) = 0 := by
    rw [h2, h0]; exact c1_zero_of_cell0 _ _ hlen (hA10 _ s hF)
  have := uniC_val' (topIface_edge r hr C) (shapeData_edge r hr C) s (cnt := Zc (r + 1) x τ) hkn hD hcx
    (by rw [h0]; exact hlt x τ hg)
    (fun m hm => by
      rw [h0, h2]
      exact hnet x τ hg s hF m hm)
  have e : engCmd r E gE btE = uniC (UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv E gE btE) (ECDLP.L85B.tabMv E gE btE)) := rfl
  rw [e, this]

end ECDLP.L88
end
