import ECDLPv2.L109_Source
import ECDLPv2.L109_Residue
import ECDLPv2.L113_Out

/-!
# L115 / Top: the counting driver (generic in the oracle)
`cntTop G fl cc = G ; ifZero fl ZERO (parse ; cc)`, `ZERO` leaves `Q[0] = 0` in the output array `Q = 2` (the empty code = `encodeNat 0`).
`CCSpec m cc T` : on `Gx` instances and call states `Conf x (pre x)`, `cc` leaves `encodeNat (Zc m x (pre x))` in array `2` within `T |encB x|` steps.
`cntTop_out` : `outOf (array 2) = encodeNat (ECDLP109.count m x)` and the source cost is `≤ Tg L + 21 L + T L + 8`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
open ECDLP ECDLP.L61 ECDLP.L70 ECDLP.L77 Turing Computability Function Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def zeroOut : Cmd := .seq (.setK 843 0) (.wr 2 843 0 843)

theorem zeroOut_run (st : St) : outOf ((Cmd.run zeroOut st).1.ar 2) = [] ∧ (Cmd.run zeroOut st).2 ≤ 3 := by
  have : (Cmd.run zeroOut st).1.ar 2 = Function.update (st.ar 2) 0 0 := by
    simp [zeroOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr, St.setAr, St.putAr]
  refine ⟨?_, by simp [zeroOut, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]⟩
  rw [this]
  simp [outOf]

theorem encodeNat_zero : encodeNat 0 = [] := by simp [encodeNat, encodeNum]

/-- the oracle contract of the counting driver -/
def CCSpec (m : ℕ) (cc : Cmd) (T : ℕ → ℕ) : Prop :=
  ∀ (x : Inst) (st : St), Gx x → Conf x (pre x) st →
    outOf ((Cmd.run cc st).1.ar 2) = encodeNat (Zc m x (pre x)) ∧ (Cmd.run cc st).2 ≤ T (encB x).length

def cntTop (G : Cmd) (fl : ℕ) (cc : Cmd) : Cmd :=
  .seq G (.ifZero fl zeroOut (.seq (.loop 0 1 parseBody) cc))

theorem zc_zero_of_not_Gx (m : ℕ) (x : Inst) (h : ¬ Gx x) : Zc m x (pre x) = 0 := by
  by_contra hne
  exact h ((good_iff m x _).1 (ECDLP.L70.Zc_pos_good m x _ (Nat.pos_of_ne_zero hne))).1

theorem cntTop_out (m : ℕ) (G cc : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ)
    (hG : GateSpec Gx G fl Tg) (hc : CCSpec m cc T) (x : Inst) :
    outOf ((srcOut (cntTop G fl cc) (encB x)).ar 2) = encodeNat (ECDLP109.count m x) ∧
      srcCost (cntTop G fl cc) (encB x) ≤ Tg (encB x).length + 21 * (encB x).length + T (encB x).length + 8 := by
  obtain ⟨g0, gA, g2, g5, g7, g8, gf, gc⟩ := hG.spec x
  rw [show ECDLP109.count m x = Zc m x (pre x) from ECDLP.L109.count_eq_Zc m x]
  simp only [srcOut, srcCost, cntTop, Cmd.run_seq, Cmd.run_ifZero]
  generalize Cmd.run G (St.init (encB x)) = r at g0 gA g2 g5 g7 g8 gf gc ⊢
  by_cases hF : Gx x
  · have hz : r.1.sc fl ≠ 0 := fun h => (gf.1 h) hF
    simp only [hz, if_false, Cmd.run_seq]
    obtain ⟨p, a, b, xR, yR, π⟩ := x
    set x : Inst := (p, a, b, xR, yR, π) with hxdef
    have hxs : encB x = block (pre x) ++ [p, a, b, xR, yR].flatMap (fun n => block (encodeNat n)) := rfl
    obtain ⟨p2, pc, p0, pA, psc, par, pcost⟩ := parse_run (pre x) ([p, a, b, xR, yR].flatMap (fun n => block (encodeNat n))) r.1
      (by rw [gA, hxs]) (by rw [g0, hxs]) g2 g7 g8
    generalize hs1 : Cmd.run (.loop 0 1 parseBody) r.1 = s1 at p2 pc p0 pA psc par pcost ⊢
    have hconf : Conf x (pre x) s1.1 := ⟨by rw [p0, g0], by rw [pA, gA], p2, pc⟩
    obtain ⟨o1, o2⟩ := hc x s1.1 hF hconf
    refine ⟨o1, ?_⟩
    rw [g0] at pcost
    omega
  · have hz : r.1.sc fl = 0 := gf.2 hF
    simp only [hz, if_true]
    obtain ⟨o1, o2⟩ := zeroOut_run r.1
    rw [zc_zero_of_not_Gx m x hF, encodeNat_zero]
    exact ⟨o1, by omega⟩

end ECDLP.L115
#print axioms ECDLP.L115.cntTop_out
