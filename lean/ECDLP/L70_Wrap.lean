import ECDLP.L70_Good

/-!
# L70 / Wrap: from an engine-convention zero test and a guard to L61's `ZSpec`

* `ESpec m c0 Tc` : the engine's zero test `c0` (convention of `zero_edge'` / Rudich's `CSpec`: scalar `3` is `1`
  iff the count is `0`), required on `Good` instances only; keeps scalars `< 10` (except 3) and arrays `< 3`
  (automatic for `Ex.comp e 3 t`, `t ≥ 10`, by `comp_spec`).
* `GSpec m g Tg` : the guard decides `Good` (scalar `3` is the flag), within `Tg` steps, for every query of the driver.
* `wrapCmd g c0` = `g; if flag = 0 then skip else (c0; flip scalar 3)`.
* `zspec_of_wrap` : `ZSpec m (wrapCmd g c0) (Tg + Tc + 6)`.  This is the length-`(n+1)` guard (queries with
  `|τ| = n+1` have `¬ Good`, so the flag is `0` and the answer `0` is correct since `Zc = 0`) and the renaming wrapper
  (engine output `[Z = 0]` to the driver's `[0 < Z]`).
-/
namespace ECDLP.L70
open ECDLP ECDLP.L61 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the state conventions of `ZSpec` -/
def Conf (x : Inst) (τ : List Bool) (st : St) : Prop :=
  st.sc 0 = (encB x).length ∧ st.ar 0 = startingMemory (encB x) ∧ st.sc 2 = τ.length ∧
    ∀ j, j < τ.length → st.ar 1 j = bitN (τ.getD j false)

/-- flip the answer scalar -/
def flipCmd : Cmd := .ifZero 3 (.setK 3 1) (.setK 3 0)

theorem flip_run (st : St) :
    (Cmd.run flipCmd st).1.sc 3 = (if st.sc 3 = 0 then 1 else 0) ∧
    (∀ y, y ≠ 3 → (Cmd.run flipCmd st).1.sc y = st.sc y) ∧ (Cmd.run flipCmd st).1.ar = st.ar ∧
    (Cmd.run flipCmd st).2 = 2 := by
  by_cases h : st.sc 3 = 0 <;> simp [flipCmd, Cmd.run_ifZero, Cmd.run_setK, h, Function.update_apply] <;>
    intro y hy <;> simp [hy]

open Classical in
/-- **The engine's zero-test contract** (convention of `zero_edge'`: `1` iff no decomposition). -/
structure ESpec (m : ℕ) (c0 : Cmd) (Tc : ℕ → ℕ) : Prop where
  keep : Keep c0
  spec : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst m x τ → Good m x τ →
    (Cmd.run c0 st).1.sc 3 = (if 0 < Zc m x τ then 0 else 1) ∧ (Cmd.run c0 st).2 ≤ Tc (encB x).length

open Classical in
/-- **The guard's contract**: the flag (scalar `3`) is `[Good]`. -/
structure GSpec (m : ℕ) (g : Cmd) (Tg : ℕ → ℕ) : Prop where
  keep : Keep g
  spec : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst m x τ →
    (Cmd.run g st).1.sc 3 = (if Good m x τ then 1 else 0) ∧ (Cmd.run g st).2 ≤ Tg (encB x).length

/-- the composite oracle -/
def wrapCmd (g c0 : Cmd) : Cmd := .seq g (.ifZero 3 .skip (.seq c0 flipCmd))

theorem zspec_of_wrap {m : ℕ} {g c0 : Cmd} {Tg Tc : ℕ → ℕ} (hg : GSpec m g Tg) (hc : ESpec m c0 Tc) :
    ZSpec m (wrapCmd g c0) (fun L => Tg L + Tc L + 6) := by
  classical
  have hf := flip_run
  refine ⟨⟨fun st i hi h3 => ?_, fun st a ha => ?_⟩, fun x st τ h0 hA h2 hc' hok => ?_⟩
  · have e1 := hg.keep.sc st i hi h3
    simp only [wrapCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize Cmd.run g st = r at e1
    by_cases hz : r.1.sc 3 = 0
    · simp [hz, Cmd.run_skip, e1]
    · simp only [hz, if_false, Cmd.run_seq]
      have e2 := hc.keep.sc r.1 i hi h3
      have e3 := (flip_run (Cmd.run c0 r.1).1).2.1 i h3
      rw [e3, e2, e1]
  · have e1 := hg.keep.ar st a ha
    simp only [wrapCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize Cmd.run g st = r at e1
    by_cases hz : r.1.sc 3 = 0
    · simp [hz, Cmd.run_skip, e1]
    · simp only [hz, if_false, Cmd.run_seq]
      have e2 := hc.keep.ar r.1 a ha
      have e3 := (flip_run (Cmd.run c0 r.1).1).2.2.1
      rw [e3, e2, e1]
  · have hconf : Conf x τ st := ⟨h0, hA, h2, hc'⟩
    obtain ⟨gv, gc⟩ := hg.spec x st τ hconf hok
    have k0 := hg.keep.sc st 0 (by norm_num) (by norm_num)
    have k2 := hg.keep.sc st 2 (by norm_num) (by norm_num)
    have a0 := hg.keep.ar st 0 (by norm_num)
    have a1 := hg.keep.ar st 1 (by norm_num)
    simp only [wrapCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize hr : Cmd.run g st = r at gv gc k0 k2 a0 a1
    by_cases hG : Good m x τ
    · have hz : r.1.sc 3 ≠ 0 := by rw [gv]; simp [hG]
      have hconf' : Conf x τ r.1 := ⟨by rw [k0, h0], by rw [a0, hA], by rw [k2, h2],
        fun j hj => by rw [a1]; exact hc' j hj⟩
      obtain ⟨cv, cc⟩ := hc.spec x r.1 τ hconf' hok hG
      simp only [hz, if_false, Cmd.run_seq]
      obtain ⟨f1, -, -, f4⟩ := flip_run (Cmd.run c0 r.1).1
      rw [f1, cv]
      refine ⟨by split_ifs <;> simp_all, ?_⟩
      omega
    · have hz : r.1.sc 3 = 0 := by rw [gv]; simp [hG]
      have hZ : ¬ 0 < Zc m x τ := fun h => hG (Zc_pos_good m x τ h)
      simp only [hz, if_true, Cmd.run_skip]
      refine ⟨by simp [hz, hZ], ?_⟩
      omega

end ECDLP.L70
