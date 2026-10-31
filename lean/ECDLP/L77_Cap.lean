import ECDLP.L77_Gate

/-!
# L77 / Cap: L70's capstone restated with the one-time gate

Hypotheses (all explicit `Prop`s):
* `EVal`, `HTau`, `HLink` : unchanged from L70 (engine zero test on `Good` queries, its cost).
* `LSpec` : the only per-call guard left, the LENGTH test `|τ| ≤ nlen` (needs `nlen` = `m (size ⌈p^(1/m)⌉ + 1)`), on instances with `Gx x`.
  (If the engine itself returns count `0` on over-long prefixes, use `subexponentialRate_gate_strong`, which has no per-call guard.)
* `HookSpec` : L76's input-layer checks (`Δ ≠ 0`, `R` nonsingular), run ONCE after L71's primality guard.
`subexponentialRate_gate` : `L61.SubexpRate (r+1)`, the `encB` version of `subexponentialRate`.
-/
namespace ECDLP.L77
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

open Classical in
/-- **The per-call length guard**, on `Gx` instances only. -/
structure LSpec (m : ℕ) (g : Cmd) (Tg : ℕ → ℕ) : Prop where
  keep : Keep g
  spec : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst m x τ → Gx x →
    (Cmd.run g st).1.sc 3 = (if τ.length ≤ nlen m x then 1 else 0) ∧ (Cmd.run g st).2 ≤ Tg (encB x).length

theorem zspecAt_of_wrap {m : ℕ} {g c0 : Cmd} {Tg Tc : ℕ → ℕ} (hg : LSpec m g Tg) (hc : ESpec m c0 Tc) :
    ZSpecAt Gx m (wrapCmd g c0) (fun L => Tg L + Tc L + 6) := by
  classical
  refine ⟨⟨fun st i hi h3 => ?_, fun st a ha => ?_⟩, fun x st τ hGx h0 hA h2 hc' hok => ?_⟩
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
    obtain ⟨gv, gc⟩ := hg.spec x st τ hconf hok hGx
    have k0 := hg.keep.sc st 0 (by norm_num) (by norm_num)
    have k2 := hg.keep.sc st 2 (by norm_num) (by norm_num)
    have a0 := hg.keep.ar st 0 (by norm_num)
    have a1 := hg.keep.ar st 1 (by norm_num)
    simp only [wrapCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize hr : Cmd.run g st = r at gv gc k0 k2 a0 a1
    by_cases hG : τ.length ≤ nlen m x
    · have hG' : Good m x τ := (good_iff m x τ).2 ⟨hGx, hG⟩
      have hz : r.1.sc 3 ≠ 0 := by rw [gv]; simp [hG]
      have hconf' : Conf x τ r.1 := ⟨by rw [k0, h0], by rw [a0, hA], by rw [k2, h2],
        fun j hj => by rw [a1]; exact hc' j hj⟩
      obtain ⟨cv, cc⟩ := hc.spec x r.1 τ hconf' hok hG'
      simp only [hz, if_false, Cmd.run_seq]
      obtain ⟨f1, -, -, f4⟩ := flip_run (Cmd.run c0 r.1).1
      rw [f1, cv]
      refine ⟨by split_ifs <;> simp_all, ?_⟩
      omega
    · have hz : r.1.sc 3 = 0 := by rw [gv]; simp [hG]
      have hZ : ¬ 0 < Zc m x τ := fun h => hG ((good_iff m x τ).1 (Zc_pos_good m x τ h)).2
      simp only [hz, if_true, Cmd.run_skip]
      refine ⟨by simp [hz, hZ], ?_⟩
      omega

theorem hnec (m : ℕ) : ∀ x, ¬ Gx x → lexLeast m x = none := lexLeast_none_of_not_Gx m

/-- **Strong form (no per-call guard):** gate `G` (one-time) and an oracle that is correct on `Gx` instances for all queries
the driver asks, including over-long ones. -/
theorem subexponentialRate_gate_strong (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ)
    (hG : GateSpec Gx G fl Tg) (hc : ZSpecAt Gx m c T)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) : SubexpRate m :=
  top_subexp m c G fl T Tg Gx hG hc (hnec m) hT hTg

/-- **The capstone with the one-time gate.** -/
theorem subexponentialRate_gate (r : ℕ) (c0 lg H : Cmd) (cost : EdgeInp → ℕ) (Tl Th : ℕ → ℕ) (S q fl fl2 : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_gate : EVal (r + 1) c0) (H_tau : HTau r cost) (H_link : HLink r c0 cost)
    (H_len : LSpec (r + 1) lg Tl) (H_lenT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tl L ≤ C * 2 ^ (L / k))
    (H_hook : HookSpec (fun x => x.1.Prime) Gx2 H fl2 Th)
    (H_hookT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Th L ≤ C * 2 ^ (L / k)) :
    SubexpRate (r + 1) := by
  obtain ⟨Tc, hc, hT⟩ := engine_T r c0 cost H_tau H_link
  obtain ⟨Tg, hG, hTg⟩ := gate_hook S q hS hq1 hqS Gx2 H fl fl2 hfl Th H_hook
  have hz := zspecAt_of_wrap H_len (espec_of H_gate hc)
  refine subexponentialRate_gate_strong (r + 1) _ _ fl _ Tg hG hz ?_ (hTg H_hookT)
  intro k hk
  obtain ⟨C1, h1⟩ := H_lenT k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

end ECDLP.L77
