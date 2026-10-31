import ECDLP.L70_Red

/-!
# L70 / Capstone: `subexponentialRate_edge`

For every fixed `m = r + 1`, a `TM2ComputableInTime encB encOut (lexLeast m)` machine within `C_k 2^(L/k)` for
every `k`, from the following explicit hypotheses (all `Prop`s; nothing is assumed beyond them):

* `H_gate`  (`EVal`)   : an engine zero-test command `c0` (convention of `zero_edge'`) is correct on `Good` queries.
* `H_tau`              : `edge_rate`'s hypothesis `τ` for a cost function `cost : EdgeInp → ℕ`.
* `H_link`             : `c0`'s actual step count on a query is at most `cost` of the reduced edge input plus a
                         linear term (the input layer).
* `H_guard` (`GSpec`)  : a guard command decides `Good` within a sub-exponential number of steps.
-/
namespace ECDLP.L70
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

open Classical in
/-- **H_gate**: the value half of the engine contract. -/
structure EVal (m : ℕ) (c0 : Cmd) : Prop where
  keep : Keep c0
  val : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst m x τ → Good m x τ →
    (Cmd.run c0 st).1.sc 3 = (if 0 < Zc m x τ then 0 else 1)

theorem espec_of {m : ℕ} {c0 : Cmd} {Tc : ℕ → ℕ} (hv : EVal m c0)
    (hc : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst m x τ → Good m x τ →
      (Cmd.run c0 st).2 ≤ Tc (encB x).length) : ESpec m c0 Tc :=
  ⟨hv.keep, fun x st τ h1 h2 h3 => ⟨hv.val x st τ h1 h2 h3, hc x st τ h1 h2 h3⟩⟩

/-- **H_tau**: the evaluation-cost hypothesis of `edge_rate`. -/
def HTau (r : ℕ) (cost : EdgeInp → ℕ) : Prop :=
  ∃ c E : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len → cost i ≤ c * (V + 1) ^ E

/-- **H_link**: the command's steps are bounded by `cost` (of the reduced input) plus an `O(L)` input layer. -/
def HLink (r : ℕ) (c0 : Cmd) (cost : EdgeInp → ℕ) : Prop :=
  ∃ K : ℕ, ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst (r + 1) x τ → Good (r + 1) x τ →
    (Cmd.run c0 st).2 ≤ cost (redInp x τ) + K * ((encB x).length + 1)

theorem div_succ_le (L k : ℕ) (hk : 1 ≤ k) : (L + 1) / k ≤ L / k + 1 := by
  calc (L + 1) / k ≤ (L + k) / k := Nat.div_le_div_right (by omega)
    _ = L / k + 1 := by rw [Nat.add_div_right _ (by omega)]

/-- the engine's step bound as a function of the input length, sub-exponential -/
theorem engine_T (r : ℕ) (c0 : Cmd) (cost : EdgeInp → ℕ) (hτ : HTau r cost) (hl : HLink r c0 cost) :
    ∃ Tc : ℕ → ℕ, (∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → okInst (r + 1) x τ → Good (r + 1) x τ →
      (Cmd.run c0 st).2 ≤ Tc (encB x).length) ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k) := by
  classical
  have hk := edge_rate r cost hτ
  choose! C hC using hk
  obtain ⟨K, hK⟩ := hl
  set A := r + 1 + 6 with hA
  let U : ℕ → ℕ → ℕ := fun k L => C (A * k) * 2 ^ ((L + 1) / k) + K * (L + 1)
  have hU : ∀ x st τ, Conf x τ st → okInst (r + 1) x τ → Good (r + 1) x τ → ∀ k, 1 ≤ k →
      (Cmd.run c0 st).2 ≤ U k (encB x).length := by
    intro x st τ h1 h2 h3 k hk1
    have a1 := hK x st τ h1 h2 h3
    have a2 := hC (A * k) (by nlinarith) (redInp x τ) (adm_red r x τ h3)
    have a3 := len_red_le (r + 1) x τ h3
    have a4 : (redInp x τ).len / (A * k) ≤ ((encB x).length + 1) / k := by
      calc (redInp x τ).len / (A * k) ≤ (A * ((encB x).length + 1)) / (A * k) :=
            Nat.div_le_div_right (by rw [hA]; nlinarith)
        _ = ((encB x).length + 1) / k := Nat.mul_div_mul_left _ _ (by omega)
    have a5 : 2 ^ ((redInp x τ).len / (A * k)) ≤ 2 ^ (((encB x).length + 1) / k) :=
      Nat.pow_le_pow_right (by norm_num) a4
    have a6 := Nat.mul_le_mul_left (C (A * k)) a5
    show _ ≤ C (A * k) * 2 ^ (((encB x).length + 1) / k) + K * ((encB x).length + 1)
    omega
  refine ⟨fun L => ⨅ k : ℕ, U (k + 1) L, fun x st τ h1 h2 h3 => ?_, fun k hk1 => ?_⟩
  · exact le_ciInf fun k => hU x st τ h1 h2 h3 (k + 1) (by omega)
  · refine ⟨2 * C (A * k) + 2 * K * k, fun L => ?_⟩
    have h1 : (⨅ k' : ℕ, U (k' + 1) L) ≤ U k L := by
      have := ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => U (k' + 1) L)) (k - 1)
      have e : k - 1 + 1 = k := by omega
      simpa [e] using this
    refine le_trans h1 ?_
    have h2 : 2 ^ ((L + 1) / k) ≤ 2 * 2 ^ (L / k) := by
      calc 2 ^ ((L + 1) / k) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) (div_succ_le L k hk1)
        _ = 2 * 2 ^ (L / k) := by ring
    have h3 : L + 1 ≤ k * (2 * 2 ^ (L / k)) := by
      calc L + 1 ≤ k * 2 ^ ((L + 1) / k) := le_two_pow_div (L + 1) k (by omega)
        _ ≤ k * (2 * 2 ^ (L / k)) := Nat.mul_le_mul_left _ h2
    show C (A * k) * 2 ^ ((L + 1) / k) + K * (L + 1) ≤ _
    have h4 := Nat.mul_le_mul_left (C (A * k)) h2
    have h5 := Nat.mul_le_mul_left K h3
    nlinarith

/-- **The capstone** (conditional on the four explicit hypotheses). -/
theorem subexponentialRate_edge (r : ℕ) (c0 g : Cmd) (cost : EdgeInp → ℕ) (Tg : ℕ → ℕ)
    (H_gate : EVal (r + 1) c0) (H_tau : HTau r cost) (H_link : HLink r c0 cost)
    (H_guard : GSpec (r + 1) g Tg) (H_guardT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) :
    ECDLP.L61.SubexpRate (r + 1) := by
  obtain ⟨Tc, hc, hT⟩ := engine_T r c0 cost H_tau H_link
  refine subexpRate_of_zspec (r + 1) (wrapCmd g c0) _ (zspec_of_wrap H_guard (espec_of H_gate hc)) ?_
  intro k hk
  obtain ⟨C1, h1⟩ := H_guardT k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

end ECDLP.L70
