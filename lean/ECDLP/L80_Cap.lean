import ECDLP.L80_Orc
import ECDLP.L77_Cap
import ECDLP.L69_Tau

/-!
# L80 / Cap: the per-call oracle `oraC` as an `ESpec`, and the capstone with the one-time gate
Hypotheses on the (abstract) engine command `eng` (run in the frame at `S`):
* `EngVal r eng` : on every state satisfying the layout predicate `FrameIn`, `sc 3` is `[no decomposition]` (the content of L64/L68 `zero_edge'`).
* `EngCost r eng` : the state-generic cost bound (this is exactly the shape of L69 `uniC_cost'`: only `sc 0`, `sc 2 < sc 0` are used).
-/
namespace ECDLP.L80
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L60 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

open Classical in
def EngVal (r : ℕ) (eng : Cmd) : Prop :=
  ∀ (x : Inst) (τ : List Bool), ECDLP.L70.Good (r + 1) x τ → ∀ s : St, FrameIn r (redInp x τ) s →
    (Cmd.run eng s).1.sc 3 = (if 0 < Zc (r + 1) x τ then 0 else 1)

def EngCost (r : ℕ) (eng : Cmd) : Prop :=
  ∃ c E : ℕ, ∀ (V : ℕ) (i : EdgeInp), i.adm r → (edgeFamily r).UniReq V i.len → ∀ s : St, s.sc 0 = i.len →
    s.sc 2 < s.sc 0 → (Cmd.run eng s).2 ≤ c * (V + 1) ^ E

theorem engRate (r : ℕ) (eng : Cmd) (h : EngCost r eng) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ i : EdgeInp, i.adm r → ∀ s : St, s.sc 0 = i.len → s.sc 2 < s.sc 0 →
      (Cmd.run eng s).2 ≤ C * 2 ^ (i.len / k) := by
  obtain ⟨c, E, hc⟩ := h
  obtain ⟨Z, hR, hZ⟩ := NetFamily.uniReq_expG (edgeFamily_spec r)
  intro k hk
  obtain ⟨C, hC⟩ := hZ ((E + 1) * k) (by nlinarith)
  refine ⟨c * 2 ^ (E * (C + 1)), fun i hi s h0 h2 => ?_⟩
  calc (Cmd.run eng s).2 ≤ c * (2 ^ Z i.len + 1) ^ E := hc _ i hi (hR _) s h0 h2
    _ ≤ c * (2 ^ (E * (C + 1)) * 2 ^ (i.len / k)) :=
        Nat.mul_le_mul_left _ (pow_absorb E k C i.len (Z i.len) hk (hC _))
    _ = c * 2 ^ (E * (C + 1)) * 2 ^ (i.len / k) := by ring

theorem PB_subexp (m k : ℕ) (hk : 1 ≤ k) : ∃ C : ℕ, ∀ L, PB m L ≤ C * 2  ^ (L / k) := by
  obtain ⟨C, hC⟩ := poly_subexp 3 k hk
  have hle : ∀ L, 8 + (m + 2) * L ≤ (m + 10) * (L + 1) := fun L => by nlinarith
  have hle2 : ∀ L, (8 + (m + 2) * L) + m * (L + 1) + 2 ≤ (2 * m + 12) * (L + 1) := fun L => by nlinarith
  refine ⟨(400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3001 + 10000 * (2 * m + 12) ^ 2) * C, fun L => ?_⟩
  have h1 := hC L
  have p1 : 1 ≤ (L + 1) := by omega
  have e1 : (8 + (m + 2) * L) ^ 3 ≤ (m + 10) ^ 3 * (L + 1) ^ 3 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (hle L) 3
  have e2 : (8 + (m + 2) * L) ^ 2 ≤ (m + 10) ^ 2 * (L + 1) ^ 3 := by
    calc (8 + (m + 2) * L) ^ 2 ≤ ((m + 10) * (L + 1)) ^ 2 := Nat.pow_le_pow_left (hle L) 2
      _ = (m + 10) ^ 2 * (L + 1) ^ 2 := by rw [mul_pow]
      _ ≤ (m + 10) ^ 2 * (L + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right p1 (by norm_num))
  have e3 : 8 + (m + 2) * L ≤ (m + 10) * (L + 1) ^ 3 := by
    calc 8 + (m + 2) * L ≤ (m + 10) * (L + 1) := hle L
      _ ≤ (m + 10) * (L + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have e4 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ p1
  have e5 : ((8 + (m + 2) * L) + m * (L + 1) + 2) ^ 2 ≤ (2 * m + 12) ^ 2 * (L + 1) ^ 3 := by
    calc ((8 + (m + 2) * L) + m * (L + 1) + 2) ^ 2 ≤ ((2 * m + 12) * (L + 1)) ^ 2 := Nat.pow_le_pow_left (hle2 L) 2
      _ = (2 * m + 12) ^ 2 * (L + 1) ^ 2 := by rw [mul_pow]
      _ ≤ (2 * m + 12) ^ 2 * (L + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right p1 (by norm_num))
  unfold PB
  have f1 := Nat.mul_le_mul_left (400 * m) e1
  have f2 := Nat.mul_le_mul_left (13000 * m) e2
  have f3 := Nat.mul_le_mul_left (4000 * m) e3
  have f5 := Nat.mul_le_mul_left 10000 e5
  have g : (400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3001 + 10000 * (2 * m + 12) ^ 2) * (L + 1) ^ 3 ≤
      (400 * m * (m + 10) ^ 3 + 13000 * m * (m + 10) ^ 2 + 4000 * m * (m + 10) + 3001 + 10000 * (2 * m + 12) ^ 2) * (C * 2 ^ (L / k)) :=
    Nat.mul_le_mul_left _ h1
  nlinarith [f1, f2, f3, f5, g, e4]

set_option maxHeartbeats 4000000 in
theorem oracle_spec (r S : ℕ) (hS : 1400 ≤ S) (eng : Cmd) (hv : EngVal r eng) (hc : EngCost r eng) :
    ∃ Tc : ℕ → ℕ, ESpec (r + 1) (oraC (r + 1) S eng) Tc ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k) := by
  classical
  have hk := engRate r eng hc
  choose! C hC using hk
  set A := r + 1 + 6 with hA
  let U : ℕ → ℕ → ℕ := fun k L => PB (r + 1) L + C (A * k) * 2 ^ ((L + 1) / k) + 10
  have hU : ∀ (x : Inst) (st : St) (τ : List Bool), Conf x τ st → ECDLP.L70.Good (r + 1) x τ → ∀ k, 1 ≤ k →
      (Cmd.run (oraC (r + 1) S eng) st).2 ≤ U k (encB x).length := by
    intro x st τ hconf hgood k hk1
    obtain ⟨hF, hcost, -, -⟩ := pre_frame r S hS x τ st hconf hgood
    have hrun := run_shift S eng
    generalize hX : Cmd.run (checkC (r + 1)) st = X
    generalize hY : Cmd.run (frameW S) X.1 = Y
    generalize hZ : Cmd.run (eng.shift S) Y.1 = Z
    have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW S)) st = (Y.1, X.2 + Y.2 + 1) := by
      simp only [Cmd.run_seq, hX, hY]
    rw [hs2] at hF hcost
    simp only at hF hcost
    have hZ2 : Z.2 = (Cmd.run eng (unshift S Y.1)).2 := by
      have := (hrun Y.1).2.1
      rw [← hZ]; exact this
    have hlen := len_red_le (r + 1) x τ hgood
    have hadm := adm_red r x τ hgood
    obtain ⟨hF0, hF2, -⟩ := hF
    have hF2' : (unshift S Y.1).sc 2 < (unshift S Y.1).sc 0 := by
      rw [hF2, hF0]; unfold EdgeInp.len; omega
    have hAk : 1 ≤ A * k := by nlinarith
    have a2 := hC (A * k) hAk (redInp x τ) hadm (unshift S Y.1) hF0 hF2'
    have a4 : (redInp x τ).len / (A * k) ≤ ((encB x).length + 1) / k := by
      calc (redInp x τ).len / (A * k) ≤ (A * ((encB x).length + 1)) / (A * k) :=
            Nat.div_le_div_right (by rw [hA]; nlinarith)
        _ = ((encB x).length + 1) / k := Nat.mul_div_mul_left _ _ (by omega)
    have a5 : 2 ^ ((redInp x τ).len / (A * k)) ≤ 2 ^ (((encB x).length + 1) / k) :=
      Nat.pow_le_pow_right (by norm_num) a4
    have a6 := Nat.mul_le_mul_left (C (A * k)) a5
    have hcopy : (Cmd.run (oraC (r + 1) S eng) st).2 = X.2 + (Y.2 + (Z.2 + 1 + 1) + 1) + 1 := by
      simp only [oraC, Cmd.run_seq, Cmd.run_copy, hX, hY, hZ]
    show _ ≤ PB (r + 1) (encB x).length + C (A * k) * 2 ^ (((encB x).length + 1) / k) + 10
    rw [hcopy]
    omega
  refine ⟨fun L => ⨅ k : ℕ, U (k + 1) L, ⟨oraC_keep (r + 1) S hS eng, fun x st τ hconf hok hgood => ?_⟩, fun k hk1 => ?_⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨hF, -, -, -⟩ := pre_frame r S hS x τ st hconf hgood
      generalize hX : Cmd.run (checkC (r + 1)) st = X
      generalize hY : Cmd.run (frameW S) X.1 = Y
      generalize hZ : Cmd.run (eng.shift S) Y.1 = Z
      have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW S)) st = (Y.1, X.2 + Y.2 + 1) := by
        simp only [Cmd.run_seq, hX, hY]
      rw [hs2] at hF
      simp only at hF
      have h3 : (Cmd.run (oraC (r + 1) S eng) st).1.sc 3 = Z.1.sc (S + 3) := by
        simp only [oraC, Cmd.run_seq, Cmd.run_copy, hX, hY, hZ, St.setSc_sc, Function.update_self]
      rw [h3]
      have := (run_shift S eng Y.1).1
      rw [hZ] at this
      have e : Z.1.sc (S + 3) = (unshift S Z.1).sc 3 := rfl
      rw [e, this]
      exact hv x τ hgood _ hF
    · exact le_ciInf fun k => hU x st τ hconf hgood (k + 1) (by omega)
  · obtain ⟨Cp, hCp⟩ := PB_subexp (r + 1) k hk1
    refine ⟨Cp + 2 * C (A * k) + 10, fun L => ?_⟩
    have h1 : (⨅ k' : ℕ, U (k' + 1) L) ≤ U k L := by
      have := ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => U (k' + 1) L)) (k - 1)
      have e : k - 1 + 1 = k := by omega
      simpa [e] using this
    refine le_trans h1 ?_
    have h2 : 2 ^ ((L + 1) / k) ≤ 2 * 2 ^ (L / k) := by
      calc 2 ^ ((L + 1) / k) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) (div_succ_le L k hk1)
        _ = 2 * 2 ^ (L / k) := by ring
    have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    have h4 := Nat.mul_le_mul_left (C (A * k)) h2
    have h5 := hCp L
    show PB (r + 1) L + C (A * k) * 2 ^ ((L + 1) / k) + 10 ≤ _
    nlinarith

end ECDLP.L80
