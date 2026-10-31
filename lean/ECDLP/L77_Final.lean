import ECDLP.L77_Recode
import ECDLP.L77_Cap
import ECDLP.L61_Zero

/-!
# L77 / Final: the audit statement of L35 (`Option Bool` alphabet) from the gated driver

* `opt_subexp` : `tm_of_source_opt` with a sub-exponential source-cost bound gives `C_k 2^(L/k)` on `enc`.
* `subexpEnc_of_gate_strong`, `subexponentialRate_gate_enc` : the capstones of `L77_Cap`, with conclusion exactly the statement of
  `ECDLP.subexponentialRate` (checked by `rfl` against `(ECDLP.SubexponentialRateStmt m)`).
-/
namespace ECDLP.L77
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 Turing Computability Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the statement of `ECDLP.subexponentialRate m` -/
def SubexpRateEnc (m : ℕ) : Prop :=
  ∃ M : TM2ComputableInTime ECDLP.enc encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k)

theorem subexpRateEnc_eq (m : ℕ) : SubexpRateEnc m = (ECDLP.SubexponentialRateStmt m) := rfl

theorem opt_subexp (s : Cmd) (out : ℕ) (f : Inst → Option (List Bool)) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (encB a)).ar out) = encOut (f a))
    (hS : ∀ a, srcCost s (encB a) ≤ S (ECDLP.enc a).length)
    (hSs : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, S L ≤ C * 2 ^ (L / k)) :
    ∃ M : TM2ComputableInTime ECDLP.enc encOut f, (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  obtain ⟨M, Q, k0, cc, hfin, ht⟩ := tm_of_source_opt s out f S hout hS
  refine ⟨M, hfin, fun k hk => ?_⟩
  obtain ⟨C1, hC1⟩ := hSs (12 * k) (by omega)
  refine ⟨(cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6)), fun L => ?_⟩
  rw [ht L]
  have hpoly := time_poly_aux Q k0 cc 1 (2 * L + 1) (S L) (S L) (by
    have : 1 ≤ (2 * L + 1 + 1) := by omega
    nlinarith)
  set P := 2 ^ (L / (12 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (12 * k + 1) * P := by
    have h0 := Factoring.Aux.le_two_pow_div L (12 * k) (by omega)
    rw [← hP] at h0
    have h1 : (12 * k + 1) * P = (12 * k) * P + P := by ring
    omega
  have hv : S L + 1 ≤ (C1 + 1) * P := by
    have a := hC1 L; rw [← hP] at a
    have h1 : (C1 + 1) * P = C1 * P + P := by ring
    omega
  have h0 : (2 * L + 1 + 1) ^ 6 = 64 * (L + 1) ^ 6 := by ring
  have h1 : (L + 1) ^ 6 * (S L + 1) ^ 6 ≤ ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hu 6) (Nat.pow_le_pow_left hv 6)
  have h2 : ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 =
      ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12 := by ring
  have h3 : P ^ 12 ≤ 2 ^ (L / k) := pow12_le L k
  calc _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * ((2 * L + 1 + 1) ^ 6 * (S L + 1) ^ 6) := hpoly
    _ = (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * ((L + 1) ^ 6 * (S L + 1) ^ 6)) := by rw [h0]; ring
    _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h2 ▸ h1))
    _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * 2 ^ (L / k))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3))
    _ = _ := by ring

theorem envelope_mono (C : ℕ → ℕ) : ∃ Tg : ℕ → ℕ, Monotone Tg ∧
    (∀ L v, (∀ k, 1 ≤ k → v ≤ C k * 2 ^ (L / k)) → v ≤ Tg L) ∧
    ∀ k, 1 ≤ k → ∀ L, Tg L ≤ C k * 2 ^ (L / k) := by
  refine ⟨fun L => ⨅ k : ℕ, C (k + 1) * 2 ^ (L / (k + 1)), fun L L' hLL => ?_, fun L v hv => ?_, fun k hk L => ?_⟩
  · refine le_ciInf fun k => ?_
    refine le_trans (ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => C (k' + 1) * 2 ^ (L / (k' + 1)))) k) ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right hLL))
  · exact le_ciInf fun k => hv (k + 1) (by omega)
  · have := ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => C (k' + 1) * 2 ^ (L / (k' + 1)))) (k - 1)
    have e : k - 1 + 1 = k := by omega
    simpa [e] using this

theorem len_encB_le (a : Inst) : (encB a).length ≤ 2 * (ECDLP.enc a).length + 1 := by
  obtain ⟨p, a_, b_, x, y, π⟩ := a
  rw [len_encB, len_enc]; omega

theorem E_subexp (m : ℕ) (T Tg : ℕ → ℕ)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L + drvBound m L (T L) + 2 ≤ C * 2 ^ (L / k) := by
  intro k hk
  set D := 71 * (m + 2) + 102 with hD
  have hB : ∀ L, Tg L + drvBound m L (T L) + 2 ≤ D * ((L + 1) * ((Tg L + T L) + 1)) := by
    intro L
    have h1 := drvBound_le m L (T L)
    have h2 : (L + 1) * (T L + 1) ≤ (L + 1) * ((Tg L + T L) + 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 1 ≤ (L + 1) * ((Tg L + T L) + 1) := Nat.mul_pos (by omega) (by omega)
    have h4 : Tg L + 2 ≤ 2 * ((L + 1) * ((Tg L + T L) + 1)) := by nlinarith [Nat.zero_le (L * (Tg L + T L))]
    have h5 : (71 * (m + 2) + 100) * ((L + 1) * (T L + 1)) ≤ (71 * (m + 2) + 100) * ((L + 1) * ((Tg L + T L) + 1)) :=
      Nat.mul_le_mul_left _ h2
    have h6 : D * ((L + 1) * ((Tg L + T L) + 1)) =
        (71 * (m + 2) + 100) * ((L + 1) * ((Tg L + T L) + 1)) + 2 * ((L + 1) * ((Tg L + T L) + 1)) := by
      rw [hD]; ring
    omega
  obtain ⟨C1, hC1⟩ := hT (2 * k) (by omega)
  obtain ⟨C2, hC2⟩ := hTg (2 * k) (by omega)
  refine ⟨D * ((2 * k + 1) * (C1 + C2 + 1)), fun L => ?_⟩
  refine le_trans (hB L) ?_
  set P := 2 ^ (L / (2 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (2 * k + 1) * P := by
    have h0 := Factoring.Aux.le_two_pow_div L (2 * k) (by omega)
    rw [← hP] at h0
    have h1 : (2 * k + 1) * P = (2 * k) * P + P := by ring
    omega
  have hv : (Tg L + T L) + 1 ≤ (C1 + C2 + 1) * P := by
    have a := hC1 L; have b := hC2 L; rw [← hP] at a b
    have h1 : (C1 + C2 + 1) * P = C1 * P + C2 * P + P := by ring
    omega
  have h3 : P * P ≤ 2 ^ (L / k) := by
    have h := Factoring.Aux.mul_div_mul_le 2 k L
    calc P * P = 2 ^ (2 * (L / (2 * k))) := by rw [hP, ← pow_add]; ring_nf
      _ ≤ 2 ^ (L / k) := Nat.pow_le_pow_right (by norm_num) h
  calc D * ((L + 1) * ((Tg L + T L) + 1)) ≤ D * (((2 * k + 1) * P) * ((C1 + C2 + 1) * P)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hu hv)
    _ = D * ((2 * k + 1) * (C1 + C2 + 1)) * (P * P) := by ring
    _ ≤ D * ((2 * k + 1) * (C1 + C2 + 1)) * 2 ^ (L / k) := Nat.mul_le_mul_left _ h3

/-- the sub-exponential source cost of the gated driver, as a function of `|enc x|`, gives the machine on `enc`. -/
theorem subexpEnc_of_gate (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ) (F : Inst → Prop)
    (hG : GateSpec F G fl Tg) (hc : ZSpecAt F m c T) (hnec : ∀ x, ¬ F x → lexLeast m x = none)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) : SubexpRateEnc m := by
  classical
  choose! C hC using E_subexp m T Tg hT hTg
  obtain ⟨Eb, hmono, hE1, hE2⟩ := envelope_mono C
  refine opt_subexp (topCmd G fl m c) 2 (lexLeast m) (fun L => Eb (2 * L + 1))
    (fun a => (top_out m c G fl T Tg F hG hc hnec a).1) (fun a => ?_) (fun k hk => ?_)
  · refine le_trans (top_out m c G fl T Tg F hG hc hnec a).2 ?_
    refine le_trans (hE1 _ _ (fun k hk => hC k hk _)) ?_
    exact hmono (len_encB_le a)
  · refine ⟨2 * C (2 * k), fun L => ?_⟩
    refine le_trans (hE2 (2 * k) (by omega) (2 * L + 1)) ?_
    have h1 : (2 * L + 1) / (2 * k) ≤ L / k + 1 := by
      calc (2 * L + 1) / (2 * k) ≤ (2 * (L + k)) / (2 * k) := Nat.div_le_div_right (by omega)
        _ = (L + k) / k := Nat.mul_div_mul_left _ _ (by omega)
        _ = L / k + 1 := by rw [Nat.add_div_right _ (by omega)]
    have h2 : 2 ^ ((2 * L + 1) / (2 * k)) ≤ 2 * 2 ^ (L / k) :=
      calc 2 ^ ((2 * L + 1) / (2 * k)) ≤ 2 ^ (L / k + 1) := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 * 2 ^ (L / k) := by ring
    calc C (2 * k) * 2 ^ ((2 * L + 1) / (2 * k)) ≤ C (2 * k) * (2 * 2 ^ (L / k)) := Nat.mul_le_mul_left _ h2
      _ = 2 * C (2 * k) * 2 ^ (L / k) := by ring

/-- **Non-vacuity.**  The whole pipeline (gate, driver, recoding machine) at `m = 0`, unconditionally: a machine on `enc`. -/
theorem subexponentialRate_zero_enc : SubexpRateEnc 0 := by
  have hG : GateSpec (fun _ => True) (.setK 20 1) 20 (fun _ => 1) := by
    refine ⟨fun x => ?_⟩
    simp [Cmd.run_setK, St.init]
  have hc : ZSpecAt (fun _ => True) 0 c0 (fun _ => 1) :=
    ⟨zspec_zero.keep, fun x st τ _ h0 hA h2 hc' hok => zspec_zero.spec x st τ h0 hA h2 hc' hok⟩
  refine subexpEnc_of_gate 0 c0 _ 20 (fun _ => 1) (fun _ => 1) (fun _ => True) hG hc
    (fun x hx => absurd trivial hx) ?_ ?_
  · intro k _; exact ⟨1, fun L => by simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ (L / k))⟩
  · intro k _; exact ⟨1, fun L => by simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ (L / k))⟩

/-- **Capstone for L35's statement (strong form, no per-call guard).** -/
theorem subexponentialRate_gate_strong_enc (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ)
    (hG : GateSpec Gx G fl Tg) (hc : ZSpecAt Gx m c T)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) : SubexpRateEnc m :=
  subexpEnc_of_gate m c G fl T Tg Gx hG hc (hnec m) hT hTg

/-- **The capstone for L35's `subexponentialRate`**, conditional on the engine (EVal, HTau, HLink), the per-call length test (LSpec)
and the input layer (HookSpec). -/
theorem subexponentialRate_gate_enc (r : ℕ) (c0 lg H : Cmd) (cost : EdgeInp → ℕ) (Tl Th : ℕ → ℕ) (S q fl fl2 : ℕ)
    (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (hfl : 10 ≤ fl)
    (H_gate : EVal (r + 1) c0) (H_tau : HTau r cost) (H_link : HLink r c0 cost)
    (H_len : LSpec (r + 1) lg Tl) (H_lenT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tl L ≤ C * 2 ^ (L / k))
    (H_hook : HookSpec (fun x => x.1.Prime) Gx2 H fl2 Th)
    (H_hookT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Th L ≤ C * 2 ^ (L / k)) :
    SubexpRateEnc (r + 1) := by
  obtain ⟨Tc, hc, hT⟩ := engine_T r c0 cost H_tau H_link
  obtain ⟨Tg, hG, hTg⟩ := gate_hook S q hS hq1 hqS Gx2 H fl fl2 hfl Th H_hook
  have hz := zspecAt_of_wrap H_len (espec_of H_gate hc)
  refine subexponentialRate_gate_strong_enc (r + 1) _ _ fl _ Tg hG hz ?_ (hTg H_hookT)
  intro k hk
  obtain ⟨C1, h1⟩ := H_lenT k hk
  obtain ⟨C2, h2⟩ := hT k hk
  refine ⟨C1 + C2 + 6, fun L => ?_⟩
  have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
  have := h1 L
  have := h2 L
  nlinarith

end ECDLP.L77
