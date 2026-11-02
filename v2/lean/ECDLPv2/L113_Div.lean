import ECDLPv2.L113_Loop

/-!
# L113 / Div: restoring division of bit-array numbers (one turn)
Arrays: numerator `Nn`, divisor `Dd`, quotient `Q`, remainder `R`, temp `TM`, constant one `ONE`.  Scalars `830` (turn), `831` (cell index `n - c`),
`832` (bit), `833` (inner counter), `834` (quotient flag), `835` (= 1, a constant).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

/-- rewriting one cell of a bit array -/
theorem V_update_at (f : ℕ → ℕ) (n p v : ℕ) (hp : 1 ≤ p) (hpn : p ≤ n) (hv : v ≤ 1) :
    V (Function.update f p v) n + bt f p * 2 ^ (p - 1) = V f n + v * 2 ^ (p - 1) := by
  induction n, hpn using Nat.le_induction with
  | base =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [V_snoc, V_snoc]
    have e : V (Function.update f (q + 1) v) q = V f q :=
      V_congr fun i _ hi => by simp [Function.update_apply, show i ≠ q + 1 by omega]
    have e2 : bt (Function.update f (q + 1) v) (q + 1) = v := by
      simp only [bt, Function.update_self]; split_ifs <;> omega
    rw [e, e2]; simp; ring
  | succ n hn ih =>
    rw [V_snoc, V_snoc]
    have e2 : bt (Function.update f p v) (n + 1) = bt f (n + 1) := by
      simp [bt, Function.update_apply, show n + 1 ≠ p by omega]
    rw [e2]
    nlinarith [ih]

/-- scalar 831 := scalar 710 - scalar 830 (as `decr`s) -/
def idxC : Cmd := .seq (.copy 831 710) (.loop 830 833 (.decr 831))

theorem idxC_run (s : St) (n c : ℕ) (hW : s.sc 710 = n) (hc : s.sc 830 = c) :
    (Cmd.run idxC s).1.sc 831 = n - c ∧ (∀ y, y ≠ 831 → y ≠ 833 → (Cmd.run idxC s).1.sc y = s.sc y) ∧
    (Cmd.run idxC s).1.ar = s.ar ∧ (Cmd.run idxC s).2 ≤ 2 * c + 4 := by
  set s1 := s.setSc 831 (s.sc 710) with hs1
  have e830 : s1.sc 830 = c := by simp [hs1, St.setSc, hc]
  let P : ℕ → St → Prop := fun i t => t.sc 831 = n - i ∧ (∀ y, y ≠ 831 → y ≠ 833 → t.sc y = s.sc y) ∧ t.ar = s.ar
  have h0 : P 0 s1 := ⟨by simp [hs1, St.setSc, hW], fun y h1 h2 => by simp [hs1, St.setSc, Function.update_of_ne h1], rfl⟩
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (.decr 831) (t.setSc 833 i)).1 ∧ (Cmd.run (.decr 831) (t.setSc 833 i)).2 ≤ 1 := by
    intro i t ⟨p1, p2, p3⟩
    refine ⟨⟨?_, fun y h1 h2 => ?_, ?_⟩, by simp [Cmd.run_decr]⟩
    · simp [Cmd.run_decr, St.setSc, p1]; omega
    · simp [Cmd.run_decr, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2]; exact p2 y h1 h2
    · simp [Cmd.run_decr, St.setSc, p3]
  have hI := Cmd.loop_inv (b := 830) (c := 833) (body := .decr 831) (st := s1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 830) (c := 833) (body := .decr 831) (st := s1) P 1 h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  rw [e830] at hI hC
  have hr : Cmd.run idxC s = ((Cmd.run (.loop 830 833 (.decr 831)) s1).1, 1 + (Cmd.run (.loop 830 833 (.decr 831)) s1).2 + 1) := by
    simp [idxC, Cmd.run_seq, Cmd.run_copy, hs1]
  rw [hr]
  obtain ⟨a1, a2, a3⟩ := hI
  refine ⟨a1, a2, a3, ?_⟩
  simp only; omega

/-- `R := 2 R + [Nn cell idx ≠ 0]`, `idx` in scalar 831 -/
def shiftIn (Nn R TM ONE : ℕ) : Cmd :=
  .seq (copyA TM R) <| .seq (addC false R TM) <| .seq (.rd 832 Nn 831 0) (.ifZero 832 .skip (addC false R ONE))

/-- scalars written by `shiftIn` -/
def Zs (y : ℕ) : Prop := (721 ≤ y ∧ y ≤ 799) ∨ y = 832

theorem shiftIn_run (Nn R TM ONE : ℕ) (hRT : R ≠ TM) (hRO : R ≠ ONE) (hNR : Nn ≠ R) (hNT : Nn ≠ TM) (hOT : ONE ≠ TM)
    (s : St) (n idx : ℕ) (hW : s.sc 710 = n) (hi : s.sc 831 = idx) (hO : V (s.ar ONE) n = 1)
    (hlt : 2 * V (s.ar R) n + 1 < 2 ^ n) :
    V ((Cmd.run (shiftIn Nn R TM ONE) s).1.ar R) n = 2 * V (s.ar R) n + bt (s.ar Nn) idx ∧
    (∀ a, a ≠ R → a ≠ TM → (Cmd.run (shiftIn Nn R TM ONE) s).1.ar a = s.ar a) ∧
    (∀ y, ¬ Zs y → (Cmd.run (shiftIn Nn R TM ONE) s).1.sc y = s.sc y) ∧
    (Cmd.run (shiftIn Nn R TM ONE) s).2 ≤ 57 * n + 30 := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := copyA_run TM R (Ne.symm hRT) s n hW
  generalize hs1 : Cmd.run (copyA TM R) s = s1 at b1 b2 b3 b4 b5 b6
  have w1 : s1.1.sc 710 = n := by rw [b5 710 (by unfold ZC; omega)]; exact hW
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := add_run R TM hRT s1.1 n w1
  generalize hs2 : Cmd.run (addC false R TM) s1.1 = s2 at a1 a2 a3 a4 a5 a6
  have w2 : s2.1.sc 710 = n := by rw [a5 710 (by unfold ZA; omega), w1]
  have r1 : s1.1.ar R = s.ar R := b4 R hRT
  have r2 : V (s1.1.ar TM) n = V (s.ar R) n := b3
  rw [r1, r2] at a2
  have c0 : s2.1.sc 722 = 0 := by
    by_contra hne
    have : 2 ^ n ≤ s2.1.sc 722 * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [c0] at a2
  have vR2 : V (s2.1.ar R) n = 2 * V (s.ar R) n := by omega
  have g831 : s2.1.sc 831 = idx := by rw [a5 831 (by unfold ZA; omega), b5 831 (by unfold ZC; omega), hi]
  have nn2 : s2.1.ar Nn = s.ar Nn := by rw [a4 Nn hNR, b4 Nn hNT]
  have oo2 : s2.1.ar ONE = s.ar ONE := by rw [a4 ONE (Ne.symm hRO), b4 ONE hOT]
  set s3 := s2.1.setSc 832 (s2.1.ar Nn (s2.1.sc 831 + 0)) with hs3
  have c832 : s3.sc 832 = s.ar Nn idx := by simp [hs3, St.setSc, g831, nn2]
  have w3 : s3.sc 710 = n := by simp [hs3, St.setSc, Function.update_of_ne (show (710:ℕ) ≠ 832 by norm_num), w2]
  have ar3 : s3.ar = s2.1.ar := rfl
  have hrun : Cmd.run (shiftIn Nn R TM ONE) s = (( Cmd.run (.ifZero 832 .skip (addC false R ONE)) s3).1,
      s1.2 + (s2.2 + (1 + (Cmd.run (.ifZero 832 .skip (addC false R ONE)) s3).2 + 1) + 1) + 1) := by
    simp only [shiftIn, Cmd.run_seq, Cmd.run_rd, hs1, hs2]; rfl
  rw [hrun]
  by_cases hz : s.ar Nn idx = 0
  · have : s3.sc 832 = 0 := by rw [c832, hz]
    simp only [Cmd.run_ifZero, this, if_true, Cmd.run_skip]
    refine ⟨?_, fun a h1 h2 => ?_, fun y hy => ?_, ?_⟩
    · simp only [ar3]; rw [vR2]; simp [bt, hz]
    · simp only [ar3]; rw [a4 a h1, b4 a h2]
    · have h1 : ¬ ZC y := fun h => hy (Or.inl (by unfold ZC at h; exact ⟨by omega, by omega⟩))
      have h2 : ¬ ZA y := fun h => hy (Or.inl (by unfold ZA at h; exact ⟨by omega, by omega⟩))
      have h3 : y ≠ 832 := fun h => hy (Or.inr h)
      simp only [hs3, St.setSc_sc, Function.update_of_ne h3]
      rw [a5 y h2, b5 y h1]
    · omega
  · have : s3.sc 832 ≠ 0 := by rw [c832]; exact hz
    simp only [Cmd.run_ifZero, this, if_false]
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := add_run R ONE hRO s3 n w3
    simp only [ar3] at d2
    rw [oo2, hO, vR2] at d2
    have c1 : (Cmd.run (addC false R ONE) s3).1.sc 722 = 0 := by
      by_contra hne
      have : 2 ^ n ≤ (Cmd.run (addC false R ONE) s3).1.sc 722 * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [c1] at d2
    refine ⟨?_, fun a h1 h2 => ?_, fun y hy => ?_, ?_⟩
    · have : bt (s.ar Nn) idx = 1 := by simp [bt, hz]
      rw [this]; omega
    · rw [d4 a h1]; simp only [ar3]; rw [a4 a h1, b4 a h2]
    · have h1 : ¬ ZC y := fun h => hy (Or.inl (by unfold ZC at h; exact ⟨by omega, by omega⟩))
      have h2 : ¬ ZA y := fun h => hy (Or.inl (by unfold ZA at h; exact ⟨by omega, by omega⟩))
      have h3 : y ≠ 832 := fun h => hy (Or.inr h)
      rw [d5 y h2]
      simp only [hs3, St.setSc_sc, Function.update_of_ne h3]
      rw [a5 y h2, b5 y h1]
    · omega

/-- compare `R` with `Dd`, subtract if `Dd ≤ R`, set quotient cell `idx` (scalar 831) -/
def cmpSub (Dd Q R TM : ℕ) : Cmd :=
  .seq (geC TM R Dd) <| .seq (.copy 834 722) <| .seq (condSub R Dd TM) (.ifZero 834 .skip (.wr Q 831 0 835))

def Zc2 (y : ℕ) : Prop := (721 ≤ y ∧ y ≤ 799) ∨ y = 834

theorem cmpSub_run (Dd Q R TM : ℕ) (hRT : R ≠ TM) (hRD : R ≠ Dd) (hTD : TM ≠ Dd) (hQR : Q ≠ R) (hQT : Q ≠ TM)
    (s : St) (n idx Dv : ℕ) (hW : s.sc 710 = n) (hi : s.sc 831 = idx) (hidx : 1 ≤ idx ∧ idx ≤ n) (h835 : s.sc 835 = 1)
    (hDv : V (s.ar Dd) n = Dv) (hq0 : bt (s.ar Q) idx = 0) :
    V ((Cmd.run (cmpSub Dd Q R TM) s).1.ar R) n = (if Dv ≤ V (s.ar R) n then V (s.ar R) n - Dv else V (s.ar R) n) ∧
    V ((Cmd.run (cmpSub Dd Q R TM) s).1.ar Q) n = V (s.ar Q) n + (if Dv ≤ V (s.ar R) n then 2 ^ (idx - 1) else 0) ∧
    (∀ a, a ≠ R → a ≠ TM → a ≠ Q → (Cmd.run (cmpSub Dd Q R TM) s).1.ar a = s.ar a) ∧
    (∀ y, ¬ Zc2 y → (Cmd.run (cmpSub Dd Q R TM) s).1.sc y = s.sc y) ∧
    (Cmd.run (cmpSub Dd Q R TM) s).2 ≤ 110 * n + 60 := by
  obtain ⟨g1, g2, g3, g4⟩ := geC_run TM R Dd (Ne.symm hRT) hTD s n hW
  generalize hv1 : Cmd.run (geC TM R Dd) s = v1 at g1 g2 g3 g4
  have w1 : v1.1.sc 710 = n := by rw [g3 710 (by unfold ZB ZA ZC; omega)]; exact hW
  have a1 : ∀ a, a ≠ TM → v1.1.ar a = s.ar a := fun a ha => g2 a (fun h => ha h)
  set v2 := v1.1.setSc 834 (v1.1.sc 722) with hv2
  have w2 : v2.sc 710 = n := by simp [hv2, St.setSc, Function.update_of_ne (show (710:ℕ) ≠ 834 by norm_num), w1]
  have f834 : v2.sc 834 = if V (s.ar Dd) n ≤ V (s.ar R) n then 1 else 0 := by simp [hv2, St.setSc, g1]
  have ar2 : v2.ar = v1.1.ar := rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := condSub_run R Dd TM hRD hRT (Ne.symm hTD) v2 n w2
  generalize hv3 : Cmd.run (condSub R Dd TM) v2 = v3 at h1 h2 h3 h4 h5
  have eD : v2.ar Dd = s.ar Dd := by rw [ar2]; exact a1 Dd (Ne.symm hTD)
  have eR : v2.ar R = s.ar R := by rw [ar2]; exact a1 R hRT
  rw [eD, eR, hDv] at h2
  have w3 : v3.1.sc 710 = n := by rw [h4 710 (by unfold ZB ZA ZC; omega), w2]
  have c834 : v3.1.sc 834 = if Dv ≤ V (s.ar R) n then 1 else 0 := by
    rw [h4 834 (by unfold ZB ZA ZC; omega), f834, hDv]
  have c831 : v3.1.sc 831 = idx := by
    rw [h4 831 (by unfold ZB ZA ZC; omega)]; simp [hv2, St.setSc, Function.update_of_ne (show (831:ℕ) ≠ 834 by norm_num)]
    rw [g3 831 (by unfold ZB ZA ZC; omega), hi]
  have c835 : v3.1.sc 835 = 1 := by
    rw [h4 835 (by unfold ZB ZA ZC; omega)]; simp [hv2, St.setSc, Function.update_of_ne (show (835:ℕ) ≠ 834 by norm_num)]
    rw [g3 835 (by unfold ZB ZA ZC; omega), h835]
  have hrun : Cmd.run (cmpSub Dd Q R TM) s = ((Cmd.run (.ifZero 834 .skip (.wr Q 831 0 835)) v3.1).1,
      v1.2 + (1 + (v3.2 + (Cmd.run (.ifZero 834 .skip (.wr Q 831 0 835)) v3.1).2 + 1) + 1) + 1) := by
    simp only [cmpSub, Cmd.run_seq, Cmd.run_copy, hv1]; rw [← hv2, hv3]
  have qQ : v3.1.ar Q = s.ar Q := by rw [h3 Q (fun h => h.elim hQR hQT), ar2]; exact a1 Q hQT
  have qa : ∀ a, a ≠ R → a ≠ TM → v3.1.ar a = s.ar a := fun a h1' h2' => by rw [h3 a (fun h => h.elim h1' h2'), ar2]; exact a1 a h2'
  have sc3 : ∀ y, ¬ Zc2 y → v3.1.sc y = s.sc y := fun y hy => by
    have hb : ¬ ZB y := fun h => hy (Or.inl (by unfold ZB ZA ZC at h; exact ⟨by omega, by omega⟩))
    have h834 : y ≠ 834 := fun h => hy (Or.inr h)
    rw [h4 y hb]
    simp [hv2, St.setSc, Function.update_of_ne h834]
    exact g3 y hb
  rw [hrun]
  by_cases hf : Dv ≤ V (s.ar R) n
  · have : v3.1.sc 834 ≠ 0 := by rw [c834, if_pos hf]; omega
    simp only [Cmd.run_ifZero, this, if_false, Cmd.run_wr]
    refine ⟨?_, ?_, fun a h1' h2' h3' => ?_, fun y hy => ?_, ?_⟩
    · simp only [St.setAr, St.putAr, St.setAr_ar]
      rw [Function.update_of_ne hQR.symm]; rw [h2, if_pos hf]
    · simp only [St.setAr, St.putAr, St.setAr_ar]
      rw [Function.update_self, c831, c835, qQ]
      have := V_update_at (s.ar Q) n idx 1 hidx.1 hidx.2 (by norm_num)
      rw [hq0] at this; rw [if_pos hf]; simp only [Nat.add_zero, Nat.zero_mul, Nat.one_mul] at this ⊢; omega
    · simp only [St.setAr_ar]; rw [Function.update_of_ne h3', qa a h1' h2']
    · simp only [St.setAr_sc]; exact sc3 y hy
    · have := h5; have := g4; omega
  · have : v3.1.sc 834 = 0 := by rw [c834, if_neg hf]
    simp only [Cmd.run_ifZero, this, if_true, Cmd.run_skip]
    refine ⟨?_, ?_, fun a h1' h2' h3' => qa a h1' h2', fun y hy => sc3 y hy, ?_⟩
    · rw [h2, if_neg hf]
    · rw [qQ, if_neg hf]; simp
    · have := h5; have := g4; omega

theorem div_pure (T b Dv : ℕ) (hb : b ≤ 1) (hD : 0 < Dv) :
    (2 * T + b) % Dv = (if Dv ≤ 2 * (T % Dv) + b then 2 * (T % Dv) + b - Dv else 2 * (T % Dv) + b) ∧
    (2 * T + b) / Dv = 2 * (T / Dv) + (if Dv ≤ 2 * (T % Dv) + b then 1 else 0) := by
  have h1 := Nat.div_add_mod T Dv
  have h2 := Nat.mod_lt T hD
  set q := T / Dv
  set r0 := T % Dv
  by_cases hf : Dv ≤ 2 * r0 + b
  · rw [if_pos hf, if_pos hf]
    obtain ⟨d, hd⟩ : ∃ d, 2 * r0 + b = Dv + d := ⟨2 * r0 + b - Dv, by omega⟩
    have hd' : 2 * r0 + b - Dv = d := by omega
    rw [hd']
    have e : 2 * T + b = d + Dv * (2 * q + 1) := by nlinarith
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hD, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    constructor <;> ring
  · rw [if_neg hf, if_neg hf]
    have e : 2 * T + b = (2 * r0 + b) + Dv * (2 * q) := by nlinarith
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hD, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    constructor <;> ring

def divBody (Nn Dd Q R TM ONE : ℕ) : Cmd := .seq idxC (.seq (shiftIn Nn R TM ONE) (cmpSub Dd Q R TM))

/-- scalars written by a division turn -/
def Zd (y : ℕ) : Prop := (721 ≤ y ∧ y ≤ 799) ∨ (830 ≤ y ∧ y ≤ 834)

theorem divBody_step (Nn Dd Q R TM ONE : ℕ) (hRT : R ≠ TM) (hRD : R ≠ Dd) (hRO : R ≠ ONE) (hTD : TM ≠ Dd)
    (hQR : Q ≠ R) (hQT : Q ≠ TM) (hNR : Nn ≠ R) (hNT : Nn ≠ TM) (hOT : ONE ≠ TM)
    (t : St) (c n Nv Dv : ℕ) (hW : t.sc 710 = n) (hc : c < n) (h835 : t.sc 835 = 1)
    (hD0 : 0 < Dv) (hDn : 2 * Dv ≤ 2 ^ n)
    (hNv : V (t.ar Nn) n = Nv) (hDv : V (t.ar Dd) n = Dv) (hO : V (t.ar ONE) n = 1)
    (hR : V (t.ar R) n = Nv / 2 ^ (n - c) % Dv)
    (hQ : V (t.ar Q) n = Nv / 2 ^ (n - c) / Dv * 2 ^ (n - c)) :
    V ((Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).1.ar R) n = Nv / 2 ^ (n - (c + 1)) % Dv ∧
    V ((Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).1.ar Q) n = Nv / 2 ^ (n - (c + 1)) / Dv * 2 ^ (n - (c + 1)) ∧
    (∀ a, a ≠ R → a ≠ TM → a ≠ Q → (Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).1.ar a = t.ar a) ∧
    (∀ y, ¬ Zd y → (Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).1.sc y = t.sc y) ∧
    (Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).2 ≤ 200 * (n + 1) + 6 := by
  set t0 := t.setSc 830 c with ht0
  have f0 : ∀ y, y ≠ 830 → t0.sc y = t.sc y := fun y hy => by simp [ht0, St.setSc, Function.update_of_ne hy]
  have c0 : t0.sc 830 = c := by simp [ht0, St.setSc]
  obtain ⟨i1, i2, i3, i4⟩ := idxC_run t0 n c (by rw [f0 710 (by norm_num), hW]) c0
  set u1 := Cmd.run idxC t0 with hu1
  have w1 : u1.1.sc 710 = n := by rw [i2 710 (by norm_num) (by norm_num), f0 710 (by norm_num), hW]
  have ar1 : u1.1.ar = t.ar := i3
  have hRlt : V (t.ar R) n < Dv := by rw [hR]; exact Nat.mod_lt _ hD0
  obtain ⟨j1, j2, j3, j4⟩ := shiftIn_run Nn R TM ONE hRT hRO hNR hNT hOT u1.1 n (n - c) w1 i1 (by rw [ar1]; exact hO)
    (by rw [ar1]; omega)
  set u2 := Cmd.run (shiftIn Nn R TM ONE) u1.1 with hu2
  have w2 : u2.1.sc 710 = n := by rw [j3 710 (by unfold Zs; omega)]; exact w1
  have g831 : u2.1.sc 831 = n - c := by rw [j3 831 (by unfold Zs; omega)]; exact i1
  have g835 : u2.1.sc 835 = 1 := by
    rw [j3 835 (by unfold Zs; omega), i2 835 (by norm_num) (by norm_num), f0 835 (by norm_num), h835]
  have ar2 : ∀ a, a ≠ R → a ≠ TM → u2.1.ar a = t.ar a := fun a h1 h2 => by rw [j2 a h1 h2, ar1]
  -- the quotient cell is free
  have hq0 : bt (u2.1.ar Q) (n - c) = 0 := by
    rw [ar2 Q hQR hQT]
    have hv := V_div_mod2 (t.ar Q) n (n - c - 1) (by omega)
    rw [hQ] at hv
    have e1 : n - c - 1 + 1 = n - c := by omega
    rw [e1] at hv
    rw [← hv]
    have p2 : 2 ^ (n - c) = 2 ^ (n - c - 1) * 2 := by rw [← pow_succ, e1]
    have e2 : Nv / 2 ^ (n - c) / Dv * 2 ^ (n - c) = (Nv / 2 ^ (n - c) / Dv * 2) * 2 ^ (n - c - 1) := by
      rw [p2]; ring
    rw [e2, Nat.mul_div_cancel _ (by positivity)]
    simp
  obtain ⟨k1, k2, k3, k4, k5⟩ := cmpSub_run Dd Q R TM hRT hRD hTD hQR hQT u2.1 n (n - c) Dv w2 g831 ⟨by omega, by omega⟩ g835
    (by rw [ar2 Dd (Ne.symm hRD) (Ne.symm hTD)]; exact hDv) hq0
  have hrun : Cmd.run (divBody Nn Dd Q R TM ONE) t0 = ((Cmd.run (cmpSub Dd Q R TM) u2.1).1,
      u1.2 + (u2.2 + (Cmd.run (cmpSub Dd Q R TM) u2.1).2 + 1) + 1) := by
    simp only [divBody, Cmd.run_seq]; rfl
  -- arithmetic
  have e1 : n - c - 1 + 1 = n - c := by omega
  have hb : bt (t.ar Nn) (n - c) = Nv / 2 ^ (n - c - 1) % 2 := by
    have := V_div_mod2 (t.ar Nn) n (n - c - 1) (by omega)
    rw [hNv, e1] at this; exact this.symm
  have hT : Nv / 2 ^ (n - c - 1) = 2 * (Nv / 2 ^ (n - c)) + Nv / 2 ^ (n - c - 1) % 2 := by
    have := div_step Nv (n - c - 1); rw [e1] at this; exact this
  have hb1 : Nv / 2 ^ (n - c - 1) % 2 ≤ 1 := by omega
  obtain ⟨dp1, dp2⟩ := div_pure (Nv / 2 ^ (n - c)) (Nv / 2 ^ (n - c - 1) % 2) Dv hb1 hD0
  rw [← hT] at dp1 dp2
  have vR1 : V (u1.1.ar R) n = Nv / 2 ^ (n - c) % Dv := by rw [ar1, hR]
  have vR2 : V (u2.1.ar R) n = 2 * (Nv / 2 ^ (n - c) % Dv) + Nv / 2 ^ (n - c - 1) % 2 := by
    rw [j1, vR1, ar1, hb]
  have vQ2 : V (u2.1.ar Q) n = Nv / 2 ^ (n - c) / Dv * 2 ^ (n - c) := by rw [ar2 Q hQR hQT, hQ]
  rw [vR2] at k1 k2
  rw [vQ2] at k2
  have ee : n - (c + 1) = n - c - 1 := by omega
  have p2 : 2 ^ (n - c) = 2 ^ (n - c - 1) * 2 := by rw [← pow_succ, e1]
  rw [hrun]
  dsimp only
  refine ⟨?_, ?_, fun a h1 h2 h3 => ?_, fun y hy => ?_, ?_⟩
  · rw [k1, ee, dp1]
  · rw [k2, ee, dp2]
    by_cases hf : Dv ≤ 2 * (Nv / 2 ^ (n - c) % Dv) + Nv / 2 ^ (n - c - 1) % 2
    · simp only [if_pos hf]; rw [p2]; ring
    · simp only [if_neg hf]; rw [p2]; ring
  · rw [k3 a h1 h2 h3, ar2 a h1 h2]
  · have h1 : ¬ Zc2 y := fun h => hy (by unfold Zc2 at h; unfold Zd; omega)
    have h2 : ¬ Zs y := fun h => hy (by unfold Zs at h; unfold Zd; omega)
    have h3 : y ≠ 831 := fun h => hy (by unfold Zd; omega)
    have h4 : y ≠ 833 := fun h => hy (by unfold Zd; omega)
    have h5 : y ≠ 830 := fun h => hy (by unfold Zd; omega)
    rw [k4 y h1, j3 y h2, i2 y h3 h4, f0 y h5]
  · have := i4; have := j4; have := k5; omega

def divC (Nn Dd Q R TM ONE : ℕ) : Cmd :=
  .seq (zeroA R) <| .seq (zeroA Q) <| .seq (oneA ONE) <| .seq (.setK 835 1) (.loop 710 830 (divBody Nn Dd Q R TM ONE))

/-- **Division.**  `V Q = V Nn / V Dd`, `V R = V Nn % V Dd` (width `n` in scalar 710, `2 V Dd ≤ 2^n`, `V Dd > 0`). -/
theorem divC_run (Nn Dd Q R TM ONE : ℕ) (hRT : R ≠ TM) (hRD : R ≠ Dd) (hRO : R ≠ ONE) (hTD : TM ≠ Dd)
    (hQR : Q ≠ R) (hQT : Q ≠ TM) (hNR : Nn ≠ R) (hNT : Nn ≠ TM) (hOT : ONE ≠ TM)
    (hQO : Q ≠ ONE) (hNQ : Nn ≠ Q) (hDQ : Dd ≠ Q) (hNO : Nn ≠ ONE) (hDO : Dd ≠ ONE)
    (st : St) (n : ℕ) (hW : st.sc 710 = n) (hn : 1 ≤ n) (hD0 : 0 < V (st.ar Dd) n) (hDn : 2 * V (st.ar Dd) n ≤ 2 ^ n) :
    V ((Cmd.run (divC Nn Dd Q R TM ONE) st).1.ar Q) n = V (st.ar Nn) n / V (st.ar Dd) n ∧
    V ((Cmd.run (divC Nn Dd Q R TM ONE) st).1.ar R) n = V (st.ar Nn) n % V (st.ar Dd) n ∧
    (∀ a, a ≠ R → a ≠ TM → a ≠ Q → a ≠ ONE → (Cmd.run (divC Nn Dd Q R TM ONE) st).1.ar a = st.ar a) ∧
    (∀ y, ¬ (Zd y ∨ ZK y ∨ y = 835) → (Cmd.run (divC Nn Dd Q R TM ONE) st).1.sc y = st.sc y) ∧
    (Cmd.run (divC Nn Dd Q R TM ONE) st).2 ≤ n * (200 * (n + 1) + 7) + 16 * n + 40 := by
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run R st n hW
  generalize hz1 : Cmd.run (zeroA R) st = s1 at z1 z2 z3 z4 z5
  have w1 : s1.1.sc 710 = n := by rw [z4 710 (by unfold ZC; omega)]; exact hW
  obtain ⟨y1, y2, y3, y4, y5⟩ := zeroA_run Q s1.1 n w1
  generalize hz2 : Cmd.run (zeroA Q) s1.1 = s2 at y1 y2 y3 y4 y5
  have w2 : s2.1.sc 710 = n := by rw [y4 710 (by unfold ZC; omega)]; exact w1
  obtain ⟨o1, o2, o3, o4, o5⟩ := oneA_run ONE s2.1 n w2 hn
  generalize ho : Cmd.run (oneA ONE) s2.1 = s3 at o1 o2 o3 o4 o5
  have w3 : s3.1.sc 710 = n := by rw [o4 710 (by unfold ZK ZC; omega)]; exact w2
  set s4 := s3.1.setSc 835 1 with hs4
  have w4 : s4.sc 710 = n := by simp [hs4, St.setSc, Function.update_of_ne (show (710:ℕ) ≠ 835 by norm_num), w3]
  have h835 : s4.sc 835 = 1 := by simp [hs4, St.setSc]
  -- arrays after init
  have aN : s4.ar Nn = st.ar Nn := by
    show s3.1.ar Nn = _
    rw [o3 Nn hNO, y3 Nn hNQ, z3 Nn hNR]
  have aD : s4.ar Dd = st.ar Dd := by
    show s3.1.ar Dd = _
    rw [o3 Dd hDO, y3 Dd hDQ, z3 Dd hRD.symm]
  have aO : V (s4.ar ONE) n = 1 := o2
  have aR : V (s4.ar R) n = 0 := by
    show V (s3.1.ar R) n = 0
    rw [o3 R hRO, y3 R hQR.symm]; exact z2
  have aQ : V (s4.ar Q) n = 0 := by
    show V (s3.1.ar Q) n = 0
    rw [o3 Q hQO]; exact y2
  set Nv := V (st.ar Nn) n with hNv
  set Dv := V (st.ar Dd) n with hDv
  have hNlt : Nv < 2 ^ n := V_lt _ _
  let I : ℕ → St → Prop := fun c t => V (t.ar R) n = Nv / 2 ^ (n - c) % Dv ∧
    V (t.ar Q) n = Nv / 2 ^ (n - c) / Dv * 2 ^ (n - c) ∧ (∀ a, a ≠ R → a ≠ TM → a ≠ Q → t.ar a = s4.ar a) ∧
    (∀ y, ¬ Zd y → t.sc y = s4.sc y)
  have h0 : I 0 s4 := by
    refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    · rw [aR, Nat.sub_zero, Nat.div_eq_of_lt hNlt]; simp
    · rw [aQ, Nat.sub_zero, Nat.div_eq_of_lt hNlt]; simp
  have step : ∀ c t, c < n → I c t → I (c + 1) (Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).1 ∧
      (Cmd.run (divBody Nn Dd Q R TM ONE) (t.setSc 830 c)).2 ≤ 200 * (n + 1) + 6 := by
    intro c t hc ⟨p1, p2, p3, p4⟩
    have tW : t.sc 710 = n := by rw [p4 710 (by unfold Zd; omega)]; exact w4
    have t835 : t.sc 835 = 1 := by rw [p4 835 (by unfold Zd; omega)]; exact h835
    obtain ⟨r1, r2, r3, r4, r5⟩ := divBody_step Nn Dd Q R TM ONE hRT hRD hRO hTD hQR hQT hNR hNT hOT t c n Nv Dv tW hc t835 hD0 hDn
      (by rw [p3 Nn hNR hNT hNQ, aN]) (by rw [p3 Dd hRD.symm hTD.symm hDQ, aD]) (by rw [p3 ONE hRO.symm hOT hQO.symm]; exact aO)
      p1 p2
    exact ⟨⟨r1, r2, fun a h1 h2 h3 => by rw [r3 a h1 h2 h3, p3 a h1 h2 h3], fun y hy => by rw [r4 y hy, p4 y hy]⟩, r5⟩
  have hI := Cmd.loop_inv (b := 710) (c := 830) (body := divBody Nn Dd Q R TM ONE) (st := s4) I h0 (fun c t hc hp => (step c t (by rw [w4] at hc; exact hc) hp).1)
  have hC := Cmd.loop_cost_le (b := 710) (c := 830) (body := divBody Nn Dd Q R TM ONE) (st := s4) I (200 * (n + 1) + 6) h0
    (fun c t hc hp => (step c t (by rw [w4] at hc; exact hc) hp).1) (fun c t hc hp => (step c t (by rw [w4] at hc; exact hc) hp).2)
  rw [w4] at hI hC
  have hr : Cmd.run (divC Nn Dd Q R TM ONE) st = ((Cmd.run (.loop 710 830 (divBody Nn Dd Q R TM ONE)) s4).1,
      s1.2 + (s2.2 + (s3.2 + (1 + (Cmd.run (.loop 710 830 (divBody Nn Dd Q R TM ONE)) s4).2 + 1) + 1) + 1) + 1) := by
    simp only [divC, Cmd.run_seq, Cmd.run_setK, hz1, hz2, ho]; rfl
  rw [hr]
  obtain ⟨q1, q2, q3, q4⟩ := hI
  simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.mul_one] at q1 q2
  refine ⟨q2, q1, fun a h1 h2 h3 h4 => ?_, fun y hy => ?_, ?_⟩
  · rw [q3 a h1 h2 h3]
    show s3.1.ar a = _
    rw [o3 a h4, y3 a h3, z3 a h1]
  · have hz : ¬ Zd y := fun h => hy (Or.inl h)
    have hk : ¬ ZK y := fun h => hy (Or.inr (Or.inl h))
    have h835' : y ≠ 835 := fun h => hy (Or.inr (Or.inr h))
    have hc : ¬ ZC y := fun h => hk (Or.inl h)
    rw [q4 y hz]
    simp only [hs4, St.setSc_sc]
    rw [Function.update_of_ne h835', o4 y hk, y4 y hc, z4 y hc]
  · simp only
    have e : n * (200 * (n + 1) + 6 + 1) = n * (200 * (n + 1) + 7) := by ring
    rw [e] at hC
    have := z5; have := y5; have := o5; omega

end ECDLP.L113
