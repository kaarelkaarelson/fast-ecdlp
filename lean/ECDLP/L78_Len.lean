import ECDLP.L78_Frame
import ECDLP.L77_Cap

/-!
# L78 / Len: the per-call length test `lenCmd m` and its contract (inputs: any state holding the instance)

`lenCmd m` = `setW m ; parseAll ; computeC m ; scanC ; finC m`:
set the bignum width `W = (m+2) |encB| + 5`; parse the five numbers; compute `X = sInf {B | p ≤ B^m}` (L76's `computeC`);
scan for `Nat.size X`; set scalar 3 to `[|τ| ≤ m (size X + 1)]` (= `[|τ| ≤ nlen m x]`).
-/
namespace ECDLP.L78
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Factoring.Aux.Trial Computability ECDLP ECDLP.L61 ECDLP.L70 ECDLP.L71 ECDLP.L76

def lenCmd (m : ℕ) : Cmd := .seq (setW m) (.seq parseAll (.seq (computeC m) (.seq scanC (finC m))))

theorem setW_good (m : ℕ) : GoodW (setW m) := by
  obtain ⟨h1, h2⟩ := addN_good (m + 2)
  refine ⟨fun x hx => ?_, fun a ha => ?_⟩
  · by_cases hm : x ∈ Cmd.wsc (addN (m + 2))
    · exact h1 x hm
    · simp [setW, Cmd.wsc, hm] at hx
      omega
  · simp [setW, Cmd.war] at ha
    exact h2 a ha

theorem lenCmd_keep (m : ℕ) : Keep (lenCmd m) := by
  obtain ⟨a1, b1⟩ := setW_good m
  obtain ⟨a2, b2⟩ := parseAll_good
  obtain ⟨a3, b3⟩ := computeC_good m
  obtain ⟨a4, b4⟩ := scanC_good
  obtain ⟨a5, b5⟩ := finC_good m
  constructor
  · intro st i hi h3
    apply Cmd.run_sc_frame
    intro hmem
    simp only [lenCmd, Cmd.wsc, List.mem_append] at hmem
    rcases hmem with h | h | h | h | h
    · have := a1 i h; omega
    · have := a2 i h; omega
    · have := a3 i h; omega
    · have := a4 i h; omega
    · have := a5 i h; omega
  · intro st a ha
    apply Cmd.run_ar_frame
    intro hmem
    simp only [lenCmd, Cmd.war, List.mem_append] at hmem
    rcases hmem with h | h | h | h | h
    · have := b1 a h; omega
    · have := b2 a h; omega
    · have := b3 a h; omega
    · have := b4 a h; omega
    · have := b5 a h; omega


/-- the cost bound -/
def Tl (m L : ℕ) : ℕ := 10000 * m * ((m + 7) * (L + 1)) ^ 3

set_option maxHeartbeats 4000000 in
theorem lenCmd_spec (m : ℕ) (hm : 1 ≤ m) (x : Inst) (st : St) (τ : List Bool) (hc : Conf x τ st) (hP : x.1.Prime) :
    (Cmd.run (lenCmd m) st).1.sc 3 = (if τ.length ≤ nlen m x then 1 else 0) ∧
    (Cmd.run (lenCmd m) st).2 ≤ Tl m (encB x).length := by
  obtain ⟨h0, hA, h2, -⟩ := hc
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hP' : p.Prime := hP
  set N := (encB (p, a, b, xR, yR, π)).length with hN
  -- numeric facts
  have hpN : p < 2 ^ N := by
    have h1 := valL_lt (encodeNat p)
    rw [valL_encodeNat] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (enc_len_le (p, a, b, xR, yR, π)))
  have hp2 : 2 ≤ p := hP'.two_le
  obtain ⟨w1, w2, w3, w4, w5⟩ := setW_run (m := m) st
  generalize hr1 : Cmd.run (setW m) st = r1 at w1 w2 w3 w4 w5
  rw [h0] at w1 w2 w5
  set W := (m + 2) * N + 5 with hW
  have hNW : N ≤ W := by nlinarith
  have hW5 : 5 ≤ W := by omega
  have hrA : r1.1.ar 0 = startingMemory (encB (p, a, b, xR, yR, π)) := by rw [w3, hA]
  have hrN : r1.1.sc 0 = N := by rw [w2]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    parseAll_run π p a b xR yR r1.1 W w1 hrA hrN hNW
  generalize hr2 : Cmd.run parseAll r1.1 = r2 at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  have hs2 : r2.1.sc 2 = st.sc 2 := by
    rw [q10 2 (by simp [ZPa, ZC]), w4 2 (by norm_num) (by norm_num)]
  have hpm : p ≤ (2 ^ N) ^ m := le_trans hpN.le (Nat.le_self_pow (by omega) _)
  have hW1 : W - 1 = (m + 2) * N + 4 := by omega
  have hmN : (2 ^ N) ^ m ≤ 2 ^ (W - 1) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [hW1]; nlinarith)
  have h2pp : 2 * (p * p) < 2 ^ (W - 1) := by
    have h1 : p * p < 2 ^ N * 2 ^ N := Nat.mul_lt_mul'' hpN hpN
    have h2 : 2 ^ N * 2 ^ N * 2 = 2 ^ (2 * N + 1) := by ring
    have h3 : 2 ^ (2 * N + 1) ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by rw [hW1]; nlinarith)
    omega
  have hcomp := compute_run m hm r2.1 W N p a b xR yR (fun y => r2.1.sc y) (fun y _ => rfl) (by simp [q6, hrN])
    q7 (by omega) hp2 hNW hpm hmN h2pp q1 q2 q3 q4 q5 hW5 _ rfl
  obtain ⟨c1, -, -, -, c47, -, -, -, -, -, c710, c0, c2, -, -, c_cost⟩ := hcomp
  generalize hr3 : Cmd.run (computeC m) r2.1 = r3 at c47 c710 c0 c2 c_cost
  have hs3 : r3.1.sc 2 = st.sc 2 := by rw [c2, hs2]
  obtain ⟨d1, d2, d3, d4⟩ := scan_run r3.1 W c710
  generalize hr4 : Cmd.run scanC r3.1 = r4 at d1 d2 d3 d4
  have hs4 : r4.1.sc 2 = st.sc 2 := by rw [d3 2 (by norm_num) (by norm_num) (by norm_num), hs3]
  obtain ⟨e1, e2, e3, e4⟩ := fin_run m r4.1
  generalize hr5 : Cmd.run (finC m) r4.1 = r5 at e1 e2 e3 e4
  have hsz : r4.1.sc 951 = Nat.size (sInf {B | p ≤ B ^ m}) := by rw [d1, ← c47]
  have hszW : r4.1.sc 951 ≤ W := by
    rw [d1]; exact Nat.size_le.2 (V_lt _ _)
  simp only [lenCmd, Cmd.run_seq, hr1, hr2, hr3, hr4, hr5]
  have hcost : r1.2 + r2.2 + r3.2 + r4.2 + r5.2 + 4 ≤ Tl m N := by
    have hY : W ≤ (m + 7) * (N + 1) := by rw [hW]; nlinarith
    have hmWW : m * W ≤ m * W * W := Nat.le_mul_of_pos_right _ (by omega)
    have hmWWW : m * W * W ≤ m * W * W * W := Nat.le_mul_of_pos_right _ (by omega)
    have hmm : m ≤ m * W := Nat.le_mul_of_pos_right _ (by omega)
    have hWm : W ≤ m * W := Nat.le_mul_of_pos_left _ (by omega)
    have hmN' : m * N ≤ m * W := Nat.mul_le_mul_left m hNW
    have e4' : r5.2 ≤ (W + 1) * (2 * m + 2) + 8 := by
      refine le_trans e4 ?_
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 8
    have hT : m * W * W * W ≤ m * ((m + 7) * (N + 1)) ^ 3 := by
      have : W ^ 3 ≤ ((m + 7) * (N + 1)) ^ 3 := Nat.pow_le_pow_left hY 3
      calc m * W * W * W = m * W ^ 3 := by ring
        _ ≤ _ := Nat.mul_le_mul_left m this
    unfold Tl
    nlinarith [w5, q11, c_cost, d4, e4']
  refine ⟨?_, by omega⟩
  rw [e1, hs4, hsz, h2]
  rfl


theorem Tl_subexp (m : ℕ) : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tl m L ≤ C * 2 ^ (L / k) := by
  intro k hk
  refine ⟨10000 * m * (m + 7) ^ 3 * (3 * k + 1) ^ 3, fun L => ?_⟩
  set P := 2 ^ (L / (3 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (3 * k + 1) * P := by
    have := le_two_pow_div L (3 * k) (by omega)
    nlinarith
  have h3 : P ^ 3 ≤ 2 ^ (L / k) := by
    have h := mul_div_mul_le 3 k L
    calc P ^ 3 = 2 ^ (3 * (L / (3 * k))) := by rw [hP, ← pow_mul, mul_comm]
      _ ≤ 2 ^ (L / k) := Nat.pow_le_pow_right (by norm_num) h
  unfold Tl
  calc 10000 * m * ((m + 7) * (L + 1)) ^ 3 = 10000 * m * (m + 7) ^ 3 * (L + 1) ^ 3 := by ring
    _ ≤ 10000 * m * (m + 7) ^ 3 * ((3 * k + 1) * P) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu 3)
    _ = 10000 * m * (m + 7) ^ 3 * (3 * k + 1) ^ 3 * P ^ 3 := by ring
    _ ≤ 10000 * m * (m + 7) ^ 3 * (3 * k + 1) ^ 3 * 2 ^ (L / k) := Nat.mul_le_mul_left _ h3

open ECDLP.L77 in
/-- **LSpec discharged**: the per-call length test is `lenCmd`, with cost `Tl m (|encB x|)` (a polynomial). -/
theorem lspec_len (m : ℕ) (hm : 1 ≤ m) : LSpec m (lenCmd m) (Tl m) :=
  ⟨lenCmd_keep m, fun x st τ hc _ hG => lenCmd_spec m hm x st τ hc hG.1⟩

end ECDLP.L78
