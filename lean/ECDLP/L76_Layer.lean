import ECDLP.L76_Compute
import ECDLP.L76_Flags
import ECDLP.L76_Sem

/-!
# L76 / Layer: the input layer, checks part
`checkC m` = set the work width `W = 8 + (m+2)·N` (`N` = scalar 0), parse `encB`, `computeC m`, `ℓ := size X`, the flag `|τ| ≤ m(ℓ+1)`,
the parity flag of `p`, and their conjunction in scalar 775.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L61 Computability

def addN : Cmd := .loop 0 787 (.incr 710)

def repN : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (repN k) addN

def setW (m : ℕ) : Cmd := .seq (.setK 710 8) (repN (m + 2))

theorem repN_run : ∀ (k : ℕ) (s : St),
    (Cmd.run (repN k) s).1.sc 710 = s.sc 710 + k * s.sc 0 ∧ (Cmd.run (repN k) s).1.ar = s.ar ∧ (Cmd.run (repN k) s).1.sc 0 = s.sc 0 ∧
    (∀ y, y ≠ 710 → y ≠ 787 → (Cmd.run (repN k) s).1.sc y = s.sc y) ∧ (Cmd.run (repN k) s).2 ≤ k * (2 * s.sc 0 + 4) + 1 := by
  intro k
  induction k with
  | zero => intro s; simp [repN, Cmd.run_skip]
  | succ k ih =>
    intro s
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih s
    set t := (Cmd.run (repN k) s).1 with ht
    let P : ℕ → St → Prop := fun j u => u.sc 710 = t.sc 710 + j ∧ u.ar = t.ar ∧ u.sc 0 = t.sc 0 ∧
      (∀ y, y ≠ 710 → y ≠ 787 → u.sc y = t.sc y)
    have h0 : P 0 t := ⟨by simp, rfl, rfl, fun _ _ _ => rfl⟩
    have hstep : ∀ j u, j < t.sc 0 → P j u → P (j + 1) (Cmd.run (.incr 710) (u.setSc 787 j)).1 := by
      intro j u _ ⟨p1, p2, p3, p4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Cmd.run_incr, St.setSc, Function.update_apply, p1]; try omega
      · simp [Cmd.run_incr, St.setSc, p2]
      · simp [Cmd.run_incr, St.setSc, Function.update_apply, p3]
      · intro y h1 h2; simp [Cmd.run_incr, St.setSc, Function.update_apply, h1, h2, p4 y h1 h2]
    have hI := Cmd.loop_inv (b := 0) (c := 787) (body := .incr 710) P h0 hstep
    have hC := Cmd.loop_cost_le (b := 0) (c := 787) (body := .incr 710) P 1 h0 hstep (fun _ _ _ _ => by simp [Cmd.run_incr])
    obtain ⟨j1, j2, j3, j4⟩ := hI
    simp only [repN, Cmd.run_seq, addN]
    rw [← ht]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [j1, i1, i3]; ring
    · rw [j2, i2]
    · rw [j3, i3]
    · intro y h1 h2; rw [j4 y h1 h2, i4 y h1 h2]
    · rw [i3] at hC; nlinarith [i5, hC]

theorem setW_run (m : ℕ) (s : St) :
    (Cmd.run (setW m) s).1.sc 710 = 8 + (m + 2) * s.sc 0 ∧ (Cmd.run (setW m) s).1.ar = s.ar ∧
    (Cmd.run (setW m) s).1.sc 0 = s.sc 0 ∧ (∀ y, y ≠ 710 → y ≠ 787 → (Cmd.run (setW m) s).1.sc y = s.sc y) ∧
    (Cmd.run (setW m) s).2 ≤ (m + 2) * (2 * s.sc 0 + 4) + 4 := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := repN_run (m + 2) (s.setSc 710 8)
  simp only [setW, Cmd.run_seq, Cmd.run_setK]
  simp only [St.setSc_sc, Function.update_self, Function.update_of_ne (by norm_num : (0:ℕ) ≠ 710)] at i1 i3 i5
  refine ⟨i1, ?_, i3, ?_, by omega⟩
  · rw [i2]; rfl
  · intro y h1 h2; rw [i4 y h1 h2]; simp [St.setSc, Function.update_of_ne h1]

theorem ite_one_eq_one_iff (P : Prop) [Decidable P] : ((if P then 1 else 0 : ℕ) = 1) ↔ P := by
  by_cases h : P <;> simp [h]

theorem ite_ne_zero_iff (P : Prop) [Decidable P] : ((if P then 1 else 0 : ℕ) ≠ 0) ↔ P := by
  by_cases h : P <;> simp [h]

def oddC : Cmd := .seq (.setK 789 0) (.rd 788 30 789 1)

theorem oddC_run (s : St) :
    (Cmd.run oddC s).1.sc 788 = s.ar 30 1 ∧ (Cmd.run oddC s).1.ar = s.ar ∧
    (∀ y, y ≠ 788 → y ≠ 789 → (Cmd.run oddC s).1.sc y = s.sc y) ∧ (Cmd.run oddC s).2 = 3 := by
  simp [oddC, Cmd.run_seq, Cmd.run_setK, Cmd.run_rd, St.setSc, Function.update_apply]
  intro y h1 h2; simp [h1, h2]

def andFlags : Cmd := .seq (.setK 775 0)
  (.ifZero 770 .skip (.ifZero 771 .skip (.ifZero 772 .skip (.ifZero 774 .skip (.ifZero 788 .skip (.setK 775 1))))))

theorem andFlags_run (s : St) :
    (Cmd.run andFlags s).1.sc 775 = (if s.sc 770 ≠ 0 ∧ s.sc 771 ≠ 0 ∧ s.sc 772 ≠ 0 ∧ s.sc 774 ≠ 0 ∧ s.sc 788 ≠ 0 then 1 else 0) ∧
    (Cmd.run andFlags s).1.ar = s.ar ∧ (∀ y, y ≠ 775 → (Cmd.run andFlags s).1.sc y = s.sc y) ∧ (Cmd.run andFlags s).2 ≤ 12 := by
  by_cases h1 : s.sc 770 = 0 <;> by_cases h2 : s.sc 771 = 0 <;> by_cases h3 : s.sc 772 = 0 <;> by_cases h4 : s.sc 774 = 0 <;>
    by_cases h5 : s.sc 788 = 0 <;>
    simp [andFlags, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifZero, Cmd.run_skip, St.setSc, Function.update_apply, h1, h2, h3, h4, h5] <;>
    (try (intro y hy; simp [hy]))

def checkC (m : ℕ) : Cmd :=
  .seq (setW m) (.seq parseAll (.seq (computeC m) (.seq (sizeC 47 782) (.seq (nlenFlag m 782 774) (.seq oddC andFlags)))))

/-- every scalar the checks write -/
def ZChk (y : ℕ) : Prop := 710 ≤ y ∧ y ≤ 799

theorem sck_trans {s t u : St} (h1 : ScKeep ZChk s t) (h2 : ScKeep ZChk t u) : ScKeep ZChk s u :=
  (h1.trans h2).mono (fun y h => by rcases h with h | h <;> exact h)

theorem enc_len_le (π : List Bool) (p a b xR yR : ℕ) :
    (encodeNat p).length ≤ (encB (p, a, b, xR, yR, π)).length := by
  rw [encB_eq]; simp [block_length]; omega

theorem p_lt_pow (π : List Bool) (p a b xR yR : ℕ) : p < 2 ^ (encB (p, a, b, xR, yR, π)).length := by
  exact lt_of_lt_of_le (Factoring.Aux.Trial.lt_two_pow_length p) (Nat.pow_le_pow_right (by norm_num) (enc_len_le π p a b xR yR))

set_option maxHeartbeats 4000000 in
theorem checkC_run (m : ℕ) (hm : 1 ≤ m) (π : List Bool) (p a b xR yR : ℕ) (hp : p.Prime) (st : St)
    (hA : st.ar 0 = startingMemory (encB (p, a, b, xR, yR, π))) (hN : st.sc 0 = (encB (p, a, b, xR, yR, π)).length) :
    ∀ r : St × ℕ, r = Cmd.run (checkC m) st →
    (r.1.sc 775 = 1 ↔ ((ECDLP.L51.Wc p a b).Δ ≠ 0 ∧ (ECDLP.L51.Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p) ∧
        st.sc 2 ≤ m * (Nat.size (sInf {B | p ≤ B ^ m}) + 1))) ∧
    V (r.1.ar 21) (8 + (m + 2) * st.sc 0) = a % p ∧ V (r.1.ar 22) (8 + (m + 2) * st.sc 0) = b % p ∧
    V (r.1.ar 23) (8 + (m + 2) * st.sc 0) = xR % p ∧ V (r.1.ar 24) (8 + (m + 2) * st.sc 0) = yR % p ∧
    V (r.1.ar 47) (8 + (m + 2) * st.sc 0) = sInf {B | p ≤ B ^ m} ∧ V (r.1.ar 56) (8 + (m + 2) * st.sc 0) = 2 * (p * p) ∧
    V (r.1.ar 30) (8 + (m + 2) * st.sc 0) = p ∧ r.1.sc 782 = Nat.size (sInf {B | p ≤ B ^ m}) ∧
    r.1.sc 710 = 8 + (m + 2) * st.sc 0 ∧ ArK AR st r.1 ∧ ScKeep ZChk st r.1 ∧
    r.2 ≤ 400 * m * (8 + (m + 2) * st.sc 0) ^ 3 + 13000 * m * (8 + (m + 2) * st.sc 0) ^ 2 + 4000 * m * (8 + (m + 2) * st.sc 0) + 3000 := by
  intro r hr
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  set N := (encB (p, a, b, xR, yR, π)).length with hNdef
  have hpN : p < 2 ^ N := p_lt_pow π p a b xR yR
  rw [hN]
  set W := 8 + (m + 2) * N with hWdef
  have hNW : N ≤ W := by rw [hWdef]; nlinarith
  have hW5 : 5 ≤ W := by rw [hWdef]; omega
  have hW1' : W - 1 = 7 + (m + 2) * N := by omega
  have hpm : p ≤ (2 ^ N) ^ m := le_trans hpN.le (Nat.le_self_pow (by omega) _)
  have hmN : (2 ^ N) ^ m ≤ 2 ^ (W - 1) := by
    rw [← pow_mul]; apply Nat.pow_le_pow_right (by norm_num); rw [hW1']; nlinarith
  have h2pp : 2 * (p * p) < 2 ^ (W - 1) := by
    have h1 : p * p < 2 ^ N * 2 ^ N := Nat.mul_lt_mul'' hpN hpN
    have h2 : 2 ^ (2 * N + 1) ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by rw [hW1']; nlinarith)
    have h3 : 2 ^ (2 * N + 1) = 2 * (2 ^ N * 2 ^ N) := by rw [pow_succ, two_mul, pow_add]; ring
    omega
  -- stage 1: the width
  obtain ⟨w1, w2, w3, w4, w5⟩ := setW_run m st
  generalize hs1 : Cmd.run (setW m) st = q1 at w1 w2 w3 w4 w5
  rw [hN] at w1 w5
  -- stage 2: parse
  obtain ⟨pa1, pa2, pa3, pa4, pa5, pa6, pa7, pa8, pa9, pa10, pa11⟩ := parseAll_run π p a b xR yR q1.1 W (by rw [w1]) (by rw [w2, hA])
    (by rw [w3, hN]) (by rw [hNdef.symm]; exact hNW)
  generalize hs2 : Cmd.run parseAll q1.1 = q2 at pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11
  have hq2_0 : q2.1.sc 0 = N := by rw [pa6, w3, hN]
  have hq2_710 : q2.1.sc 710 = W := pa7
  -- stage 3: the arithmetic
  obtain ⟨c21, c22, c23, c24, c47, c56, c30, f0, f1, f2, c710, c0, c2, cA, cZ, cC⟩ :=
    compute_run m hm q2.1 W N p a b xR yR (fun y => q2.1.sc y) (fun y _ => rfl) hq2_0 hq2_710 (by omega) hp2 hNW hpm hmN h2pp
      pa1 pa2 pa3 pa4 pa5 hW5 (Cmd.run (computeC m) q2.1) rfl
  generalize hs3 : Cmd.run (computeC m) q2.1 = q3 at c21 c22 c23 c24 c47 c56 c30 f0 f1 f2 c710 c0 c2 cA cZ cC
  -- stage 4: the size of X
  obtain ⟨z1, z2, z3, z4⟩ := sizeC_run 47 782 ⟨by norm_num, by norm_num⟩ q3.1 W c710 (by norm_num)
  generalize hs4 : Cmd.run (sizeC 47 782) q3.1 = q4 at z1 z2 z3 z4
  -- stage 5: |tau| <= nlen
  obtain ⟨n1, n2, n3, n4, n5⟩ := nlenFlag_run m 782 774 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num) q4.1
  generalize hs5 : Cmd.run (nlenFlag m 782 774) q4.1 = q5 at n1 n2 n3 n4 n5
  -- stage 6, 7
  obtain ⟨o1, o2, o3, o4⟩ := oddC_run q5.1
  generalize hs6 : Cmd.run oddC q5.1 = q6 at o1 o2 o3 o4
  obtain ⟨d1, d2, d3, d4⟩ := andFlags_run q6.1
  generalize hs7 : Cmd.run andFlags q6.1 = q7 at d1 d2 d3 d4
  have hrr : r = (q7.1, q1.2 + (q2.2 + (q3.2 + (q4.2 + (q5.2 + (q6.2 + q7.2 + 1) + 1) + 1) + 1) + 1) + 1) := by
    rw [hr]; simp only [checkC, Cmd.run_seq, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hr1 : r.1 = q7.1 := by rw [hrr]
  have hr2 : r.2 = q1.2 + (q2.2 + (q3.2 + (q4.2 + (q5.2 + (q6.2 + q7.2 + 1) + 1) + 1) + 1) + 1) + 1 := by rw [hrr]
  rw [hr1, hr2]
  -- scalar bookkeeping
  have k2 : q3.1.sc 2 = st.sc 2 := by
    rw [c2, pa10 2 (by simp [ZPa, ZC]), w4 2 (by norm_num) (by norm_num)]
  have k4_2 : q4.1.sc 2 = st.sc 2 := by rw [z3 2 (by norm_num) (by norm_num) (by norm_num), k2]
  have k4_782 : q4.1.sc 782 = Nat.size (sInf {B | p ≤ B ^ m}) := by rw [z1, c47]
  have h770 : q6.1.sc 770 = q3.1.sc 770 := by
    rw [o3 770 (by norm_num) (by norm_num), n4 770 (by norm_num) (by norm_num) (by norm_num),
      z3 770 (by norm_num) (by norm_num) (by norm_num)]
  have h771 : q6.1.sc 771 = q3.1.sc 771 := by
    rw [o3 771 (by norm_num) (by norm_num), n4 771 (by norm_num) (by norm_num) (by norm_num),
      z3 771 (by norm_num) (by norm_num) (by norm_num)]
  have h772 : q6.1.sc 772 = q3.1.sc 772 := by
    rw [o3 772 (by norm_num) (by norm_num), n4 772 (by norm_num) (by norm_num) (by norm_num),
      z3 772 (by norm_num) (by norm_num) (by norm_num)]
  have h774 : q6.1.sc 774 = if st.sc 2 ≤ m * (Nat.size (sInf {B | p ≤ B ^ m}) + 1) then 1 else 0 := by
    rw [o3 774 (by norm_num) (by norm_num), n1, k4_2, k4_782]
  have hcell : q6.1.sc 788 = q3.1.ar 30 1 := by rw [o1, n2, z2]
  have hodd : (q3.1.ar 30 1 ≠ 0) ↔ p % 2 = 1 := by
    have := V_div_mod2 (q3.1.ar 30) W 0 (by omega)
    rw [c30] at this
    simp only [pow_zero, Nat.div_one, zero_add] at this
    unfold bt at this
    by_cases h : q3.1.ar 30 1 = 0
    · simp only [h, if_true] at this; simp [h, this]
    · simp only [h, if_false] at this; simp [h]; omega
  have hflag : q7.1.sc 775 = 1 ↔ ((q3.1.sc 770 ≠ 0) ∧ (q3.1.sc 771 ≠ 0) ∧ (q3.1.sc 772 ≠ 0) ∧
      (st.sc 2 ≤ m * (Nat.size (sInf {B | p ≤ B ^ m}) + 1)) ∧ p % 2 = 1) := by
    rw [d1, h770, h771, h772, h774, hcell, ite_one_eq_one_iff, ite_ne_zero_iff, hodd]
  have hAr : q7.1.ar = q3.1.ar := by rw [d2, o2, n2, z2]
  have hsc3 : ∀ y, y ≠ 775 → y ≠ 788 → y ≠ 789 → y ≠ 785 → y ≠ 786 → y ≠ 774 → y ≠ 780 → y ≠ 781 → y ≠ 782 →
      q7.1.sc y = q3.1.sc y := by
    intro y h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [d3 y h1, o3 y h2 h3, n4 y h4 h5 h6, z3 y h7 h8 h9]
  have hsz : Nat.size (sInf {B | p ≤ B ^ m}) ≤ W := by
    rw [← c47]; exact Nat.size_le.2 (V_lt _ _)
  have hAR : ArK AR st q3.1 := by
    have a0 : ArK AR st q1.1 := fun a _ => by rw [w2]
    have a1 : ArK AR q1.1 q2.1 := pa9.mono (fun c hc => by
      unfold AR; simp only [aJunk, aRP, aRA, aRB, aRX, aRY] at hc; omega)
    exact ark_AR_trans (ark_AR_trans a0 a1) cA
  have hZ : ScKeep ZChk st q7.1 := by
    have s1' : ScKeep ZChk st q1.1 := fun y hy => w4 y (fun h => hy (by subst h; unfold ZChk; omega))
      (fun h => hy (by subst h; unfold ZChk; omega))
    have s2' : ScKeep ZChk q1.1 q2.1 := pa10.mono (fun y hy => by
      rcases hy with hy | hy
      · unfold ZC at hy; unfold ZChk; omega
      · unfold ZChk; omega)
    have s3' : ScKeep ZChk q2.1 q3.1 := cZ.mono (fun y hy => by
      unfold ZAll2 ZAll at hy; unfold ZChk; omega)
    have s4' : ScKeep ZChk q3.1 q7.1 := fun y hy => hsc3 y (fun h => hy (by subst h; unfold ZChk; omega))
      (fun h => hy (by subst h; unfold ZChk; omega)) (fun h => hy (by subst h; unfold ZChk; omega))
      (fun h => hy (by subst h; unfold ZChk; omega)) (fun h => hy (by subst h; unfold ZChk; omega))
      (fun h => hy (by subst h; unfold ZChk; omega)) (fun h => hy (by subst h; unfold ZChk; omega))
      (fun h => hy (by subst h; unfold ZChk; omega)) (fun h => hy (by subst h; unfold ZChk; omega))
    exact sck_trans (sck_trans (sck_trans s1' s2') s3') s4'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hflag]
    rcases hp.eq_two_or_odd with h2 | hodd'
    · -- p = 2
      have hΔ0 : (ECDLP.L51.Wc p a b).Δ = 0 := by
        rw [wc_Δ]
        have h16 : (16 : ZMod p) = 0 := by
          have : ((16 : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff, h2]; decide
          simpa using this
        simp [h16]
      constructor
      · rintro ⟨-, -, -, -, h⟩; omega
      · rintro ⟨h, -⟩; exact absurd hΔ0 h
    · have hp3 : 3 ≤ p := by omega
      have hf := flags_iff p hp3 a b xR yR
      rw [← f0, ← f1, ← f2] at hf
      constructor
      · rintro ⟨h0, h1, h2', h3, -⟩
        obtain ⟨hd, hn⟩ := hf.1 ⟨by simpa [f0] using h0, by simpa [f1] using h1, by simpa [f2] using h2'⟩
        exact ⟨hd, hn, h3⟩
      · rintro ⟨hd, hn, h3⟩
        obtain ⟨e0, e1, e2⟩ := hf.2 ⟨hd, hn⟩
        exact ⟨by rw [e0]; simp, by rw [e1]; simp, by rw [e2]; simp, h3, hodd'⟩
  · rw [hAr]; exact c21
  · rw [hAr]; exact c22
  · rw [hAr]; exact c23
  · rw [hAr]; exact c24
  · rw [hAr]; exact c47
  · rw [hAr]; exact c56
  · rw [hAr]; exact c30
  · rw [d3 782 (by norm_num), o3 782 (by norm_num) (by norm_num), n4 782 (by norm_num) (by norm_num) (by norm_num)]
    exact k4_782
  · rw [hsc3 710 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    exact c710
  · exact fun a ha => by rw [hAr]; exact hAR a ha
  · exact hZ
  · have hX : q4.1.sc 782 ≤ W := by rw [k4_782]; exact hsz
    have hn5 : q5.2 ≤ m * (2 * W + 6) + 6 := by
      have := n5; rw [k4_782] at this
      have h2 : m * (2 * (Nat.size (sInf {B | p ≤ B ^ m})) + 6) ≤ m * (2 * W + 6) := Nat.mul_le_mul_left m (by omega)
      omega
    have hW1c : q1.2 ≤ (m + 2) * (2 * W + 4) + 4 := by
      have : (m + 2) * (2 * N + 4) ≤ (m + 2) * (2 * W + 4) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hW2c : (m + 2) * (2 * W + 4) ≤ m * W * 2 + 4 * m + 4 * W + 8 := by ring_nf; omega
    have hWW : W ≤ W * W := Nat.le_mul_self W
    have hmW : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
    have hmWW : W * W ≤ m * W * W := Nat.mul_le_mul_right W hmW
    have hmWWW : m * W * W ≤ m * W * W * W := Nat.le_mul_of_pos_right _ (by omega)
    have hm1 : m ≤ m * W := Nat.le_mul_of_pos_right _ (by omega)
    linarith [pa11, cC, z4, hn5, o4, d4, hW1c, hW2c]

end ECDLP.L76
