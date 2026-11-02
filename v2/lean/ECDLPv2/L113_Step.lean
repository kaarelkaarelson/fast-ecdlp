import ECDLPv2.L113_Big
import ECDLPv2.L113_Crt

/-!
# L113 / Step: one modulus of the sequential CRT, as a command
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

/-- the scalars a CRT step may write -/
def Z0 (y : ℕ) : Prop := (721 ≤ y ∧ y ≤ 799) ∨ (803 ≤ y ∧ y ≤ 899)

theorem QQ_eq (A B j k : ℕ) : QQ (A % j) (B % j) j k = QQ A B j k := by
  unfold QQ
  exact ((Nat.mod_modEq A j).add (Nat.ModEq.mul_left k (Nat.mod_modEq B j)) : _)

theorem Cells_self {n : ℕ} {f g : ℕ → ℕ} (h : Cells n f g) : Cells n f f :=
  fun i => ⟨(h i).1, fun _ => rfl⟩

def crtStep (X P T RA : ℕ) : Cmd :=
  .seq (modBig X) <| .seq (.copy 803 811) <| .seq (modBig P) <| .seq (.copy 804 811) <|
  .seq (.rd 807 RA 802 0) <| .seq (.setK 808 0) <| .seq (findC 804 804 808 806) <| .seq (.incr 806) <|
  .seq (findC 803 804 807 805) <| .seq (addMul X P 805 822) (mulSm P T 806 822)


theorem crtStep_run (X P T RA : ℕ) (hXP : X ≠ P) (hXT : X ≠ T) (hPT : P ≠ T) (hRX : RA ≠ X) (hRP : RA ≠ P) (hRT : RA ≠ T)
    (st : St) (n j N : ℕ) (hW : st.sc 710 = n) (hj : st.sc 802 = j) (h2 : 2 ≤ j)
    (hRA : st.ar RA j = N % j) (hCX : Cells n (st.ar X) (st.ar X))
    (hP : 0 < V (st.ar P) n) (hX : V (st.ar X) n < V (st.ar P) n)
    (hXN : V (st.ar X) n % V (st.ar P) n = N % V (st.ar P) n) (hlim : j * V (st.ar P) n < 2 ^ n) :
    0 < V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ∧
    V ((Cmd.run (crtStep X P T RA) st).1.ar X) n < V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ∧
    V ((Cmd.run (crtStep X P T RA) st).1.ar X) n % V ((Cmd.run (crtStep X P T RA) st).1.ar P) n =
      N % V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ∧
    j ∣ V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ∧
    V (st.ar P) n ∣ V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ∧
    V ((Cmd.run (crtStep X P T RA) st).1.ar P) n ≤ j * V (st.ar P) n ∧
    Cells n ((Cmd.run (crtStep X P T RA) st).1.ar X) (st.ar X) ∧
    (Cmd.run (crtStep X P T RA) st).1.ar RA = st.ar RA ∧
    (∀ a, a ≠ X → a ≠ P → a ≠ T → (Cmd.run (crtStep X P T RA) st).1.ar a = st.ar a) ∧
    ScKeep Z0 st (Cmd.run (crtStep X P T RA) st).1 ∧
    (Cmd.run (crtStep X P T RA) st).2 ≤ 200 * ((n + 1) * (j + 1) ^ 2) := by
  have hj0 : 0 < j := by omega
  set s1 := Cmd.run (modBig X) st with hs1
  set st2 := s1.1.setSc 803 (s1.1.sc 811) with hst2
  set s3 := Cmd.run (modBig P) st2 with hs3
  set st4 := s3.1.setSc 804 (s3.1.sc 811) with hst4
  set st5 := st4.setSc 807 (st4.ar RA (st4.sc 802 + 0)) with hst5
  set st6 := st5.setSc 808 0 with hst6
  set s7 := Cmd.run (findC 804 804 808 806) st6 with hs7
  set st8 := s7.1.setSc 806 (s7.1.sc 806 + 1) with hst8
  set s9 := Cmd.run (findC 803 804 807 805) st8 with hs9
  set s10 := Cmd.run (addMul X P 805 822) s9.1 with hs10
  set s11 := Cmd.run (mulSm P T 806 822) s10.1 with hs11
  have hrun : Cmd.run (crtStep X P T RA) st = (s11.1, s1.2 + (1 + (s3.2 + (1 + (1 + (1 + (s7.2 + (1 + (s9.2 +
      (s10.2 + s11.2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    simp only [crtStep, Cmd.run_seq]; rfl
  -- stage 1: X mod j
  obtain ⟨a1, a2, a3, a4⟩ := modBig_run X st n j hW hj h2
  rw [← hs1] at a1 a2 a3 a4
  -- stage 2
  have b710 : st2.sc 710 = n := by rw [hst2]; simp [St.setSc, Function.update_of_ne (by norm_num : (710:ℕ) ≠ 803)]; rw [a2 710 (Or.inl (by norm_num))]; exact hW
  have b802 : st2.sc 802 = j := by rw [hst2]; simp [St.setSc, Function.update_of_ne (by norm_num : (802:ℕ) ≠ 803)]; rw [a2 802 (Or.inl (by norm_num))]; exact hj
  have b803 : st2.sc 803 = V (st.ar X) n % j := by rw [hst2]; simp [St.setSc, a1]
  have bar2 : st2.ar = st.ar := by rw [hst2]; simp [St.setSc, a3]
  -- stage 3: P mod j
  obtain ⟨c1, c2, c3, c4⟩ := modBig_run P st2 n j b710 b802 h2
  rw [← hs3] at c1 c2 c3 c4
  have d710 : st4.sc 710 = n := by rw [hst4]; simp [St.setSc, Function.update_of_ne (by norm_num : (710:ℕ) ≠ 804)]; rw [c2 710 (Or.inl (by norm_num))]; exact b710
  have d802 : st4.sc 802 = j := by rw [hst4]; simp [St.setSc, Function.update_of_ne (by norm_num : (802:ℕ) ≠ 804)]; rw [c2 802 (Or.inl (by norm_num))]; exact b802
  have d803 : st4.sc 803 = V (st.ar X) n % j := by rw [hst4]; simp [St.setSc, Function.update_of_ne (by norm_num : (803:ℕ) ≠ 804)]; rw [c2 803 (Or.inl (by norm_num))]; exact b803
  have d804 : st4.sc 804 = V (st.ar P) n % j := by rw [hst4]; simp [St.setSc, c1, bar2]
  have dar : st4.ar = st.ar := by rw [hst4]; simp [St.setSc, c3, bar2]
  -- stage 5, 6
  have e807 : st6.sc 807 = N % j := by
    rw [hst6, hst5]; simp [St.setSc, Function.update_of_ne (by norm_num : (807:ℕ) ≠ 808), d802, dar, hRA]
  have e808 : st6.sc 808 = 0 := by rw [hst6]; simp [St.setSc]
  have e804 : st6.sc 804 = V (st.ar P) n % j := by
    rw [hst6, hst5]; simp [St.setSc, Function.update_of_ne (by norm_num : (804:ℕ) ≠ 808), Function.update_of_ne (by norm_num : (804:ℕ) ≠ 807), d804]
  have e803 : st6.sc 803 = V (st.ar X) n % j := by
    rw [hst6, hst5]; simp [St.setSc, Function.update_of_ne (by norm_num : (803:ℕ) ≠ 808), Function.update_of_ne (by norm_num : (803:ℕ) ≠ 807), d803]
  have e802 : st6.sc 802 = j := by
    rw [hst6, hst5]; simp [St.setSc, Function.update_of_ne (by norm_num : (802:ℕ) ≠ 808), Function.update_of_ne (by norm_num : (802:ℕ) ≠ 807), d802]
  have e710 : st6.sc 710 = n := by
    rw [hst6, hst5]; simp [St.setSc, Function.update_of_ne (by norm_num : (710:ℕ) ≠ 808), Function.update_of_ne (by norm_num : (710:ℕ) ≠ 807), d710]
  have ear : st6.ar = st.ar := by rw [hst6, hst5]; simp [St.setSc, dar]
  -- stage 7: the least u
  set VP := V (st.ar P) n with hVP
  set VX := V (st.ar X) n with hVX
  have hex7 : ∃ k, k < j ∧ QQ (st6.sc 804) (st6.sc 804) j k = st6.sc 808 := by
    refine ⟨j - 1, by omega, ?_⟩
    rw [e808]
    unfold QQ
    have : st6.sc 804 + (j - 1) * st6.sc 804 = j * st6.sc 804 := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp; ring
    rw [this, Nat.mul_mod_right]
  obtain ⟨f1, f2, f3, f4⟩ := findC_run 804 804 808 806 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    st6 j e802 (by rw [e804]; exact Nat.mod_lt _ hj0) (by rw [e804]; exact Nat.mod_lt _ hj0) (by rw [e808]; exact hj0)
  rw [← hs7] at f1 f2 f3 f4
  obtain ⟨g1, g2, g3⟩ := f1 hex7
  rw [e804, e808] at g2 g3
  simp only [QQ_eq] at g2 g3
  have hu_dvd : j ∣ (s7.1.sc 806 + 1) * VP := by
    apply Nat.dvd_of_mod_eq_zero
    unfold QQ at g2
    rw [← g2]; congr 1; ring
  have hu_min : ∀ v, 1 ≤ v → v < s7.1.sc 806 + 1 → ¬ j ∣ v * VP := by
    intro v hv1 hv2 hd
    apply g3 (v - 1) (by omega)
    unfold QQ
    have : VP + (v - 1) * VP = v * VP := by
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      simp; ring
    rw [this]; exact Nat.mod_eq_zero_of_dvd hd
  have hst8_6 : st8.sc 806 = s7.1.sc 806 + 1 := by rw [hst8]; simp [St.setSc]
  have hst8_o : ∀ y, y ≠ 806 → st8.sc y = s7.1.sc y := fun y hy => by rw [hst8]; simp [St.setSc, Function.update_of_ne hy]
  have hst8_ar : st8.ar = st.ar := by rw [hst8]; simp [St.setSc, f3, ear]
  -- stage 9: the least s
  set u := s7.1.sc 806 + 1 with hu
  have hu1 : 1 ≤ u := by omega
  have huj : u ≤ j := by omega
  have f2' : ∀ y, y ≠ 817 → y ≠ 818 → y ≠ 819 → y ≠ 820 → y ≠ 806 → s7.1.sc y = st6.sc y := f2
  have h803 : st8.sc 803 = VX % j := by rw [hst8_o 803 (by norm_num), f2' 803 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e803]
  have h804 : st8.sc 804 = VP % j := by rw [hst8_o 804 (by norm_num), f2' 804 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e804]
  have h807 : st8.sc 807 = N % j := by rw [hst8_o 807 (by norm_num), f2' 807 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e807]
  have h802 : st8.sc 802 = j := by rw [hst8_o 802 (by norm_num), f2' 802 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e802]
  have h710 : st8.sc 710 = n := by rw [hst8_o 710 (by norm_num), f2' 710 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e710]
  obtain ⟨s0, hs0, hs0'⟩ := crt_exists N VX VP j u hP hX hXN hu1 hu_dvd
  have hex9 : ∃ k, k < j ∧ QQ (st8.sc 803) (st8.sc 804) j k = st8.sc 807 := by
    refine ⟨s0, by omega, ?_⟩
    rw [h803, h804, h807, QQ_eq]; exact hs0'
  obtain ⟨i1, i2, i3, i4⟩ := findC_run 803 804 807 805 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    st8 j h802 (by rw [h803]; exact Nat.mod_lt _ hj0) (by rw [h804]; exact Nat.mod_lt _ hj0) (by rw [h807]; exact Nat.mod_lt _ hj0)
  rw [← hs9] at i1 i2 i3 i4
  obtain ⟨j1, j2, j3⟩ := i1 hex9
  rw [h803, h804, h807] at j2 j3
  simp only [QQ_eq] at j2 j3
  have hs2 : (VX + s9.1.sc 805 * VP) % j = N % j := by unfold QQ at j2; exact j2
  have hs3 : ∀ k, k < s9.1.sc 805 → (VX + k * VP) % j ≠ N % j := fun k hk => by have := j3 k hk; unfold QQ at this; exact this
  obtain ⟨k1, k2, k3⟩ := crt_step N VX VP j (s9.1.sc 805) u hP hX hXN hu1 hu_dvd hu_min hs2 hs3
  have i2' : ∀ y, y ≠ 817 → y ≠ 818 → y ≠ 819 → y ≠ 820 → y ≠ 805 → s9.1.sc y = st8.sc y := i2
  have g710 : s9.1.sc 710 = n := by rw [i2' 710 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h710]
  have g806 : s9.1.sc 806 = u := by rw [i2' 806 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hst8_6]
  have gar : s9.1.ar = st.ar := by rw [i3, hst8_ar]
  have hlimu : u * VP < 2 ^ n := lt_of_le_of_lt (Nat.mul_le_mul_right _ huj) hlim
  -- stage 10: X += s P
  obtain ⟨m1, m2, m3, m4, m5⟩ := addMul_run X P 805 822 hXP ⟨by unfold ZA; omega, by norm_num⟩ ⟨by unfold ZA; omega, by norm_num⟩
    s9.1 n g710 (by rw [gar]; exact hCX) (by rw [gar]; calc _ < u * VP := k2
                                                          _ < 2 ^ n := hlimu)
  rw [← hs10] at m1 m2 m3 m4 m5
  rw [gar] at m2
  have n710 : s10.1.sc 710 = n := by rw [m4 710 (fun h => h.elim (fun h => by unfold ZA at h; omega) (fun h => by omega))]; exact g710
  have n806 : s10.1.sc 806 = u := by rw [m4 806 (fun h => h.elim (fun h => by unfold ZA at h; omega) (fun h => by omega))]; exact g806
  have nP : s10.1.ar P = st.ar P := by rw [m3 P (Ne.symm hXP), gar]
  -- stage 11: P := u P
  obtain ⟨o1, o2, o3, o4, o5⟩ := mulSm_run P T 806 822 hPT ⟨by unfold ZB ZA ZC; omega, by norm_num⟩ ⟨by unfold ZB ZA ZC; omega, by norm_num⟩
    s10.1 n n710 (by rw [n806, nP]; exact hlimu)
  rw [← hs11] at o1 o2 o3 o4 o5
  rw [n806, nP] at o2
  rw [n806] at o5
  -- assembly
  have e6 : ∀ y, ¬ Z0 y → st6.sc y = st.sc y := by
    intro y hy
    have hny : y < 721 ∨ (799 < y ∧ y < 803) ∨ 899 < y := by unfold Z0 at hy; omega
    rw [hst6, hst5]
    simp only [St.setSc_sc, Function.update_of_ne (by omega : y ≠ 808), Function.update_of_ne (by omega : y ≠ 807)]
    rw [hst4]
    simp only [St.setSc_sc, Function.update_of_ne (by omega : y ≠ 804)]
    rw [c2 y (by omega), hst2]
    simp only [St.setSc_sc, Function.update_of_ne (by omega : y ≠ 803)]
    exact a2 y (by omega)
  have hP' : V (s11.1.ar P) n = u * VP := o2
  have hX' : V (s11.1.ar X) n = VX + s9.1.sc 805 * VP := by
    rw [o3 X hXP hXT, m2]
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only; rw [hP']; exact Nat.mul_pos hu1 hP
  · simp only; rw [hP', hX']; exact k2
  · simp only; rw [hP', hX']; exact k3
  · simp only; rw [hP']; exact hu_dvd
  · simp only; rw [hP']; exact Dvd.intro_left _ rfl
  · simp only; rw [hP']; exact Nat.mul_le_mul_right _ huj
  · simp only; rw [o3 X hXP hXT]; rw [gar] at m1; exact m1
  · simp only; rw [o3 RA hRP hRT, m3 RA hRX, gar]
  · intro a h1 h2 h3; simp only; rw [o3 a h2 h3, m3 a h1, gar]
  · intro y hy
    have hny : y < 721 ∨ (799 < y ∧ y < 803) ∨ 899 < y := by unfold Z0 at hy; omega
    simp only
    rw [o4 y (fun h => h.elim (fun h => by unfold ZB ZA ZC at h; omega) (fun h => by omega)),
      m4 y (fun h => h.elim (fun h => by unfold ZA at h; omega) (fun h => by omega)),
      i2' y (by omega) (by omega) (by omega) (by omega) (by omega), hst8_o y (by omega),
      f2' y (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact e6 y hy
  · simp only
    have hs_le : s9.1.sc 805 * (25 * n + 12) ≤ j * (25 * n + 12) := Nat.mul_le_mul_right _ (by omega)
    have hu_le : u * (25 * n + 12) ≤ j * (25 * n + 12) := Nat.mul_le_mul_right _ huj
    have hbound : s1.2 + (1 + (s3.2 + (1 + (1 + (1 + (s7.2 + (1 + (s9.2 + (s10.2 + s11.2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
        ≤ 2 * (n * (12 * j + 11) + 5) + 2 * (j * (6 * j + 9) + 7) + 2 * (j * (25 * n + 12)) + 12 * n + 30 := by
      have := a4; have := c4; have := f4; have := i4; have := m5; have := o5
      omega
    refine le_trans hbound ?_
    have key : 200 * ((n + 1) * (j + 1) ^ 2) = (2 * (n * (12 * j + 11) + 5) + 2 * (j * (6 * j + 9) + 7) +
        2 * (j * (25 * n + 12)) + 12 * n + 30) + (200 * (n * j * j) + 326 * (n * j) + 166 * n + 188 * (j * j) + 358 * j + 146) := by ring
    rw [key]; exact Nat.le_add_right _ _

end ECDLP.L113
