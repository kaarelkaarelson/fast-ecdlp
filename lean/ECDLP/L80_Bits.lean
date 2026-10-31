import ECDLP.L80_Gen

/-!
# L80 / Bits: the binary expansion of a scalar into a bit array (counter by repeated ripple increment)
`bitsC dst vS` : cells `1..n` of `dst` (`n` = scalar 710) receive the bits of `sc vS mod 2^n`; array `60` must hold the number `1`.
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def bitsC (dst vS : ℕ) : Cmd := .seq (zeroA dst) (.loop vS 820 (addC false dst 60))

def Zb (y : ℕ) : Prop := ZC y ∨ ZA y ∨ y = 820

theorem bitsC_run (dst vS : ℕ) (hd : dst ≠ 60) (hv : ¬ Zb vS) (hv710 : vS ≠ 710) (st : St) (n : ℕ) (hW : st.sc 710 = n)
    (h1 : V (st.ar 60) n = 1) :
    let r := Cmd.run (bitsC dst vS) st
    V (r.1.ar dst) n = st.sc vS % 2 ^ n ∧ ArKeep dst st r.1 ∧ ScKeep Zb st r.1 ∧
    r.2 ≤ 5 * n + 3 + st.sc vS * (25 * n + 11) := by
  intro r
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run dst st n hW
  generalize hz : Cmd.run (zeroA dst) st = s0 at z1 z2 z3 z4 z5
  have w0 : s0.1.sc 710 = n := by rw [z4 710 (by simp [ZC])]; exact hW
  have a60 : s0.1.ar 60 = st.ar 60 := z3 60 (Ne.symm hd)
  have v0 : s0.1.sc vS = st.sc vS := z4 vS (fun h => hv (Or.inl h))
  let P : ℕ → St → Prop := fun j t => V (t.ar dst) n = j % 2 ^ n ∧ t.ar 60 = st.ar 60 ∧ t.sc 710 = n ∧
    ArKeep dst st t ∧ ScKeep Zb st t
  have h0 : P 0 s0.1 := ⟨by simp [z2], a60, w0, fun a ha => by rw [z3 a ha], fun y hy => z4 y (fun h => hy (Or.inl h))⟩
  have hstep : ∀ j t, j < s0.1.sc vS → P j t → P (j + 1) (Cmd.run (addC false dst 60) (t.setSc 820 j)).1 := by
    intro j t _ ⟨p1, p2, p3, p4, p5⟩
    have t710 : (t.setSc 820 j).sc 710 = n := by simp [St.setSc, p3]
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := add_run dst 60 hd (t.setSc 820 j) n t710
    have b60 : (t.setSc 820 j).ar 60 = st.ar 60 := p2
    simp only [St.setSc_ar] at b2
    have hlt := V_lt ((Cmd.run (addC false dst 60) (t.setSc 820 j)).1.ar dst) n
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hc := b3
      have hmod : (j + 1) % 2 ^ n = (j % 2 ^ n + 1) % 2 ^ n := by rw [Nat.add_mod j 1, Nat.add_mod (j % 2 ^ n) 1, Nat.mod_mod]
      rw [hmod]
      rw [p2, h1, p1] at b2
      rcases (by omega : (Cmd.run (addC false dst 60) (t.setSc 820 j)).1.sc 722 = 0 ∨
          (Cmd.run (addC false dst 60) (t.setSc 820 j)).1.sc 722 = 1) with h | h
      · rw [h] at b2; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · rw [h] at b2
        have hjn := Nat.mod_lt j (show 0 < 2 ^ n by positivity)
        have : (j % 2 ^ n + 1) % 2 ^ n = j % 2 ^ n + 1 - 2 ^ n := by
          rcases Nat.lt_or_ge (j % 2 ^ n + 1) (2 ^ n) with h' | h'
          · exfalso; omega
          · have : j % 2 ^ n + 1 = 2 ^ n := by omega
            rw [this]; simp
        omega
    · have := b4 60 (Ne.symm hd); simp only [St.setSc_ar] at this ⊢; rw [this]; exact p2
    · have := b5 710 (by simp [ZA]); simp only [St.setSc_sc] at this; rw [this]; simpa [St.setSc] using p3
    · intro a ha; have := b4 a ha; simp only [St.setSc_ar] at this; rw [this]; exact p4 a ha
    · intro y hy
      have hy' : ¬ ZA y := fun h => hy (Or.inr (Or.inl h))
      have hy2 : y ≠ 820 := fun h => hy (Or.inr (Or.inr h))
      rw [b5 y hy']; simp [St.setSc, Function.update_apply, hy2]; exact p5 y hy
  have hI := Cmd.loop_inv (b := vS) (c := 820) (body := addC false dst 60) P h0 hstep
  have hC := Cmd.loop_cost_le (b := vS) (c := 820) (body := addC false dst 60) P (25 * n + 10) h0 hstep
    (fun j t _ ⟨p1, p2, p3, p4, p5⟩ => by
      have t710 : (t.setSc 820 j).sc 710 = n := by simp [St.setSc, p3]
      exact (add_run dst 60 hd (t.setSc 820 j) n t710).2.2.2.2.2)
  have hr : r = ((Cmd.run (.loop vS 820 (addC false dst 60)) s0.1).1, s0.2 + (Cmd.run (.loop vS 820 (addC false dst 60)) s0.1).2 + 1) := by
    simp only [r, bitsC, Cmd.run_seq, hz]
  rw [hr]
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI
  rw [v0] at i1 hC
  refine ⟨i1, fun a ha => by simp only; rw [i4 a ha], fun y hy => ?_, ?_⟩
  · simp only; rw [i5 y hy]
  · simp only
    have e : st.sc vS * (25 * n + 10 + 1) = st.sc vS * (25 * n + 11) := rfl
    omega

end ECDLP.L80
