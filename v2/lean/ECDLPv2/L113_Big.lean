import ECDLPv2.L113_Scalar

/-!
# L113 / Big: bignum loops `X := X + s * P` and `P := u * P` from L76's adder
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

/-- `X := X + (scalar sr) * P` (no overflow assumed) -/
def addMul (X P sr c : ℕ) : Cmd := .loop sr c (addC false X P)

theorem addMul_run (X P sr c : ℕ) (hXP : X ≠ P) (hc : ¬ ZA c ∧ c ≠ 710) (hsr : ¬ ZA sr ∧ sr ≠ c)
    (st : St) (n : ℕ) (hW : st.sc 710 = n) (hCX : Cells n (st.ar X) (st.ar X)) (hlt : V (st.ar X) n + st.sc sr * V (st.ar P) n < 2 ^ n) :
    Cells n ((Cmd.run (addMul X P sr c) st).1.ar X) (st.ar X) ∧
    V ((Cmd.run (addMul X P sr c) st).1.ar X) n = V (st.ar X) n + st.sc sr * V (st.ar P) n ∧
    ArKeep X st (Cmd.run (addMul X P sr c) st).1 ∧
    ScKeep (fun y => ZA y ∨ y = c) st (Cmd.run (addMul X P sr c) st).1 ∧
    (Cmd.run (addMul X P sr c) st).2 ≤ st.sc sr * (25 * n + 12) + 1 := by
  obtain ⟨hcA, hc710⟩ := hc
  let P' : ℕ → St → Prop := fun i t => Cells n (t.ar X) (st.ar X) ∧ V (t.ar X) n = V (st.ar X) n + i * V (st.ar P) n ∧
    ArKeep X st t ∧ ScKeep (fun y => ZA y ∨ y = c) st t
  have h0 : P' 0 st := ⟨hCX, by simp, fun _ _ => rfl, fun _ _ => rfl⟩
  have step : ∀ i t, i < st.sc sr → P' i t →
      P' (i + 1) (Cmd.run (addC false X P) (t.setSc c i)).1 ∧ (Cmd.run (addC false X P) (t.setSc c i)).2 ≤ 25 * n + 10 := by
    intro i t hi ⟨p1, p2, p3, p4⟩
    have w : (t.setSc c i).sc 710 = n := by
      simp [St.setSc, Function.update_of_ne (Ne.symm hc710)]; rw [p4 710 (by unfold ZA; omega)]; exact hW
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := add_run X P hXP (t.setSc c i) n w
    have hPP : t.ar P = st.ar P := p3 P (Ne.symm hXP)
    simp only [St.setSc_ar] at a1 a2
    rw [hPP, p2] at a2
    have hle : (i + 1) * V (st.ar P) n ≤ st.sc sr * V (st.ar P) n := Nat.mul_le_mul_right _ hi
    have hc0 : (Cmd.run (addC false X P) (t.setSc c i)).1.sc 722 = 0 := by
      by_contra hne
      have : 2 ^ n ≤ (Cmd.run (addC false X P) (t.setSc c i)).1.sc 722 * 2 ^ n :=
        Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    refine ⟨⟨a1.trans p1, ?_, ?_, ?_⟩, a6⟩
    · rw [hc0] at a2; nlinarith
    · intro a ha; rw [a4 a ha]; simpa [St.setSc] using p3 a ha
    · intro y hy
      have hy1 : ¬ ZA y := fun h => hy (Or.inl h)
      have hy2 : y ≠ c := fun h => hy (Or.inr h)
      rw [a5 y hy1]; simp [St.setSc, Function.update_of_ne hy2]; exact p4 y hy
  have hI := Cmd.loop_inv (b := sr) (c := c) (body := addC false X P) (st := st) P' h0 (fun i t hi hp => (step i t hi hp).1)
  have hC := Cmd.loop_cost_le (b := sr) (c := c) (body := addC false X P) (st := st) P' (25 * n + 10) h0
    (fun i t hi hp => (step i t hi hp).1) (fun i t hi hp => (step i t hi hp).2)
  obtain ⟨b1, b2, b3, b4⟩ := hI
  exact ⟨b1, b2, b3, b4, by simp only [addMul]; nlinarith [hC]⟩


/-- `P := (scalar ur) * P`, through the temporary array `T` -/
def mulSm (P T ur c : ℕ) : Cmd := .seq (zeroA T) (.seq (addMul T P ur c) (copyA P T))

theorem mulSm_run (P T ur c : ℕ) (hPT : P ≠ T) (hc : ¬ ZB c ∧ c ≠ 710) (hur : ¬ ZB ur ∧ ur ≠ c)
    (st : St) (n : ℕ) (hW : st.sc 710 = n) (hlt : st.sc ur * V (st.ar P) n < 2 ^ n) :
    Cells n ((Cmd.run (mulSm P T ur c) st).1.ar P) (st.ar P) ∧
    V ((Cmd.run (mulSm P T ur c) st).1.ar P) n = st.sc ur * V (st.ar P) n ∧
    (∀ a, a ≠ P → a ≠ T → (Cmd.run (mulSm P T ur c) st).1.ar a = st.ar a) ∧
    ScKeep (fun y => ZB y ∨ y = c) st (Cmd.run (mulSm P T ur c) st).1 ∧
    (Cmd.run (mulSm P T ur c) st).2 ≤ st.sc ur * (25 * n + 12) + 12 * n + 6 := by
  obtain ⟨hcB, hc710⟩ := hc
  obtain ⟨hurB, hurc⟩ := hur
  have hcA : ¬ ZA c := fun h => hcB (Or.inl h)
  have hcC : ¬ ZC c := fun h => hcB (Or.inr h)
  have hurA : ¬ ZA ur := fun h => hurB (Or.inl h)
  have hurC : ¬ ZC ur := fun h => hurB (Or.inr h)
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run T st n hW
  have zc := zeroA_cells T st n hW
  generalize hz : Cmd.run (zeroA T) st = s1 at z1 z2 z3 z4 z5 zc
  have w1 : s1.1.sc 710 = n := by rw [z4 710 (by unfold ZC; omega)]; exact hW
  have u1 : s1.1.sc ur = st.sc ur := z4 ur hurC
  have hCT : Cells n (s1.1.ar T) (s1.1.ar T) := fun i => ⟨fun h => by rw [zc i h.1 h.2]; omega, fun _ => rfl⟩
  have hPT1 : s1.1.ar P = st.ar P := z3 P hPT
  obtain ⟨m1, m2, m3, m4, m5⟩ := addMul_run T P ur c (Ne.symm hPT) ⟨hcA, hc710⟩ ⟨hurA, hurc⟩ s1.1 n w1 hCT
    (by rw [z2, hPT1, u1]; simpa using hlt)
  generalize hm : Cmd.run (addMul T P ur c) s1.1 = s2 at m1 m2 m3 m4 m5
  have w2 : s2.1.sc 710 = n := by
    rw [m4 710 (fun h => h.elim (fun h => by unfold ZA at h; omega) (fun h => hc710 h.symm))]; exact w1
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := copyA_run P T hPT s2.1 n w2
  have hP2 : s2.1.ar P = st.ar P := by rw [m3 P hPT, hPT1]
  have hrun : Cmd.run (mulSm P T ur c) st = ((Cmd.run (copyA P T) s2.1).1, s1.2 + (s2.2 + (Cmd.run (copyA P T) s2.1).2 + 1) + 1) := by
    simp only [mulSm, Cmd.run_seq, hz, hm]
  rw [hrun]
  refine ⟨?_, ?_, fun a h1 h2 => ?_, fun y hy => ?_, ?_⟩
  · rw [hP2] at k1; exact k1
  · rw [k3, m2, z2, hPT1, u1]; simp
  · rw [k4 a h1, m3 a h2, z3 a h2]
  · have h1 : ¬ ZC y := fun h => hy (Or.inl (Or.inr h))
    have h2 : ¬ (ZA y ∨ y = c) := fun h => hy (h.elim (fun h => Or.inl (Or.inl h)) Or.inr)
    rw [k5 y h1, m4 y h2, z4 y h1]
  · have := m5; rw [u1] at this
    omega

end ECDLP.L113
