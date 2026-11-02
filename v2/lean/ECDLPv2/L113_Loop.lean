import ECDLPv2.L113_Step

/-!
# L113 / Loop: the full CRT command `crtC`
`crtC X P T RA` : given `RA[m] = N mod m` for `2 ≤ m ≤ K+1` (`K` in scalar 801, width `n` in scalar 710) and `(K+1)! < 2^n`, `N` smaller than every
positive common multiple of `1..K+1`, it leaves `N` in the bit array `X` (cells `1..n`).  `P`, `T` are scratch arrays.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
namespace ECDLP.L113
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

def crtBody (X P T RA : ℕ) : Cmd :=
  .seq (.copy 802 800) (.seq (.incr 802) (.seq (.incr 802) (crtStep X P T RA)))

def crtC (X P T RA : ℕ) : Cmd :=
  .seq (zeroA X) (.seq (oneA P) (.loop 801 800 (crtBody X P T RA)))

/-- the scalars `crtC` may write -/
def Z1 (y : ℕ) : Prop := Z0 y ∨ y = 800 ∨ y = 802

theorem pre_eq (s : St) :
    (((s.setSc 802 (s.sc 800)).setSc 802 ((s.setSc 802 (s.sc 800)).sc 802 + 1)).setSc 802
      (((s.setSc 802 (s.sc 800)).setSc 802 ((s.setSc 802 (s.sc 800)).sc 802 + 1)).sc 802 + 1)) =
    s.setSc 802 (s.sc 800 + 2) := by
  apply St.ext
  · funext y; by_cases h : y = 802 <;> simp [St.setSc, h]
  · rfl

theorem crtBody_step (X P T RA : ℕ) (hXP : X ≠ P) (hXT : X ≠ T) (hPT : P ≠ T) (hRX : RA ≠ X) (hRP : RA ≠ P) (hRT : RA ≠ T)
    (t : St) (i n N : ℕ) (hW : t.sc 710 = n) (hRA : t.ar RA (i + 2) = N % (i + 2)) (hCX : Cells n (t.ar X) (t.ar X))
    (hP : 0 < V (t.ar P) n) (hX : V (t.ar X) n < V (t.ar P) n)
    (hXN : V (t.ar X) n % V (t.ar P) n = N % V (t.ar P) n) (hlim : (i + 2) * V (t.ar P) n < 2 ^ n) :
    0 < V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ∧
    V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar X) n < V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ∧
    V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar X) n % V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n =
      N % V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ∧
    (i + 2) ∣ V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ∧
    V (t.ar P) n ∣ V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ∧
    V ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar P) n ≤ (i + 2) * V (t.ar P) n ∧
    Cells n ((Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar X) (t.ar X) ∧
    (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar RA = t.ar RA ∧
    (∀ a, a ≠ X → a ≠ P → a ≠ T → (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.ar a = t.ar a) ∧
    (∀ y, ¬ Z1 y → (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1.sc y = t.sc y) ∧
    (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).2 ≤ 200 * ((n + 1) * (i + 3) ^ 2) + 6 := by
  set u3 := (t.setSc 800 i).setSc 802 (i + 2) with hu3
  have hrun : Cmd.run (crtBody X P T RA) (t.setSc 800 i) =
      ((Cmd.run (crtStep X P T RA) u3).1, 1 + (1 + (1 + (Cmd.run (crtStep X P T RA) u3).2 + 1) + 1) + 1) := by
    simp only [crtBody, Cmd.run_seq, Cmd.run_copy, Cmd.run_incr]
    rw [pre_eq]
    simp [hu3, St.setSc]
  have f3 : ∀ y, y ≠ 800 → y ≠ 802 → u3.sc y = t.sc y := fun y h1 h2 => by
    simp [hu3, St.setSc, Function.update_of_ne h1, Function.update_of_ne h2]
  have s802 : u3.sc 802 = i + 2 := by simp [hu3, St.setSc]
  have s710 : u3.sc 710 = n := by rw [f3 710 (by norm_num) (by norm_num), hW]
  have sar : u3.ar = t.ar := by simp [hu3, St.setSc]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r8', r9, r10⟩ := crtStep_run X P T RA hXP hXT hPT hRX hRP hRT u3 n (i + 2) N s710 s802
    (by omega) (by rw [sar]; exact hRA) (by rw [sar]; exact hCX) (by rw [sar]; exact hP) (by rw [sar]; exact hX)
    (by rw [sar]; exact hXN) (by rw [sar]; exact hlim)
  rw [sar] at r5 r6 r7 r8
  rw [hrun]
  dsimp only
  refine ⟨r1, r2, r3, r4, r5, r6, r7, r8, fun a h1 h2 h3 => by rw [r8' a h1 h2 h3, sar], fun y hy => ?_, ?_⟩
  · have hy1 : ¬ Z0 y := fun h => hy (Or.inl h)
    have hy2 : y ≠ 800 := fun h => hy (Or.inr (Or.inl h))
    have hy3 : y ≠ 802 := fun h => hy (Or.inr (Or.inr h))
    exact (r9 y hy1).trans (f3 y hy2 hy3)
  · have r10' : (Cmd.run (crtStep X P T RA) u3).2 ≤ 200 * ((n + 1) * (i + 3) ^ 2) := r10
    omega

theorem crtC_run (X P T RA : ℕ) (hXP : X ≠ P) (hXT : X ≠ T) (hPT : P ≠ T) (hRX : RA ≠ X) (hRP : RA ≠ P) (hRT : RA ≠ T)
    (st : St) (n K N : ℕ) (hW : st.sc 710 = n) (hK : st.sc 801 = K) (hn : 1 ≤ n) (hfac : (K + 1).factorial < 2 ^ n)
    (hRA : ∀ m, 2 ≤ m → m ≤ K + 1 → st.ar RA m = N % m)
    (hbig : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ K + 1 → i ∣ Y) → N < Y) :
    V ((Cmd.run (crtC X P T RA) st).1.ar X) n = N ∧ Cells n ((Cmd.run (crtC X P T RA) st).1.ar X) (st.ar X) ∧
    (Cmd.run (crtC X P T RA) st).1.ar RA = st.ar RA ∧
    (∀ a, a ≠ X → a ≠ P → a ≠ T → (Cmd.run (crtC X P T RA) st).1.ar a = st.ar a) ∧
    (∀ y, ¬ Z1 y → (Cmd.run (crtC X P T RA) st).1.sc y = st.sc y) ∧
    (Cmd.run (crtC X P T RA) st).2 ≤ K * (200 * ((n + 1) * (K + 3) ^ 2) + 7) + 10 * n + 20 := by
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroA_run X st n hW
  generalize hz : Cmd.run (zeroA X) st = s1 at z1 z2 z3 z4 z5
  have w1 : s1.1.sc 710 = n := by rw [z4 710 (by unfold ZC; omega)]; exact hW
  obtain ⟨o1, o2, o3, o4, o5⟩ := oneA_run P s1.1 n w1 hn
  generalize ho : Cmd.run (oneA P) s1.1 = s2 at o1 o2 o3 o4 o5
  have w2 : s2.1.sc 710 = n := by rw [o4 710 (by unfold ZK ZC; omega)]; exact w1
  have k801 : s2.1.sc 801 = K := by
    rw [o4 801 (by unfold ZK ZC; omega), z4 801 (by unfold ZC; omega)]; exact hK
  have x2 : s2.1.ar X = s1.1.ar X := o3 X hXP
  let I : ℕ → St → Prop := fun i t => 0 < V (t.ar P) n ∧ V (t.ar P) n ≤ (i + 1).factorial ∧ V (t.ar X) n < V (t.ar P) n ∧
    V (t.ar X) n % V (t.ar P) n = N % V (t.ar P) n ∧ (∀ m, 1 ≤ m → m ≤ i + 1 → m ∣ V (t.ar P) n) ∧
    Cells n (t.ar X) (st.ar X) ∧ t.ar RA = st.ar RA ∧ (∀ a, a ≠ X → a ≠ P → a ≠ T → t.ar a = st.ar a) ∧
    (∀ y, ¬ Z1 y → t.sc y = st.sc y)
  have h0 : I 0 s2.1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o2]; omega
    · rw [o2]; simp
    · rw [o2, x2, z2]; omega
    · rw [o2, x2, z2]; exact (Nat.mod_one N).symm
    · intro m h1 h2; rw [o2]; have : m = 1 := by omega
      subst this; exact one_dvd _
    · rw [x2]; exact z1
    · rw [o3 RA hRP, z3 RA hRX]
    · intro a h1 h2 h3; rw [o3 a h2, z3 a h1]
    · intro y hy
      have h1 : ¬ ZC y := fun h => hy (Or.inl (Or.inl (by unfold ZC at h; omega)))
      have h2 : ¬ ZK y := fun h => hy (Or.inl (Or.inl (by unfold ZK ZC at h; omega)))
      rw [o4 y h2, z4 y h1]
  have step : ∀ i t, i < K → I i t → I (i + 1) (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).1 ∧
      (Cmd.run (crtBody X P T RA) (t.setSc 800 i)).2 ≤ 200 * ((n + 1) * (K + 3) ^ 2) + 6 := by
    intro i t hi ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩
    have tW : t.sc 710 = n := by rw [p9 710 (by unfold Z1 Z0; omega)]; exact hW
    have hlim : (i + 2) * V (t.ar P) n < 2 ^ n := by
      calc (i + 2) * V (t.ar P) n ≤ (i + 2) * (i + 1).factorial := Nat.mul_le_mul_left _ p2
        _ = (i + 2).factorial := (Nat.factorial_succ (i + 1)).symm
        _ ≤ (K + 1).factorial := Nat.factorial_le (by omega)
        _ < 2 ^ n := hfac
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r8', r9, r10⟩ := crtBody_step X P T RA hXP hXT hPT hRX hRP hRT t i n N tW
      (by rw [p7]; exact hRA (i + 2) (by omega) (by omega)) (Cells_self p6) p1 p3 p4 hlim
    refine ⟨⟨r1, ?_, r2, r3, ?_, r7.trans p6, by rw [r8, p7], fun a h1 h2 h3 => by rw [r8' a h1 h2 h3, p8 a h1 h2 h3],
      fun y hy => by rw [r9 y hy, p9 y hy]⟩, ?_⟩
    · calc _ ≤ (i + 2) * V (t.ar P) n := r6
        _ ≤ (i + 2) * (i + 1).factorial := Nat.mul_le_mul_left _ p2
        _ = (i + 1 + 1).factorial := (Nat.factorial_succ (i + 1)).symm
    · intro m hm1 hm2
      by_cases hm : m = i + 2
      · rw [hm]; exact r4
      · exact (p5 m hm1 (by omega)).trans r5
    · have : (K + 3) ^ 2 ≥ (i + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := Nat.mul_le_mul_left (n + 1) this
      omega
  have hI := Cmd.loop_inv (b := 801) (c := 800) (body := crtBody X P T RA) (st := s2.1) I h0 (fun i t hi hp => (step i t (by omega) hp).1)
  have hC := Cmd.loop_cost_le (b := 801) (c := 800) (body := crtBody X P T RA) (st := s2.1) I (200 * ((n + 1) * (K + 3) ^ 2) + 6) h0
    (fun i t hi hp => (step i t (by omega) hp).1) (fun i t hi hp => (step i t (by omega) hp).2)
  rw [k801] at hI hC
  have hr : Cmd.run (crtC X P T RA) st = ((Cmd.run (.loop 801 800 (crtBody X P T RA)) s2.1).1,
      s1.2 + (s2.2 + (Cmd.run (.loop 801 800 (crtBody X P T RA)) s2.1).2 + 1) + 1) := by
    simp only [crtC, Cmd.run_seq, hz, ho]
  rw [hr]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hI
  refine ⟨?_, q6, q7, q8, q9, ?_⟩
  · exact crt_final q1 q3 q4 q5 hbig
  · simp only
    have e : K * (200 * ((n + 1) * (K + 3) ^ 2) + 6 + 1) = K * (200 * ((n + 1) * (K + 3) ^ 2) + 7) := by ring
    rw [e] at hC
    omega

end ECDLP.L113
