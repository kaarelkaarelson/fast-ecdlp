import ECDLP.L80_FrameRng
import ECDLP.L80_Hook
import ECDLP.L70_Red

/-!
# L80 / Orc: the per-call oracle `oraC = checkC ; frameW ; engine.shift S ; sc 3 := engine's sc 3` and its frame
-/
namespace ECDLP.L80
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the initial-state predicate of the engine, in L72's layout (arrays `0..11` by windows, `sc 0 = len`, `sc 2 = 0`);
nothing is asked of array 3, of the other cells, or of the other scalars -/
def FrameIn (r : ℕ) (i : EdgeInp) (s : St) : Prop :=
  s.sc 0 = i.len ∧ s.sc 2 = 0 ∧
    Reads72n s.sc s.ar i.p i.a i.b (Bd i.p r) i.xR i.yR i.π (ell i.p r) (ECDLP.L72.bWof (Nat.size i.p))

theorem frameIn_stOf (r : ℕ) (i : EdgeInp) (h : i.adm r) (h9 : 9 ≤ Nat.size i.p) : FrameIn r i (ECDLP.L72.stOf r i) :=
  ⟨ECDLP.L72.stOf_sc0 r i, by simp [ECDLP.L72.stOf], Reads72n.of_reads72 (ECDLP.L72.reads72_stOf r i h h9)⟩

/-! ### the shifted engine writes only above `S` -/

theorem shift_wsc (S : ℕ) : ∀ (c : Cmd) (y : ℕ), y ∈ (c.shift S).wsc → S ≤ y
  | .skip, y, h => by simp [Cmd.shift, Cmd.wsc] at h
  | .seq s t, y, h => by
      simp only [Cmd.shift, Cmd.wsc, List.mem_append] at h
      rcases h with h | h; exact shift_wsc S s y h; exact shift_wsc S t y h
  | .setK x k, y, h => by simp [Cmd.shift, Cmd.wsc] at h; omega
  | .copy x z, y, h => by simp [Cmd.shift, Cmd.wsc] at h; omega
  | .incr x, y, h => by simp [Cmd.shift, Cmd.wsc] at h; omega
  | .decr x, y, h => by simp [Cmd.shift, Cmd.wsc] at h; omega
  | .rd x a i o, y, h => by simp [Cmd.shift, Cmd.wsc] at h; omega
  | .wr a i o z, y, h => by simp [Cmd.shift, Cmd.wsc] at h
  | .ifLt x z s t, y, h => by
      simp only [Cmd.shift, Cmd.wsc, List.mem_append] at h
      rcases h with h | h; exact shift_wsc S s y h; exact shift_wsc S t y h
  | .ifZero x s t, y, h => by
      simp only [Cmd.shift, Cmd.wsc, List.mem_append] at h
      rcases h with h | h; exact shift_wsc S s y h; exact shift_wsc S t y h
  | .loop b c body, y, h => by
      simp only [Cmd.shift, Cmd.wsc, List.mem_cons] at h
      rcases h with h | h; omega; exact shift_wsc S body y h
  | .call M a, y, h => by simp [Cmd.shift, Cmd.wsc] at h

theorem shift_war (S : ℕ) : ∀ (c : Cmd) (a : ℕ), a ∈ (c.shift S).war → S ≤ a
  | .skip, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .seq s t, y, h => by
      simp only [Cmd.shift, Cmd.war, List.mem_append] at h
      rcases h with h | h; exact shift_war S s y h; exact shift_war S t y h
  | .setK x k, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .copy x z, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .incr x, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .decr x, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .rd x a i o, y, h => by simp [Cmd.shift, Cmd.war] at h
  | .wr a i o z, y, h => by simp [Cmd.shift, Cmd.war] at h; omega
  | .ifLt x z s t, y, h => by
      simp only [Cmd.shift, Cmd.war, List.mem_append] at h
      rcases h with h | h; exact shift_war S s y h; exact shift_war S t y h
  | .ifZero x s t, y, h => by
      simp only [Cmd.shift, Cmd.war, List.mem_append] at h
      rcases h with h | h; exact shift_war S s y h; exact shift_war S t y h
  | .loop b c body, y, h => by
      simp only [Cmd.shift, Cmd.war] at h
      exact shift_war S body y h
  | .call M a, y, h => by simp [Cmd.shift, Cmd.war] at h; omega

def oraC (m S : ℕ) (eng : Cmd) : Cmd :=
  .seq (checkC m) (.seq (frameW S) (.seq (eng.shift S) (.copy 3 (S + 3))))

theorem oraC_keep (m S : ℕ) (hS : 1400 ≤ S) (eng : Cmd) : Keep (oraC m S eng) := by
  have h1 := checkC_rng m
  have h2 := frameW_rng S hS
  have hsc : ∀ i, i < 10 → i ≠ 3 → i ∉ (oraC m S eng).wsc := by
    intro i hi h3 hm
    have e : (oraC m S eng).wsc = (checkC m).wsc ++ ((frameW S).wsc ++ ((eng.shift S).wsc ++ [3])) := rfl
    rw [e] at hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm
    · have := (h1.1 i hm).1; omega
    · have := (h2.1 i hm).1; omega
    · have := shift_wsc S eng i hm; omega
    · exact h3 hm
  have har : ∀ a, a < 3 → a ∉ (oraC m S eng).war := by
    intro a ha hm
    have e : (oraC m S eng).war = (checkC m).war ++ ((frameW S).war ++ ((eng.shift S).war ++ [])) := rfl
    rw [e] at hm
    simp only [List.mem_append, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm
    · have := (h1.2 a hm).1; omega
    · have := (h2.2 a hm).1; omega
    · have := shift_war S eng a hm; omega
  exact ⟨fun st i hi h3 => Cmd.run_sc_frame _ st i (hsc i hi h3), fun st a ha => Cmd.run_ar_frame _ st a (har a ha)⟩

/-! ### the state after `checkC ; frameW` -/

def PB (m N : ℕ) : ℕ :=
  (400 * m * (8 + (m + 2) * N) ^ 3 + 13000 * m * (8 + (m + 2) * N) ^ 2 + 4000 * m * (8 + (m + 2) * N) + 3000) +
    10000 * ((8 + (m + 2) * N) + m * (N + 1) + 2) ^ 2 + 1

set_option maxHeartbeats 4000000 in
theorem pre_frame (r S : ℕ) (hS : 1400 ≤ S) (x : Inst) (τ : List Bool) (st : St) (hconf : Conf x τ st) (hgood : Good (r + 1) x τ) :
    let s2 := Cmd.run (.seq (checkC (r + 1)) (frameW S)) st
    FrameIn r (redInp x τ) (unshift S s2.1) ∧ s2.2 ≤ PB (r + 1) (encB x).length ∧
    s2.1.ar 0 = st.ar 0 ∧ s2.1.ar 1 = st.ar 1 := by
  intro s2
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨h0, hA, h2, h1⟩ := hconf
  obtain ⟨hp, hΔ, hns, hl⟩ := hgood
  haveI : Fact p.Prime := ⟨hp⟩
  set N := (encB (p, a, b, xR, yR, π)).length with hN
  obtain ⟨hf, c21, c22, c23, c24, c47, c56, c30, c782, c710, cA, cZ, cC⟩ :=
    checkC_run (r + 1) (by omega) π p a b xR yR hp st hA h0 _ rfl
  generalize hs1 : Cmd.run (checkC (r + 1)) st = s1 at hf c21 c22 c23 c24 c47 c56 c30 c782 c710 cA cZ cC
  rw [h0] at c21 c22 c23 c24 c47 c56 c30 c710 cC
  obtain ⟨W, hW⟩ : ∃ W, W = 8 + (r + 1 + 2) * N := ⟨_, rfl⟩
  rw [← hW] at c21 c22 c23 c24 c47 c56 c30 c710 cC
  have hsc2 : s1.1.sc 2 = τ.length := by rw [cZ 2 (by simp [ZChk]), h2]
  have har1 : s1.1.ar 1 = st.ar 1 := cA 1 (by simp [AR])
  have har0 : s1.1.ar 0 = st.ar 0 := cA 0 (by simp [AR])
  have hp2 : 2 ≤ p := hp.two_le
  have hsz2 : 2 ≤ Nat.size p := (Nat.lt_size).2 (by simpa using hp2)
  have hab : a % p ≠ 0 ∨ b % p ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hΔ
    rw [wc_Δ]
    have ha0 : ((a : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).2 (Nat.dvd_of_mod_eq_zero hc.1)
    have hb0 : ((b : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff b p).2 (Nat.dvd_of_mod_eq_zero hc.2)
    rw [ha0, hb0]; ring
  have hXp : sInf {B | p ≤ B ^ (r + 1)} ≤ p := ECDLP.L51.Bd_le hp.pos r
  have hfw := frameW_run S hS s1.1 W p (a % p) (b % p) (xR % p) (yR % p) (sInf {B | p ≤ B ^ (r + 1)}) τ c710 c30 c21 c22 c23 c24 c47 c56
    c782 hsc2 (by intro j hj; rw [har1]; exact h1 j hj) hsz2 hab (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos)
    (Nat.mod_lt _ hp.pos) hXp
  obtain ⟨fw1, fw2, fw3, fw4⟩ := hfw
  have e1 : s2.1 = (Cmd.run (frameW S) s1.1).1 := by simp only [s2, Cmd.run_seq, hs1]
  have e2 : s2.2 = s1.2 + (Cmd.run (frameW S) s1.1).2 + 1 := by simp only [s2, Cmd.run_seq, hs1]
  have hτN : τ.length ≤ (r + 1) * (N + 1) := by
    have h1' := ECDLP.L61.nlen_le (r + 1) p a b xR yR π
    have h2' := ECDLP.L61.len_encB_ge p a b xR yR π
    have : τ.length ≤ ECDLP.L61.nlen (r + 1) (p, a, b, xR, yR, π) := hl
    exact le_trans this (le_trans h1' (Nat.mul_le_mul_left _ (by omega)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    refine ⟨?_, fw3, fw1⟩
    · rw [fw2]; simp [redInp, EdgeInp.len]
  · rw [e2]
    unfold PB
    have h3 : (W + τ.length + 2) ^ 2 ≤ (W + (r + 1) * (N + 1) + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    simp only [← hW]
    omega
  · rw [e1, Cmd.run_ar_frame _ _ 0 (fun hm => by have := ((frameW_rng S hS).2 0 hm).1; omega), har0]
  · rw [e1, Cmd.run_ar_frame _ _ 1 (fun hm => by have := ((frameW_rng S hS).2 1 hm).1; omega), har1]

end ECDLP.L80
