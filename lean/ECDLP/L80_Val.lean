import ECDLP.L80_Lists
import ECDLP.L76_Layer

/-!
# L80 / Val: value lemmas for truncated / zero-padded bit arrays, the pi copy
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem bt_bt' (x : ℕ) : (if (if x = 0 then 0 else 1) = 0 then 0 else 1 : ℕ) = (if x = 0 then 0 else 1) := by
  split_ifs <;> simp_all

/-- bits above `n` of a number below `2^n` vanish -/
theorem V_trunc (f : ℕ → ℕ) (w n x : ℕ) (hx : V f w = x) (hxn : x < 2 ^ n) (hnw : n ≤ w) : V f n = x := by
  have key : ∀ k, n ≤ k → k ≤ w → V f k = V f n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; rfl
    | succ k hk ih =>
      intro hkw
      have h1 := V_div_mod2 f w k (by omega)
      have h2 : V f w / 2 ^ k = 0 := by
        rw [hx]; exact Nat.div_eq_of_lt (lt_of_lt_of_le hxn (Nat.pow_le_pow_right (by norm_num) hk))
      rw [h2] at h1
      have h3 : bt f (k + 1) = 0 := by simpa using h1.symm
      rw [V_snoc, h3, ih (by omega)]; simp
  rw [← hx, ← key w hnw le_rfl]

/-- a zero-padded copy has the value of the source truncated -/
theorem V_pad (f g : ℕ → ℕ) (w : ℕ) :
    ∀ n, (∀ i, 1 ≤ i → i ≤ n → g i = if i ≤ w then bt f i else 0) → V g n = V f (min n w) := by
  intro n
  induction n with
  | zero => intro _; simp [V, numCells]
  | succ n ih =>
    intro h
    rw [V_snoc, ih (fun i h1 h2 => h i h1 (by omega))]
    by_cases hn : n + 1 ≤ w
    · have e : bt g (n + 1) = bt f (n + 1) := by
        have := h (n + 1) (by omega) le_rfl
        rw [if_pos hn] at this
        unfold bt; rw [this]; have := bt_le f (n + 1); unfold bt at this ⊢; split_ifs at this ⊢ <;> simp_all
      rw [e, min_eq_left (by omega : n ≤ w), min_eq_left hn, V_snoc]
    · have e : bt g (n + 1) = 0 := by
        have := h (n + 1) (by omega) le_rfl
        rw [if_neg hn] at this; simp [bt, this]
      rw [e, min_eq_right (by omega : w ≤ n), min_eq_right (by omega : w ≤ n + 1)]; simp

theorem V_padval (f g : ℕ → ℕ) (w n x : ℕ) (hg : ∀ i, 1 ≤ i → i ≤ n → g i = if i ≤ w then bt f i else 0)
    (hx : V f w = x) (hxn : x < 2 ^ n) : V g n = x := by
  rw [V_pad f g w n hg]
  rcases Nat.le_total n w with h | h
  · rw [min_eq_left h]; exact V_trunc f w n x hx hxn h
  · rw [min_eq_right h]; exact hx

/-! ### the prefix copy -/

def piBody (dst : ℕ) : Cmd := .seq (.rd 819 1 818 0) (.seq (.ifZero 819 .skip (.setK 819 1)) (.wr dst 818 1 819))

def piC (dst : ℕ) : Cmd := .loop 2 818 (piBody dst)

theorem piC_run (dst : ℕ) (hd : dst ≠ 1) (st : St) (n : ℕ) (hn : st.sc 2 = n) :
    (∀ q, q < n → (Cmd.run (piC dst) st).1.ar dst (q + 1) = bt (st.ar 1) q) ∧
    ArKeep dst st (Cmd.run (piC dst) st).1 ∧ ScKeep ZP2 st (Cmd.run (piC dst) st).1 ∧ (Cmd.run (piC dst) st).2 ≤ n * 8 + 1 := by
  have key := mapLoop (b := 2) (c := 818) (body := piBody dst) dst (fun j => bt (st.ar 1) j) ZP2 7 st n hn
    (by unfold ZP2; omega) (fun j => bt_le _ _) (by
      intro t j hj h3 h4
      have hs : t.ar 1 = st.ar 1 := h3 1 (Ne.symm hd)
      by_cases a : st.ar 1 j = 0
      · simp [piBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_wr, hs, a, bt, Function.update_apply, St.setSc]
        try (intro y hy; simp only [ZP2, not_or] at hy; simp [hy.1, hy.2])
      · simp [piBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_wr, hs, a, bt, Function.update_apply, St.setSc]
        try (intro y hy; simp only [ZP2, not_or] at hy; simp [hy.1, hy.2]))
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  refine ⟨fun q hq => ?_, k3, k4, by unfold piC; omega⟩
  have := k2 (q + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at this
  exact this

end ECDLP.L80
