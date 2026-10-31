import ECDLP.L76_Num

/-!
# L76 / Map: cellwise loops (`copyA`, `zeroA`) and the generic `mapLoop` lemma
Scratch scalars `731 .. 735`.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- **Generic cellwise loop.**  If one turn `j` writes the bit `v j` into cell `j+1` of `dst` and touches otherwise only
scalars in `Z` (including the counter `c`), then `n` turns write `v` into the cells `1..n`. -/
theorem mapLoop {b c : ℕ} {body : Cmd} (dst : ℕ) (v : ℕ → ℕ) (Z : ℕ → Prop) (K : ℕ) (st : St) (n : ℕ)
    (hn : st.sc b = n) (hc : Z c) (hv : ∀ j, v j ≤ 1)
    (hb : ∀ (t : St) (j : ℕ), j < n → ArKeep dst st t → ScKeep Z st t →
      (Cmd.run body (t.setSc c j)).1.ar = Function.update t.ar dst (Function.update (t.ar dst) (j + 1) (v j)) ∧
      (∀ y, ¬ Z y → (Cmd.run body (t.setSc c j)).1.sc y = t.sc y) ∧ (Cmd.run body (t.setSc c j)).2 ≤ K) :
    Cells n ((Cmd.run (.loop b c body) st).1.ar dst) (st.ar dst) ∧
    (∀ i, 1 ≤ i → i ≤ n → (Cmd.run (.loop b c body) st).1.ar dst i = v (i - 1)) ∧
    ArKeep dst st (Cmd.run (.loop b c body) st).1 ∧ ScKeep Z st (Cmd.run (.loop b c body) st).1 ∧
    (Cmd.run (.loop b c body) st).2 ≤ n * (K + 1) + 1 := by
  let P : ℕ → St → Prop := fun j t =>
    Cells j (t.ar dst) (st.ar dst) ∧ (∀ i, 1 ≤ i → i ≤ j → t.ar dst i = v (i - 1)) ∧ ArKeep dst st t ∧ ScKeep Z st t
  have h0 : P 0 st := ⟨fun i => ⟨fun h => by omega, fun _ => rfl⟩, fun i h1 h2 => by omega, fun a _ => rfl, fun y _ => rfl⟩
  have hstep : ∀ j t, j < st.sc b → P j t → P (j + 1) (Cmd.run body (t.setSc c j)).1 := by
    intro j t hj ⟨c1, c2, c3, c4⟩
    obtain ⟨e1, e2, e3⟩ := hb t j (by omega) c3 c4
    have hupd : (Cmd.run body (t.setSc c j)).1.ar dst = Function.update (t.ar dst) (j + 1) (v j) := by
      rw [e1]; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hupd]; exact Cells_succ c1 _ (hv j)
    · intro i h1 h2
      rw [hupd]
      by_cases hi : i = j + 1
      · subst hi; simp
      · simp [Function.update_apply, hi]; exact c2 i h1 (by omega)
    · intro a ha; rw [e1]; simp [Function.update_apply, ha]; exact c3 a ha
    · intro y hy; rw [e2 y hy]; exact c4 y hy
  have hI := Cmd.loop_inv (b := b) (c := c) (body := body) P h0 hstep
  have hC := Cmd.loop_cost_le (b := b) (c := c) (body := body) P K h0 hstep
    (fun j t hj hp => (hb t j (by omega) hp.2.2.1 hp.2.2.2).2.2)
  rw [hn] at hI hC
  exact ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2, hC⟩

/-- the registers `731 .. 735` -/
def ZC (y : ℕ) : Prop := 731 ≤ y ∧ y ≤ 735

def copyBody (dst src : ℕ) : Cmd :=
  .seq (.rd 733 src 731 1) (.seq (.ifZero 733 .skip (.setK 733 1)) (.wr dst 731 1 733))

/-- `dst[1..W] := bits of src[1..W]` -/
def copyA (dst src : ℕ) : Cmd := .loop 710 731 (copyBody dst src)

theorem copyA_run (dst src : ℕ) (hds : dst ≠ src) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    Cells n ((Cmd.run (copyA dst src) st).1.ar dst) (st.ar dst) ∧
    (∀ i, 1 ≤ i → i ≤ n → (Cmd.run (copyA dst src) st).1.ar dst i = bt (st.ar src) i) ∧
    V ((Cmd.run (copyA dst src) st).1.ar dst) n = V (st.ar src) n ∧
    ArKeep dst st (Cmd.run (copyA dst src) st).1 ∧ ScKeep ZC st (Cmd.run (copyA dst src) st).1 ∧
    (Cmd.run (copyA dst src) st).2 ≤ 7 * n + 1 := by
  have key := mapLoop (b := 710) (c := 731) (body := copyBody dst src) dst (fun j => bt (st.ar src) (j + 1)) ZC 6 st n hW
    (by unfold ZC; omega) (fun j => bt_le _ _) (by
      intro t j hj h3 h4
      have hs : t.ar src = st.ar src := h3 src (Ne.symm hds)
      have h710 : t.sc 710 = n := by rw [h4 710 (by unfold ZC; omega)]; exact hW
      by_cases a : st.ar src (j + 1) = 0
      · simp [copyBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_wr, hs, a, bt, Function.update_apply]
        try (intro y hy; simp only [ZC, not_and, not_le] at hy
             split_ifs <;> first | rfl | (exfalso; omega))
      · simp [copyBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_wr, hs, a, bt, Function.update_apply]
        try (intro y hy; simp only [ZC, not_and, not_le] at hy
             split_ifs <;> first | rfl | (exfalso; omega)))
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  have k2' : ∀ i, 1 ≤ i → i ≤ n → (Cmd.run (copyA dst src) st).1.ar dst i = bt (st.ar src) i := by
    intro i h1 h2; have := k2 i h1 h2; rw [show i - 1 + 1 = i by omega] at this; exact this
  refine ⟨k1, k2', ?_, k3, k4, by unfold copyA; omega⟩
  · refine V_congr_bt fun j h1 h2 => ?_
    have := k2' j h1 h2
    unfold bt at this ⊢
    rw [this]; split_ifs <;> simp_all
  
end ECDLP.L76
