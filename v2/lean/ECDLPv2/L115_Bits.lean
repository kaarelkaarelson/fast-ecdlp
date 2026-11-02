import ECDLPv2.L113_Out
import ECDLPv2.L115_Look

/-!
# L115 / Bits: a scalar to a bit array
`toBitsC Q w` : with scalar `860 = v`, writes the low `w` bits of `v` into cells `1..w` of array `Q` (by repeated halving through scalars `860, 861, 862`) and sets
scalar `710 = w`.  `toBitsC_run` : if `v < 2^w` then `V (Q after) w = v`; cost `≤ w (14 v + 50) + 5`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76 Ex Uni

attribute [local irreducible] cset

def toBitsBody (Q : ℕ) : Cmd :=
  .seq (cset (.mod (.var 860) (.lit 2)) 862) (.seq (.wr Q 861 1 862) (cset (.div (.var 860) (.lit 2)) 860))

def toBitsC (Q w : ℕ) : Cmd := .seq (.setK 710 w) (.loop 710 861 (toBitsBody Q))

theorem V_bits (f : ℕ → ℕ) (v : ℕ) : ∀ w, (∀ j, j < w → f (j + 1) = (v / 2 ^ j) % 2) → V f w = v % 2 ^ w
  | 0, _ => by simp [V, numCells, Nat.mod_one]
  | w + 1, h => by
      rw [V_snoc, V_bits f v w (fun j hj => h j (by omega)), Nat.mod_pow_succ]
      have : bt f (w + 1) = (v / 2 ^ w) % 2 := by
        unfold bt
        rw [h w (by omega)]
        have := Nat.mod_lt (v / 2 ^ w) (show 0 < 2 by norm_num)
        split_ifs with h0
        · exact h0.symm
        · omega
      rw [this]; ring

theorem toBitsBody_step (Q : ℕ) (t : St) (i v : ℕ) (h860 : t.sc 860 = v / 2 ^ i) :
    let r := Cmd.run (toBitsBody Q) (t.setSc 861 i)
    r.1.sc 860 = v / 2 ^ (i + 1) ∧ r.1.ar Q = Function.update (t.ar Q) (i + 1) ((v / 2 ^ i) % 2) ∧
    (∀ a, a ≠ Q → r.1.ar a = t.ar a) ∧
    (∀ y, y < 1000 → y ≠ 860 → y ≠ 861 → y ≠ 862 → r.1.sc y = t.sc y) ∧ r.2 ≤ 14 * v + 50 := by
  intro r
  set t1 := t.setSc 861 i with ht1
  have e860 : t1.sc 860 = v / 2 ^ i := by simp [ht1, St.setSc, h860]
  obtain ⟨a1, a2, a3, a4⟩ := cset_spec (.mod (.var 860) (.lit 2)) 862 t1 (by simp [VB]) (by norm_num)
  set t2 := (Cmd.run (cset (.mod (.var 860) (.lit 2)) 862) t1).1 with ht2
  have e2 : t2.sc 862 = (v / 2 ^ i) % 2 := by rw [a1]; simp [Ex.eval, e860]
  have e2' : t2.sc 861 = i := by rw [a2 861 (by norm_num) (by norm_num)]; simp [ht1, St.setSc]
  have e2'' : t2.sc 860 = v / 2 ^ i := by rw [a2 860 (by norm_num) (by norm_num), e860]
  set t3 := (Cmd.run (.wr Q 861 1 862) t2).1 with ht3
  have h3 : t3 = t2.setAr Q (t2.sc 861 + 1) (t2.sc 862) := by rw [ht3, Cmd.run_wr]
  obtain ⟨b1, b2, b3, b4⟩ := cset_spec (.div (.var 860) (.lit 2)) 860 t3 (by simp [VB]) (by norm_num)
  have e3 : t3.sc 860 = v / 2 ^ i := by rw [h3]; simp [e2'']
  have hrun : r = ((Cmd.run (cset (.div (.var 860) (.lit 2)) 860) t3).1,
      (Cmd.run (cset (.mod (.var 860) (.lit 2)) 862) t1).2 + ((Cmd.run (.wr Q 861 1 862) t2).2 +
        (Cmd.run (cset (.div (.var 860) (.lit 2)) 860) t3).2 + 1) + 1) := by
    show Cmd.run (toBitsBody Q) t1 = _
    simp only [toBitsBody, Cmd.run_seq, ← ht2, ← ht3]
  have c1 : (Cmd.run (cset (.mod (.var 860) (.lit 2)) 862) t1).2 ≤ 7 * (v / 2 ^ i) + 18 := by
    have := a4; simp only [Ex.cost, Ex.eval, e860] at this; omega
  have c3 : (Cmd.run (cset (.div (.var 860) (.lit 2)) 860) t3).2 ≤ 7 * (v / 2 ^ i) + 18 := by
    have := b4; simp only [Ex.cost, Ex.eval, e3] at this; omega
  have hv : v / 2 ^ i ≤ v := Nat.div_le_self _ _
  have c2 : (Cmd.run (.wr Q 861 1 862) t2).2 = 1 := by rw [Cmd.run_wr]
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [b1]; simp only [Ex.eval, e3]
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  · simp only
    rw [b3, h3]; simp [St.setAr, St.putAr, e2, e2', a3, ht1]
  · intro a ha
    simp only
    rw [b3, h3]; simp [St.setAr, St.putAr, Function.update_of_ne ha, a3, ht1]
  · intro y hy h1 h2 h3'
    simp only
    rw [b2 y hy h1, h3]
    simp [St.setAr, a2 y hy h3', ht1, St.setSc, Function.update_of_ne h2]
  · simp only
    omega

theorem toBitsC_run (Q w : ℕ) (st : St) (v : ℕ) (h860 : st.sc 860 = v) (hv : v < 2 ^ w) :
    V ((Cmd.run (toBitsC Q w) st).1.ar Q) w = v ∧ (Cmd.run (toBitsC Q w) st).1.sc 710 = w ∧
    (∀ a, a ≠ Q → (Cmd.run (toBitsC Q w) st).1.ar a = st.ar a) ∧
    (∀ y, y < 1000 → y ≠ 710 → y ≠ 860 → y ≠ 861 → y ≠ 862 → (Cmd.run (toBitsC Q w) st).1.sc y = st.sc y) ∧
    (Cmd.run (toBitsC Q w) st).2 ≤ w * (14 * v + 51) + 3 := by
  set s1 := st.setSc 710 w with hs1
  have w1 : s1.sc 710 = w := by simp [hs1, St.setSc]
  let P : ℕ → St → Prop := fun i t => t.sc 860 = v / 2 ^ i ∧
    (∀ j, j < i → t.ar Q (j + 1) = (v / 2 ^ j) % 2) ∧ (∀ j, i ≤ j → t.ar Q (j + 1) = st.ar Q (j + 1)) ∧
    t.ar Q 0 = st.ar Q 0 ∧
    (∀ a, a ≠ Q → t.ar a = st.ar a) ∧ (∀ y, y < 1000 → y ≠ 710 → y ≠ 860 → y ≠ 861 → y ≠ 862 → t.sc y = st.sc y) ∧ t.sc 710 = w
  have h0 : P 0 s1 := ⟨by simp [hs1, St.setSc, h860], fun j hj => absurd hj (by omega), fun _ _ => rfl, rfl, fun _ _ => rfl,
    fun y hy h1 _ _ _ => by simp [hs1, St.setSc, Function.update_of_ne h1], w1⟩
  have step : ∀ i t, P i t → P (i + 1) (Cmd.run (toBitsBody Q) (t.setSc 861 i)).1 ∧
      (Cmd.run (toBitsBody Q) (t.setSc 861 i)).2 ≤ 14 * v + 50 := by
    intro i t ⟨p1, p2, p3, p3', p4, p5, p6⟩
    obtain ⟨r1, r2, r3, r4, r5⟩ := toBitsBody_step Q t i v p1
    refine ⟨⟨r1, ?_, ?_, ?_, fun a ha => by rw [r3 a ha, p4 a ha], fun y hy h1 h2 h3 h4 => by rw [r4 y hy h2 h3 h4, p5 y hy h1 h2 h3 h4], ?_⟩, r5⟩
    · intro j hj
      rw [r2]
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne (by omega)]; exact p2 j (by omega)
    · intro j hj
      rw [r2, Function.update_of_ne (by omega)]; exact p3 j (by omega)
    · rw [r2, Function.update_of_ne (by omega)]; exact p3'
    · rw [r4 710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact p6
  have hI := Cmd.loop_inv (b := 710) (c := 861) (body := toBitsBody Q) (st := s1) P h0 (fun i t _ hp => (step i t hp).1)
  have hC := Cmd.loop_cost_le (b := 710) (c := 861) (body := toBitsBody Q) (st := s1) P (14 * v + 50) h0
    (fun i t _ hp => (step i t hp).1) (fun i t _ hp => (step i t hp).2)
  rw [w1] at hI hC
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  have hrun : Cmd.run (toBitsC Q w) st = ((Cmd.run (.loop 710 861 (toBitsBody Q)) s1).1,
      1 + (Cmd.run (.loop 710 861 (toBitsBody Q)) s1).2 + 1) := by
    simp only [toBitsC, Cmd.run_seq, Cmd.run_setK]
    rfl
  rw [hrun]
  have hvq := V_bits _ v w (fun j hj => i2 j hj)
  refine ⟨?_, i7, i5, i6, ?_⟩
  · rw [hvq]; exact Nat.mod_eq_of_lt hv
  · simp only
    have : w * (14 * v + 50 + 1) + 1 + 2 = w * (14 * v + 51) + 3 := by ring
    omega

end ECDLP.L115
