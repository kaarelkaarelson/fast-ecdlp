import ECDLP.L85_A_Count

/-!
# L69 / Uni: the cost of the counting command for a general top (Rudich `UniCost`)
-/
namespace ECDLP.L85A
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one modulus.** -/
theorem modBody_cost' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface DB F L0X SX TX) (hS : F.Spec) {V n k ℓ : ℕ} (s : St) (j : ℕ) (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (h303 : s.sc 303 ≤ V)
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k') (hR : 2 ≤ j → F.FamOK V j K0u ℓ n) (hjV : j ≤ V)
    (hnV : n ≤ V) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).2 ≤ 100 * YB DB V ^ 3 := by
  have hY := YB_ge DB V
  have hPB := PB_le_YB DB V
  have hY3 : YB DB V ≤ YB DB V ^ 3 := Nat.le_self_pow (by norm_num) _
  have hY23 : YB DB V ^ 2 ≤ YB DB V ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  set s' := s.setSc 300 j
  set t1 := (Cmd.run (.copy 10 300) s').1
  set t2 := (Cmd.run (.setK 315 2) t1).1
  have g2 : ∀ y, y ≠ 315 → y ≠ 10 → y ≠ 300 → t2.sc y = s.sc y := fun y a b c => by
    simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have j10 : t2.sc 10 = j := by simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy]
  have c315 : t2.sc 315 = 2 := by simp [t2, Cmd.run_setK]
  have e : (Cmd.run (modBody (UP' L0X SX TX)) s').2 = (Cmd.run (.copy 10 300) s').2 + ((Cmd.run (.setK 315 2) t1).2 +
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX)) (.seq (dmLoop UP) (cset flagE 301)))) t2).2 + 1) + 1 := by
    rw [show modBody (UP' L0X SX TX) = .seq (.copy 10 300) (.seq (.setK 315 2) (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX))
      (.seq (dmLoop UP) (cset flagE 301))))) from rfl, seq_cost, seq_cost]
  rw [e, Cmd.run_copy, Cmd.run_setK, Cmd.run_ifLt, j10, c315]
  by_cases hj : j < 2
  · rw [if_pos hj, Cmd.run_skip]; omega
  rw [if_neg hj]
  have R := hR (by omega)
  have hm : 1 < j := by omega
  have kc := countM_cost' hI hS (n := n) (k := k) (ℓ := ℓ) t2 hm j10
    (by rw [g2 11 (by norm_num) (by norm_num) (by norm_num), h11])
    (by rw [g2 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [g2 2 (by norm_num) (by norm_num) (by norm_num), h2]) hkn
    (by rw [g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [g2 316 (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [g2 303 (by norm_num) (by norm_num) (by norm_num)]; exact h303)
    (fun v k' h => by have := topOk_lt h; have := h.1; rw [g2 v (by omega) (by omega) (by omega), htok v k' h])
    R hℓ hlv
  rw [seq_cost, seq_cost]
  set t3 := (Cmd.run (countM (UP' L0X SX TX)) t2).1 with ht3
  have f3 : ∀ y < 990, ¬ WC y → t3.sc y = t2.sc y := fun y hy hW => by rw [ht3]; exact countM_frame' hI t2 hy hW
  have m3 : t3.sc 10 = j := by rw [f3 10 (by norm_num) (by simp [WC, WP, WL]), j10]
  have z3 : t3.sc 0 = n := by
    rw [f3 0 (by norm_num) (by simp [WC, WP, WL]), g2 0 (by norm_num) (by norm_num) (by norm_num), h0]
  have w3 : t3.sc 2 = k := by
    rw [f3 2 (by norm_num) (by simp [WC, WP, WL]), g2 2 (by norm_num) (by norm_num) (by norm_num), h2]
  have l3 : t3.sc 307 = ℓ := by
    rw [f3 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307]
  have c3 : t3.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n := by
    rw [f3 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12]
  obtain ⟨kd, d4⟩ := dmLoop_cost (D := DB) t3 hm l3 c3 m3 (hI.ok_deep R) hℓ hlv
  obtain ⟨-, f4, -⟩ := dmLoop_spec t3 (by omega) l3 c3 m3
  set t4 := (Cmd.run (dmLoop UP) t3).1 with ht4
  obtain ⟨-, -, -, k4⟩ := cset_spec flagE 301 t4 (by simp [VB, flagE, ifEq, c1E, nsum, xBit, bitRd]) (by norm_num)
  have m4 : t4.sc 10 = j := by rw [ht4, f4 10 (by norm_num) (by simp [WD]) (by norm_num), m3]
  have z4 : t4.sc 0 = n := by rw [ht4, f4 0 (by norm_num) (by simp [WD]) (by norm_num), z3]
  have w4 : t4.sc 2 = k := by rw [ht4, f4 2 (by norm_num) (by simp [WD]) (by norm_num), w3]
  have kf : (Cmd.run (cset flagE 301) t4).2 ≤ 2 * PB DB V + 60 :=
    le_trans k4 (flagE_cost (D := DB) (by omega) m4 hm hjV (by rw [w4, z4]; exact hkn) (by rw [z4]; exact hnV))
  omega


set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of the counting command**, polynomial in `YB DB V`. -/
theorem uniC_cost_le' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface DB F L0X SX TX) (hS : F.Spec) (V : ℕ) (st : St) (hkn : st.sc 2 < st.sc 0) (R : F.UniReq V (st.sc 0)) :
    (Cmd.run (uniC (UP' L0X SX TX)) st).2 ≤ 200 * YB DB V ^ 4 := by
  have htop := R.main.top
  have hM : 2 * F.Mof K0u (ellOf (st.sc 0)) (st.sc 0) + 1 ≤ V := R.main.hM
  have hnp := R.np
  have hlv := R.lv
  have hsm := R.small
  have hkb := R.kb
  set n := st.sc 0
  set k := st.sc 2
  set ℓ := ellOf n
  set L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n
  have hW := @le_Wv V
  have hY := YB_ge DB V
  have hPB := PB_le_YB DB V
  have hY2 : YB DB V ^ 2 ≤ YB DB V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY1 : YB DB V ≤ YB DB V ^ 4 := Nat.le_self_pow (by norm_num) _
  have hMof : F.Mof K0u ℓ n = n + mlogN K0u ℓ L + 4 := rfl
  have hml : mlogN K0u ℓ L ≤ V := by omega
  have R2 := htop 2 le_rfl (by omega)
  have k1 := setup_cost' hI hS st R2 hml hnp hlv hsm hkb
  obtain ⟨s11, s307, s316, s12, s303, s310, stok, sfr, sar⟩ := setup_spec' hI st
  set b1 := (Cmd.run (setup (UP' L0X SX TX)) st).1 with hb1
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := mE) (by simp [mE, VB]) (show 314 < 1000 by norm_num) b1
  set b2 := (Cmd.run (cset mE 314) b1).1 with hb2
  have b0 : b1.sc 0 = n := sfr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2' : b1.sc 2 = k := sfr 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have k2' : (Cmd.run (cset mE 314) b1).2 ≤ PB DB V := by
    refine le_trans k2 (cost_le_PB ?_ (by simp [mE, Ex.dp]))
    have e0 : vw b1 0 = n := by rw [vw_lt (by norm_num), b0]
    have e310 : vw b1 310 = mlogN K0u ℓ L := by rw [vw_lt (by norm_num), s310]
    unfold mE
    refine B_add (B_mul (B_lit (by omega)) (B_add (B_add (B_var (by rw [e0]; omega)) (B_var (by rw [e310]; omega))
      (by simp only [Ex.eval, e0, e310]; omega)) (B_lit (by omega)) (by simp only [Ex.eval, e0, e310]; omega))
      (by simp only [Ex.eval, e0, e310]; omega)) (B_lit (by omega)) (by simp only [Ex.eval, e0, e310]; omega)
  set b3 := (Cmd.run (.setK 301 0) b2).1 with hb3
  have g3 : ∀ y < 1000, y ≠ 301 → y ≠ 314 → b3.sc y = b1.sc y := fun y hy h1 h2 => by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne h1]
    rw [← vw_lt hy, v2, Function.update_of_ne h2, vw_lt hy]
  have M314 : b3.sc 314 = 2 * F.Mof K0u ℓ n + 1 := by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne (show (314 : ℕ) ≠ 301 by norm_num)]
    rw [← vw_lt (show 314 < 1000 by norm_num), v2, Function.update_self]
    simp only [mE, Ex.eval, vw_lt (show 0 < 1000 by norm_num), vw_lt (show 310 < 1000 by norm_num), b0, s310]
    rfl
  -- the moduli loop
  let MI : ℕ → St → Prop := fun _ s => ∀ y < 990, ¬ WM y → s.sc y = b3.sc y
  have hstep : ∀ j s, j < b3.sc 314 → MI j s → MI (j + 1) (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).1 ∧
      (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).2 ≤ 100 * YB DB V ^ 3 := by
    intro j s hj hs
    have q : ∀ y, y ∈ [11, 0, 2, 307, 316, 12, 303] → s.sc y = b1.sc y := fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [hs y (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 y (by omega) (by omega) (by omega)]
    refine ⟨fun y hy hW => ?_, ?_⟩
    · rw [modBody_frame' hI _ hy hW]
      simp only [St.setSc_sc]
      rw [Function.update_of_ne (by simp only [WM] at hW; omega)]
      exact hs y hy hW
    · rw [M314] at hj
      exact modBody_cost' hI hS s j (n := n) (k := k) (ℓ := ℓ) (by rw [q 11 (by simp), s11]) (by rw [q 0 (by simp), b0])
        (by rw [q 2 (by simp), b2']) hkn (by rw [q 307 (by simp), s307]) (by rw [q 316 (by simp), s316])
        (by rw [q 12 (by simp), s12]) (by rw [q 303 (by simp), s303]; exact hnp)
        (fun v k' h => by
          have := topOk_lt h; have := h.1
          rw [hs v (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 v (by omega) (by omega) (by omega),
            stok v k' h])
        (fun h2 => htop j h2 (by omega)) (by omega) (by omega) (by omega) hlv
  have kL := Cmd.loop_cost_le (b := 314) (c := 300) (body := modBody (UP' L0X SX TX)) (st := b3) MI (100 * YB DB V ^ 3)
    (fun _ _ _ => rfl) (fun j s hj hs => (hstep j s hj hs).1) (fun j s hj hs => (hstep j s hj hs).2)
  rw [M314] at kL
  have kL' : (Cmd.run (.loop 314 300 (modBody (UP' L0X SX TX))) b3).2 ≤ 102 * YB DB V ^ 4 := le_trans kL (loop_le (V := V) (k := 100) (e := 3) (le_trans (by omega : 2 * F.Mof K0u ℓ n + 1 ≤ V) hW))
  set b4 := (Cmd.run (.loop 314 300 (modBody (UP' L0X SX TX))) b3).1
  obtain ⟨-, -, k5⟩ := vw_cset (e := Uni.bitE) (by simp [Uni.bitE, VB]) (show 3 < 1000 by norm_num) b4
  have k5' : (Cmd.run (cset Uni.bitE 3) b4).2 ≤ 9 := le_trans k5 (bitE_cost _ _)
  have hle := seq_le k1 (seq_le k2' (seq_le (le_refl (Cmd.run (.setK 301 0) b2).2) (seq_le kL' k5')))
  rw [show uniC (UP' L0X SX TX) = .seq (setup (UP' L0X SX TX)) (.seq (cset mE 314) (.seq (.setK 301 0) (.seq (.loop 314 300 (modBody (UP' L0X SX TX)))
    (cset Uni.bitE 3)))) from rfl]
  refine le_trans hle ?_
  simp only [Cmd.run_setK]
  omega


/-- **The counting command with the family's top costs at most `c · (V+1)^E`** whenever `V` meets the family's
`UniReq` at the input length (Rudich `uniC_cost`, general top). -/
theorem uniC_cost' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface DB F L0X SX TX) (hS : F.Spec) :
    ∃ c : ℕ, ∀ (V : ℕ) (st : St), st.sc 2 < st.sc 0 → F.UniReq V (st.sc 0) →
      (Cmd.run (uniC (UP' L0X SX TX)) st).2 ≤ c * (V + 1) ^ (24 * DB + 8) := by
  refine ⟨200 * (4 * 4096 ^ DB) ^ 4, fun V st hkn R => le_trans (uniC_cost_le' hI hS V st hkn R) ?_⟩
  have h := Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (UCost85.YB_le (D := DB) V) 4)
  generalize V + 1 = X at h ⊢
  generalize (4096 : ℕ) ^ DB = c at h ⊢
  refine le_trans h (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_assoc]
  congr 3
  ring

end ECDLP.L85A
