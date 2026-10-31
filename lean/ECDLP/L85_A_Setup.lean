import ECDLP.L85_A_Iface

/-!
# L69 / Setup: cost and value of the parameters and the sweep for a general top (Rudich `setup_cost (D := DB)`, `setup_spec`)
-/
namespace ECDLP.L85A
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of the parameters and the sweep.** -/
theorem setup_cost' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface DB F L0X SX TX) (hS : F.Spec) {V : ℕ} (st : St)
    (hT : F.FamOK V 2 K0u (ellOf (st.sc 0)) (st.sc 0))
    (hml : mlogN K0u (ellOf (st.sc 0)) (F.Ltop (Kb K0u (ellOf (st.sc 0))) (Gs K0u (ellOf (st.sc 0)))
      (st.sc 0)) ≤ V)
    (hnp : NPof K0u (ellOf (st.sc 0)) (F.Ltop (Kb K0u (ellOf (st.sc 0))) (Gs K0u (ellOf (st.sc 0)))
      (st.sc 0)) ≤ V)
    (hlv : lvlV (Kb K0u (ellOf (st.sc 0))) ≤ V) (hsm : st.sc 0 + ellOf (st.sc 0) + 64 ≤ V)
    (hkb : Kb K0u (ellOf (st.sc 0) + 1) ^ 40 ≤ V) :
    (Cmd.run (setup (UP' L0X SX TX)) st).2 ≤ 60 * YB DB V ^ 2 := by
  set n := st.sc 0
  set ℓ := ellOf n
  set K := Kb K0u ℓ
  set L := F.Ltop K (Gs K0u ℓ) n
  have hW := @le_Wv V
  have RW := hS.ok_mono hT hW
  have hY := YB_ge DB V
  have hPB := PB_le_YB DB V
  have hY2 : YB DB V ≤ YB DB V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hg : 0 < Gs K0u ℓ := Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ hg) (hI.ok_KG hT)
  have hℓV : ellOf n ≤ Wv V := by show ℓ ≤ Wv V; omega
  have hKbV : Kb K0u (ellOf n) ≤ Wv V := by show K ≤ Wv V; omega
  -- e1: 11 := s
  obtain ⟨v1, a1, k1⟩ := vw_cset (e := sE) (by simp [sE, pow2, VB]) (show 11 < 1000 by norm_num) st
  set e1 := (Cmd.run (cset sE 11) st).1
  have k1' : (Cmd.run (cset sE 11) st).2 ≤ PB DB V :=
    le_trans k1 (cost_le_PB (sE_bdd (by rw [vw_lt (by norm_num)]; exact (hI.ok_hn RW))) (le_trans dpT_sE (by norm_num)))
  rw [eval_sE, vw_lt (show 0 < 1000 by norm_num)] at v1
  -- e2: 307 := ℓ
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := ellE) (by simp [ellE, kbE, powE, VB]) (show 307 < 1000 by norm_num) e1
  set e2 := (Cmd.run (cset ellE 307) e1).1
  have z1 : vw e1 0 = n := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (show 0 < 1000 by norm_num)]
  have k2' : (Cmd.run (cset ellE 307) e1).2 ≤ PB DB V :=
    le_trans k2 (cost_le_PB (ellE_bdd z1 (by omega) (by omega) (le_trans hkb hW)) dp_ellE)
  rw [eval_ellE, z1] at v2
  -- e3: 43 := K
  obtain ⟨v3, a3, k3⟩ := vw_cset (vb_kbE 307 (by norm_num)) (show 43 < 1000 by norm_num) e2
  set e3 := (Cmd.run (cset (kbE 307) 43) e2).1
  have k3' : (Cmd.run (cset (kbE 307) 43) e2).2 ≤ PB DB V :=
    le_trans k3 (cost_le_PB (kbE_bdd (by rw [v2, Function.update_self]; exact hℓV)
      (by rw [v2, Function.update_self]; exact hKbV)) (dp_kbE 307))
  rw [eval_kbE, v2, Function.update_self] at v3
  obtain ⟨v4, a4, -⟩ := vw_copy (show 316 < 1000 by norm_num) (show 43 < 1000 by norm_num) e3
  set e4 := (Cmd.run (.copy 316 43) e3).1
  rw [v3, Function.update_self] at v4
  have K4 : e4.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), Function.update_self]
  have k5' : (Cmd.run UP.tset e4).2 ≤ 15 * PB DB V := by
    rw [show UP.tset = topSet 43 from rfl]
    obtain ⟨-, -, -, -, h5⟩ := topSet_spec (q := 43) e4 K4 (Or.inr (by norm_num)) (by norm_num)
    have := set_le_PB (D := DB) (V := V) (K := K) (by omega)
    omega
  obtain ⟨t1, t2, a5⟩ := UP_ok.tset e4
  set e5 := (Cmd.run UP.tset e4).1
  rw [K4] at t1
  have w5 : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → vw e5 y = vw e4 y := fun y hy h1 h3 h59 => by
    rw [vw_lt hy, vw_lt hy, t2 y hy h1 h3 h59]
  obtain ⟨v6, a6, k6⟩ := vw_cset hI.vl0 (show 12 < 1000 by norm_num) e5
  set e6 := (Cmd.run (cset L0X 12) e5).1
  have tk5 : ∀ v k, tokU K v k → vw e5 v = k := fun v k h => by
    have := topOk_lt h; rw [vw_lt (by omega), t1 v k h]
  have s5 : vw e5 11 = sOf n := by
    rw [w5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), v1, Function.update_self]
  have n5 : vw e5 0 = n := by
    rw [w5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), v1,
      Function.update_of_ne (by norm_num), vw_lt (show 0 < 1000 by norm_num)]
  have k6' : (Cmd.run (cset L0X 12) e5).2 ≤ PB DB V := by
    refine le_trans k6 ?_
    exact hI.l0_cost V ℓ n (vw e5) e5.ar RW tk5 s5 n5
  rw [hI.l0_eval K n (vw e5) e5.ar tk5 s5 n5] at v6
  obtain ⟨v7, a7, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 12 < 1000 by norm_num) e6
  set e7 := (Cmd.run (.copy 40 12) e6).1
  obtain ⟨v8, a8, -⟩ := vw_setK (k := 1) (show 303 < 1000 by norm_num) e7
  set e8 := (Cmd.run (.setK 303 1) e7).1
  obtain ⟨v10, a10, -⟩ := vw_setK (k := 0) (show 310 < 1000 by norm_num) e8
  set e10 := (Cmd.run (.setK 310 0) e8).1
  have L6 : vw e6 12 = L := by rw [v6, Function.update_self]; rfl
  have g10 : ∀ y, y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → vw e10 y = vw e6 y := fun y a _ c d => by
    rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
      Function.update_of_ne d]
  have k11 := sweep_cost (D := DB) e10 (ℓ := ℓ) (L := L)
    (by rw [← vw_lt (show 307 < 1000 by norm_num), g10 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      v6, Function.update_of_ne (by norm_num), w5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4]
        simp [ℓ, n])
    (by rw [← vw_lt (show 40 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_of_ne (by norm_num), v7, Function.update_self, L6])
    (by rw [← vw_lt (show 303 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_self])
    (by rw [← vw_lt (show 310 < 1000 by norm_num), v10, Function.update_self])
    (hI.ok_deep hT) (by omega) hlv hnp hml
  have hle := seq_le k1' (seq_le k2' (seq_le k3' (seq_le (le_refl (Cmd.run (.copy 316 43) e3).2) (seq_le k5'
    (seq_le k6' (seq_le (le_refl (Cmd.run (.copy 40 12) e6).2) (seq_le (le_refl (Cmd.run (.setK 303 1) e7).2)
      (seq_le (le_refl (Cmd.run (.setK 310 0) e8).2) k11))))))))
  have e : (Cmd.run (setup (UP' L0X SX TX)) st).2 = (Cmd.run (.seq (cset sE 11) <| .seq (cset ellE 307) <|
      .seq (cset (kbE 307) 43) <| .seq (.copy 316 43) <|
      .seq UP.tset <| .seq (cset L0X 12) <|
      .seq (.copy 40 12) <| .seq (.setK 303 1) <| .seq (.setK 310 0) <|
      .loop 307 306 (sweepBody UP)) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy, Cmd.run_setK]
  omega


set_option maxRecDepth 20000 in
/-- **The parameters and the sweep.** -/
theorem setup_spec' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface DB F L0X SX TX) (st : St) :
    let n := st.sc 0
    let ℓ := ellOf n
    let K := Kb K0u ℓ
    let L := F.Ltop K (Gs K0u ℓ) n
    let r := (Cmd.run (setup (UP' L0X SX TX)) st).1
    r.sc 11 = sOf n ∧ r.sc 307 = ℓ ∧ r.sc 316 = K ∧ r.sc 12 = L ∧ r.sc 303 = NPof K0u ℓ L ∧
      r.sc 310 = mlogN K0u ℓ L ∧ (∀ v k, tokU K v k → r.sc v = k) ∧
      (∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → ¬ WS y → y ≠ 306 → y ≠ 11 → y ≠ 307 → y ≠ 316 →
        y ≠ 12 → r.sc y = st.sc y) ∧ r.ar = st.ar := by
  intro n ℓ K L r
  obtain ⟨v1, a1, -⟩ := vw_cset (e := sE) (by simp [sE, pow2, VB]) (show 11 < 1000 by norm_num) st
  set e1 := (Cmd.run (cset sE 11) st).1
  rw [eval_sE, vw_lt (show 0 < 1000 by norm_num)] at v1
  obtain ⟨v2, a2, -⟩ := vw_cset (e := ellE) (by simp [ellE, kbE, powE, VB]) (show 307 < 1000 by norm_num) e1
  set e2 := (Cmd.run (cset ellE 307) e1).1
  rw [eval_ellE, v1, Function.update_of_ne (by norm_num), vw_lt (show 0 < 1000 by norm_num)] at v2
  obtain ⟨v3, a3, -⟩ := vw_cset (vb_kbE 307 (by norm_num)) (show 43 < 1000 by norm_num) e2
  set e3 := (Cmd.run (cset (kbE 307) 43) e2).1
  rw [eval_kbE, v2, Function.update_self] at v3
  obtain ⟨v4, a4, -⟩ := vw_copy (show 316 < 1000 by norm_num) (show 43 < 1000 by norm_num) e3
  set e4 := (Cmd.run (.copy 316 43) e3).1
  rw [v3, Function.update_self] at v4
  obtain ⟨t1, t2, a5⟩ := UP_ok.tset e4
  set e5 := (Cmd.run UP.tset e4).1
  have K4 : e4.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), Function.update_self]
  rw [K4] at t1
  have w5 : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → vw e5 y = vw e4 y := fun y hy h1 h3 h59 => by
    rw [vw_lt hy, vw_lt hy, t2 y hy h1 h3 h59]
  have n5 : vw e5 0 = n := by
    rw [w5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num)]
    simp [n, Function.update_apply, vw_lt]
  obtain ⟨v6, a6, -⟩ := vw_cset hI.vl0 (show 12 < 1000 by norm_num) e5
  set e6 := (Cmd.run (cset L0X 12) e5).1
  have tk5 : ∀ v k, tokU K v k → vw e5 v = k := fun v k h => by
    have := topOk_lt h; rw [vw_lt (by omega), t1 v k h]
  have s5 : vw e5 11 = sOf n := by
    rw [w5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), Function.update_self]
  rw [hI.l0_eval K n (vw e5) e5.ar tk5 s5 n5] at v6
  obtain ⟨v7, a7, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 12 < 1000 by norm_num) e6
  set e7 := (Cmd.run (.copy 40 12) e6).1
  obtain ⟨v8, a8, -⟩ := vw_setK (k := 1) (show 303 < 1000 by norm_num) e7
  set e8 := (Cmd.run (.setK 303 1) e7).1
  obtain ⟨v10, a10, -⟩ := vw_setK (k := 0) (show 310 < 1000 by norm_num) e8
  set e10 := (Cmd.run (.setK 310 0) e8).1
  have pre : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → y ≠ 12 →
      y ≠ 316 → y ≠ 43 → y ≠ 307 → y ≠ 11 → vw e10 y = vw st y :=
    fun y hy h1 h3 h59 a b c d e f g h i => by
      rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
        Function.update_of_ne d, v6, Function.update_of_ne e, w5 y hy h1 h3 h59, v4, Function.update_of_ne f,
        Function.update_of_ne g, Function.update_of_ne h, Function.update_of_ne i]
  have L6 : vw e6 12 = L := by rw [v6, Function.update_self]; rfl
  have g10 : ∀ y, y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → vw e10 y = vw e6 y := fun y a b c d => by
    rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
      Function.update_of_ne d]
  have k6 : ∀ y, y ∈ [307, 316, 11] → vw e6 y = vw e4 y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [v6, Function.update_of_ne (by omega), w5 y (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨sI, sfr, sar⟩ := sweep_spec e10 (ℓ := ℓ) (L := L)
    (by rw [← vw_lt (show 307 < 1000 by norm_num), g10 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      k6 307 (by simp), v4]; simp [ℓ, n])
    (by rw [← vw_lt (show 40 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_of_ne (by norm_num), v7, Function.update_self, L6])
    (by rw [← vw_lt (show 303 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_self])
    (by rw [← vw_lt (show 310 < 1000 by norm_num), v10, Function.update_self])
  set e11 := (Cmd.run (.loop 307 306 (sweepBody UP)) e10).1
  obtain ⟨lam, l40, l303, l310⟩ := sI 0 (by omega)
  simp only [NPof, mlogN, mul_one, add_zero] at l303 l310
  have hrun : (Cmd.run (setup (UP' L0X SX TX)) st).1 = e11 := by simp only [setup, Cmd.run_seq]; rfl
  have f11 : ∀ y, y ∈ [307, 316, 11, 12] → e11.sc y = vw e6 y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [sfr y (by omega) (by simp only [WS]; omega) (by omega), ← vw_lt (show y < 1000 by omega),
      g10 y (by omega) (by omega) (by omega) (by omega)]
  have tk6 : ∀ v k, tokU K v k → vw e6 v = k := fun v k h => by
    have := topOk_lt h; have := h.1; rw [v6, Function.update_of_ne (by omega), tk5 v k h]
  simp only [r]
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, l303, l310, fun v k h => ?_, fun y hy h1 h3 h59 hW h306 h11 h307 h316 h12 => ?_, ?_⟩
  · rw [f11 11 (by simp), k6 11 (by simp), v4]; simp [n]
  · rw [f11 307 (by simp), k6 307 (by simp), v4]; simp [ℓ, n]
  · rw [f11 316 (by simp), k6 316 (by simp), v4]; simp [K, ℓ, n]
  · rw [f11 12 (by simp), L6]
  · have := topOk_lt h; have := h.1
    rw [sfr v (by omega) (by simp only [WS]; omega) (by omega), ← vw_lt (show v < 1000 by omega),
      g10 v (by omega) (by omega) (by omega) (by omega), tk6 v k h]
  · rw [sfr y hy hW h306, ← vw_lt hy, pre y hy h1 h3 h59 (by simp only [WS] at hW; omega)
      (by simp only [WS] at hW; omega) (by simp only [WS] at hW; omega) (by simp only [WS] at hW; omega) h12 h316
      (by simp only [WS] at hW; omega) h307 h11, vw_lt hy]
  · rw [sar, a10, a8, a7, a6, a5, a4, a3, a2, a1]


end ECDLP.L85A
