import ECDLP.L69_Keep

/-!
# L69 / Count: the cost of the whole count modulo `m` for a general top (Rudich `UCost.countM_cost`)
-/
namespace ECDLP.L69
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost Finset SB ECDLP.L60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of the whole count modulo `m`.** -/
theorem countM_cost' {F : NetFamily} {L0X SX TX : Ex} (hI : TopIface F L0X SX TX) (hS : F.Spec) {V m n k ℓ : ℕ} (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h11 : st.sc 11 = sOf n)
    (h0 : st.sc 0 = n) (h2 : st.sc 2 = k) (hkn : k < n) (h307 : st.sc 307 = ℓ) (h316 : st.sc 316 = Kb K0u ℓ)
    (h12 : st.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (h303 : st.sc 303 ≤ V)
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → st.sc v = k') (R : F.FamOK V m K0u ℓ n) (hℓ : ℓ ≤ V)
    (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (countM (UP' L0X SX TX)) st).2 ≤ 60 * YB V ^ 3 := by
  have : NeZero m := ⟨by omega⟩
  have hW := @le_Wv V
  have hVV := @sq_le_Wv V
  have RW := hS.ok_mono R hW
  have hY := YB_ge V
  have hPB := PB_le_YB V
  have hY3 : YB V ≤ YB V ^ 3 := Nat.le_self_pow (by norm_num) _
  set K := Kb K0u ℓ
  set L := F.Ltop K (3 * K ^ 8) n
  have hK : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < 3 * K ^ 8 := Nat.mul_pos (by norm_num) (Nat.pow_pos hK0)
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ (show 0 < Gs K0u ℓ from hg)) (hI.ok_KG R)
  have hLK : 2 ^ (L * K) ≤ V := hI.ok_LK R
  have hLKV : L * K ≤ V := le_trans Nat.lt_two_pow_self.le hLK
  -- c1: 15 := xf
  obtain ⟨v1, a1, k1⟩ := vw_cset hI.vts (show 15 < 1000 by norm_num) st
  set c1 := (Cmd.run (cset SX 15) st).1
  have tk : ∀ v k', tokU K v k' → vw st v = k' := fun v k' h => by
    have := topOk_lt h; rw [vw_lt (by omega), htok v k' h]
  have q10 : vw st 10 = m := by rw [vw_lt (by norm_num), h10]
  have q11 : vw st 11 = sOf n := by rw [vw_lt (by norm_num), h11]
  have q0 : vw st 0 = n := by rw [vw_lt (by norm_num), h0]
  have q2 : vw st 2 = k := by rw [vw_lt (by norm_num), h2]
  have q12 : vw st 12 = L := by rw [vw_lt (by norm_num), h12]; rfl
  have k1' : (Cmd.run (cset SX 15) st).2 ≤ PB V :=
    le_trans k1 (hI.s_cost V m ℓ n k (vw st) st.ar RW hkn.le tk q10 q11 q0 q2 q12)
  obtain ⟨Tt, hTt⟩ := hI.tab_spec V m ℓ n k (vw st) st.ar RW hm hkn.le tk q10 q11 q0 q2 q12
  set xf := eval (vw st) st.ar SX with hxf
  rw [hxf] at v1
  -- c2: 321 := K · 2^(L K); c3: 320 := 2
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := .mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) (by simp [VB, pow2])
    (show 321 < 1000 by norm_num) c1
  set c2 := (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).1
  have k1K : vw c1 316 = K := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h316]
  have l1 : vw c1 12 = L := by rw [v1, Function.update_of_ne (by norm_num), q12]
  have hn : K * 2 ^ (L * K) ≤ Wv V := le_trans (Nat.mul_le_mul hKV hLK) hVV
  have k2' : (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).2 ≤ PB V := by
    refine le_trans k2 (cost_le_PB ?_ (by simp [Ex.dp, pow2]))
    have Bm : Bdd (Wv V) (vw c1) c1.ar (.mul (.var 12) (.var 316)) :=
      B_mul (B_var (by rw [l1]; exact le_trans (le_trans (Nat.le_mul_of_pos_right _ hK0) hLKV) hW))
        (B_var (by rw [k1K]; omega)) (by simp only [Ex.eval, l1, k1K]; omega)
    refine B_mul (B_var (by rw [k1K]; omega)) (B_pow2 Bm (by omega) (by simp only [Ex.eval, l1, k1K]; omega)) ?_
    simp only [Ex.eval, eval_pow2, l1, k1K]; exact hn
  rw [show eval (vw c1) c1.ar (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) = K * 2 ^ (L * K) by
    simp only [Ex.eval, eval_pow2, k1K, l1]] at v2
  obtain ⟨v3, a3, -⟩ := vw_setK (k := 2) (show 320 < 1000 by norm_num) c2
  set c3 := (Cmd.run (.setK 320 2) c2).1
  have w3 : ∀ y, y ≠ 320 → y ≠ 321 → y ≠ 15 → vw c3 y = vw st y := fun y h1 h2 h3 => by
    rw [v3, Function.update_of_ne h1, v2, Function.update_of_ne h2, v1, Function.update_of_ne h3]
  have ar3 : c3.ar = st.ar := by rw [a3, a2, a1]
  have sc3 : ∀ y < 1000, y ≠ 320 → y ≠ 321 → y ≠ 15 → c3.sc y = st.sc y := fun y hy h1 h2 h3 => by
    rw [← vw_lt hy, w3 y h1 h2 h3, vw_lt hy]
  have p3 : c3.sc 320 = 2 := by rw [← vw_lt (show 320 < 1000 by norm_num), v3, Function.update_self]
  have n3 : c3.sc 321 = K * 2 ^ (L * K) := by
    rw [← vw_lt (show 321 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), v2, Function.update_self]
  have x3 : c3.sc 15 = xf := by
    rw [← vw_lt (show 15 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), v2,
      Function.update_of_ne (by norm_num), v1, Function.update_self]
  have K3 : c3.sc 316 = K := by rw [sc3 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h316]
  -- c4: the top table
  have henv : ∀ i (A' : ℕ → ℕ → ℕ), AgP c3.ar A' (c3.sc 320) →
      (∀ y < 82, y ≠ 15 → fillEnv c3.sc 311 316 82 83 i y = st.sc y) ∧
        (∀ v k', tokU K v k' → fillEnv c3.sc 311 316 82 83 i v = k') ∧ (∀ a, a ≠ 3 → A' a = st.ar a) ∧
        fillEnv c3.sc 311 316 82 83 i 15 = xf := by
    intro i A' hA'
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 82 → y ≠ 83 → fillEnv c3.sc 311 316 82 83 i y = c3.sc y :=
      fun y hy h1 h2 h3 => by
        simp only [fillEnv]
        rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have g : ∀ y < 82, y ≠ 15 → fillEnv c3.sc 311 316 82 83 i y = st.sc y := fun y hy h => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), sc3 y (by omega) (by omega) (by omega) h]
    exact ⟨g, fun v k' h => by have := topOk_lt h; have := h.1; rw [g v (by omega) (by omega), htok v k' h],
      fun a ha => by rw [hA'.1 a ha, ar3],
      by rw [hσ 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num), x3]⟩
  have hval : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      eval (fillEnv c3.sc 311 316 82 83 i) A' TX = (tabK Tt (i % K) (i / K)).val := by
    intro i hi A' hA'
    obtain ⟨g, tkσ, e0, x15⟩ := henv i A' hA'
    rw [n3] at hi
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have hQ : i / K < 2 ^ (L * K) := Nat.div_lt_of_lt_mul hi
    have h82 : fillEnv c3.sc 311 316 82 83 i 82 = i % K := by simp [fillEnv, K3]
    have h83 : fillEnv c3.sc 311 316 82 83 i 83 = i / K := by simp [fillEnv, K3]
    have := (hTt (fillEnv c3.sc 311 316 82 83 i) A' (fun y hy h => by rw [g y hy h, vw_lt (by omega)]) x15 e0
      (by rw [h82]; exact hγ) (by rw [h83]; exact hQ)).1
    rw [h82, h83] at this
    exact this
  have hcost : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      cost (fillEnv c3.sc 311 316 82 83 i) A' TX ≤ PB V := by
    intro i hi A' hA'
    obtain ⟨g, tkσ, e0, x15⟩ := henv i A' hA'
    rw [n3] at hi
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have hQ : i / K < 2 ^ (L * K) := Nat.div_lt_of_lt_mul hi
    have h82 : fillEnv c3.sc 311 316 82 83 i 82 = i % K := by simp [fillEnv, K3]
    have h83 : fillEnv c3.sc 311 316 82 83 i 83 = i / K := by simp [fillEnv, K3]
    exact (hTt (fillEnv c3.sc 311 316 82 83 i) A' (fun y hy h => by rw [g y hy h, vw_lt (by omega)]) x15 e0
      (by rw [h82]; exact hγ) (by rw [h83]; exact hQ)).2
  have k4 := fill_spec TX (vn := 321) (vi := 311) (vK := 316) (vγ := 82) (vΘ := 83) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hI.vtt c3 (by rw [p3]; omega) _ (PB V) hval hcost
  rw [n3] at k4
  have k4' : (Cmd.run (fillC TX 321 311 316 82 83 320) c3).2 ≤ 3 * YB V := le_trans k4 (fill_le hn le_rfl)
  obtain ⟨f1, f2⟩ := fill_val TX (vn := 321) (vi := 311) (vK := 316) (vγ := 82) (vΘ := 83) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hI.vtt c3 (by rw [p3]; omega) _ hval
  set c4 := (Cmd.run (fillC TX 321 311 316 82 83 320) c3).1
  have ar4 : c4.ar = filled st.ar (fun i => (tabK Tt (i % K) (i / K)).val) 2 (K * 2 ^ (L * K)) := by
    rw [f1, ar3, p3, n3]
  have hT4 : Holds c4.ar 2 Tt := by rw [ar4]; exact holds_filled Tt _ (by norm_num) (by omega)
  obtain ⟨v5, a5, -⟩ := vw_setK (k := 0) (show 308 < 1000 by norm_num) c4
  set c5 := (Cmd.run (.setK 308 0) c4).1
  have sc5 : ∀ y < 990, y ≠ 308 → y ≠ 311 → y ≠ 320 → y ≠ 321 → y ≠ 15 → c5.sc y = st.sc y :=
    fun y hy h0 h1 h2 h3 h4 => by
      rw [← vw_lt (show y < 1000 by omega), v5, Function.update_of_ne h0, vw_lt (by omega), f2 y hy h1,
        sc3 y (by omega) h2 h3 h4]
  have k6 := pathLoop_cost Tt c5 hm (by rw [sc5 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10])
    (by rw [sc5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [sc5 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [sc5 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [← vw_lt (show 308 < 1000 by norm_num), v5, Function.update_self])
    (by rw [sc5 303 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h303)
    (by rw [a5]; exact hT4) (hI.ok_deep R) hLK hℓ hlv
  have hle := seq_le k1' (seq_le k2' (seq_le (le_refl (Cmd.run (.setK 320 2) c2).2) (seq_le k4'
    (seq_le (le_refl (Cmd.run (.setK 308 0) c4).2) k6))))
  have e : (Cmd.run (countM (UP' L0X SX TX)) st).2 = (Cmd.run (.seq (cset SX 15) <|
      .seq (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) <|
      .seq (.setK 320 2) <| .seq (fillC TX 321 311 316 82 83 320) <| .seq (.setK 308 0)
      (.loop 303 304 (pathBody UP))) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_setK]
  omega


end ECDLP.L69
