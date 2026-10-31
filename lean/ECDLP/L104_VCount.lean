import ECDLP.L104_Shape

/-!
# L104 / VCount: the value of the whole count modulo `m` for a general top (Rudich `countM_spec`, general top)

`countMF_spec'`: for the counting command with top expressions `SX, TX` of a `ShapeDataF` `SD`, the scalar `308` ends at
`(deepMult * cnt : ZMod m).val`, where `cnt` is any natural number with `(SD.D m n k st.ar).inner.value = cnt` in `ZMod m`.
Rudich's `top_search`, `top_tab_rep`, `top_value` are replaced by `SDF_search`, `SDF_tab_rep` (L85_A_Shape) and
`SDF_top_value`; the path and level specs (`pathLoop_spec` with `UP_ok`) are Rudich's, unchanged (`pathBody (UP' ..) = pathBody UP`).
-/
namespace ECDLP.L104B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

/-- the value of the top clique at the search's choice is the value of the network -/
theorem SDF_top_value {F : NetFamily} {T : TopShape} {SX TX : Ex} (SD : ShapeDataF DB P F T SX TX) {m n k ℓ : ℕ}
    (A : ℕ → ℕ → ℕ) (hP : P n A) :
    ((((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ) (Gs_pos K0u ℓ (by norm_num)))).coarsen
      (chiOf (Kb K0u ℓ) (Gs K0u ℓ) (firstGood (okG (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ)
        (Gs_pos K0u ℓ (by norm_num))))) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
        (by have := Kb_ge K0u (by norm_num) ℓ; omega)) (Kb K0u ℓ ^ Gs K0u ℓ) (Kb K0u ℓ ^ Gs K0u ℓ))
        (by have := Kb_ge K0u (by norm_num) ℓ; omega))).toClique (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)).value =
      (SD.D m n k A).inner.value := by
  have hK0 : 0 < Kb K0u ℓ := by have := Kb_ge K0u (by norm_num) ℓ; omega
  obtain ⟨x0, hx0, hok⟩ := SDF_good SD (m := m) (n := n) (k := k) (ℓ := ℓ) A hP
  have hsp := firstGood_spec (okG (((SD.D m n k A).inner.coarsen ((SD.D m n k A).cl (Gs K0u ℓ)
        (Gs_pos K0u ℓ (by norm_num))))) (Kb K0u ℓ) (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) hK0)
      (le_refl (Kb K0u ℓ ^ Gs K0u ℓ)) ⟨x0, hx0, hok⟩
  rw [okG_value _ hK0 hsp.2, Net.value_coarsen]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The whole count modulo `m`, general top.** -/
theorem countMF_spec' {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (SD : ShapeDataF DB P F T SX TX)
    {m n k ℓ cnt : ℕ} (st : St) (hP : P n st.ar) (hm : 1 < m) (h10 : st.sc 10 = m) (h11 : st.sc 11 = sOf n)
    (h0 : st.sc 0 = n) (h2 : st.sc 2 = k) (hkn : k < n) (h307 : st.sc 307 = ℓ) (h316 : st.sc 316 = Kb K0u ℓ)
    (h12 : st.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (h303 : st.sc 303 = NPof K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → st.sc v = k')
    (hcnt : ((SD.D m n k st.ar).inner.value : ZMod m) = (cnt : ZMod m)) :
    (Cmd.run (countM (UP' L0X SX TX)) st).1.sc 308 =
        (((deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) : ℕ) : ZMod m) * (cnt : ZMod m)).val ∧
      (∀ y < 990, ¬ WC y → (Cmd.run (countM (UP' L0X SX TX)) st).1.sc y = st.sc y) ∧
      (∀ a, a ≠ 3 → (Cmd.run (countM (UP' L0X SX TX)) st).1.ar a = st.ar a) := by
  have : NeZero m := ⟨by omega⟩
  set K := Kb K0u ℓ with hKdef
  set L := F.Ltop K (Gs K0u ℓ) n with hLdef
  have hK : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < Gs K0u ℓ := Gs_pos K0u ℓ (by norm_num)
  have hgK : Gs K0u ℓ = 3 * K ^ 8 := rfl
  set Dn := SD.D m n k st.ar with hDn
  set CN := Dn.inner.coarsen (Dn.cl (Gs K0u ℓ) hg) with hCN
  set xf := firstGood (okG CN K L hK0) (K ^ Gs K0u ℓ) (K ^ Gs K0u ℓ) with hxf
  set Tt := (CN.coarsen (chiOf K (Gs K0u ℓ) xf hK0)).toClique L with hTt
  have hc : countM (UP' L0X SX TX) = .seq (cset SX 15) (.seq (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321)
      (.seq (.setK 320 2) (.seq (fillC TX 321 311 316 82 83 320) (.seq (.setK 308 0) (.loop 303 304 (pathBody UP)))))) := rfl
  rw [hc]
  repeat rw [Cmd.run_seq]
  -- c1: 15 := xf
  obtain ⟨v1, a1, -⟩ := vw_cset SD.vS (show 15 < 1000 by norm_num) st
  set c1 := (Cmd.run (cset SX 15) st).1
  have tk : ∀ v k', tokU K v k' → vw st v = k' := fun v k' h => by
    have := topOk_lt h; rw [vw_lt (by omega), htok v k' h]
  have xs : eval (vw st) st.ar SX = xf := by
    rw [(LS.eval_cost (SD.hSX K) tk (σ := vw st) (A := st.ar)).1]
    exact SDF_search SD (A := st.ar) hP hm (by rw [vw_lt (by norm_num), h10])
      (by rw [vw_lt (by norm_num), h11]) (by rw [vw_lt (by norm_num), h0]) (by rw [vw_lt (by norm_num), h2]) hkn.le
      (by rw [vw_lt (by norm_num), h12])
  rw [xs] at v1
  -- c2: 321 := K · 2^(L K); c3: 320 := 2
  obtain ⟨v2, a2, -⟩ := vw_cset (e := .mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) (by simp [VB, pow2])
    (show 321 < 1000 by norm_num) c1
  set c2 := (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).1
  have k1 : vw c1 316 = K := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h316]
  have l1 : vw c1 12 = L := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h12]
  rw [show eval (vw c1) c1.ar (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) = K * 2 ^ (L * K) by
    simp only [Ex.eval, eval_pow2, k1, l1]] at v2
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
  have hval : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      eval (fillEnv c3.sc 311 316 82 83 i) A' TX = (tabK Tt (i % K) (i / K)).val := by
    intro i _ A' hA'
    set σ := fillEnv c3.sc 311 316 82 83 i
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 82 → y ≠ 83 → σ y = c3.sc y := fun y hy h1 h2 h3 => by
      simp only [σ, fillEnv]
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have g : ∀ y < 82, y ≠ 15 → σ y = st.sc y := fun y hy h => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), sc3 y (by omega) (by omega) (by omega) h]
    have tkσ : ∀ v k', topOk K (3 * K ^ 8) v k' → σ v = k' := fun v k' h => by
      have := topOk_lt h; have := h.1; rw [g v (by omega) (by omega), htok v k' h]
    have hA3 : ∀ a, a ≠ 3 → A' a = st.ar a := fun a ha => by rw [hA'.1 a ha, ar3]
    have hR := SDF_tab_rep SD (σ := σ) (A := A') (m := m) (n := n) (k := k) (ℓ := ℓ) (SD.hPc n st.ar A' hA3 hP) hm
      (by rw [g 10 (by norm_num) (by norm_num), h10])
      (by rw [g 11 (by norm_num) (by norm_num), h11]) (by rw [g 0 (by norm_num) (by norm_num), h0])
      (by rw [g 2 (by norm_num) (by norm_num), h2]) hkn.le (by rw [g 12 (by norm_num) (by norm_num), h12])
      (xf := xf) (by rw [hσ 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num), x3])
    rw [SD.hcong m n k st.ar A' hA3] at hR
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have z := hR σ (Ag.refl _ _) ⟨i % K, hγ⟩ (i / K) (by simp [σ, fillEnv, K3]) (by simp [σ, fillEnv, K3])
    rw [(LS.eval_cost (SD.hTX K) tkσ (σ := σ) (A := A')).1]
    change eval σ A' (GroupEx.tab (T.gs (Kb K0u ℓ) (Gs K0u ℓ))) = _
    rw [z.eq_val, tabK, dif_pos hγ]
  obtain ⟨f1, f2⟩ := fill_val TX (vn := 321) (vi := 311) (vK := 316) (vγ := 82) (vΘ := 83) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) SD.vT c3 (by rw [p3]; omega) _ hval
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
  have hP := pathLoop_spec UP UP_ok Tt c5 hm (by rw [sc5 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10])
    (by rw [sc5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h307])
    (by rw [sc5 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h12])
    (by rw [sc5 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h316])
    (by rw [← vw_lt (show 308 < 1000 by norm_num), v5, Function.update_self]) (by rw [a5]; exact hT4)
  obtain ⟨r308, rfr, -, rar⟩ := hP
  refine ⟨?_, fun y hy hW => ?_, fun a ha => ?_⟩
  · rw [r308, sc5 303 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h303, sum_chainVal, deepVal_eq, SDF_top_value SD (ℓ := ℓ) st.ar hP, hcnt]
  · simp only [WC, WP, WL] at hW
    rw [rfr y hy (by simp only [WP, WL]; omega) (by omega), sc5 y hy (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  · rw [rar a ha, a5, ar4]
    simp [filled, Function.update_of_ne ha]

end ECDLP.L104B
