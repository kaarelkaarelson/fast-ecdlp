import ECDLP.L104_VCount

/-!
# L104 / VUni: the output bit of the counting command for a general top (Rudich `uniC_val`, general top)

`modBodyF_spec'` : one modulus adds `[2 <= j and not j | D * cnt]` to the flag count (`D = deepMult`, `cnt` the value of the
network modulo `j`).  `uniCF_val'` : the output bit of `uniC (UP' L0X SX TX)` is `[cnt = 0]`, when the divisor-1 correction
vanishes (`c1 = 0`: `hcx`), the count is `< 2^n`, and the top network of the memory has value `cnt` modulo every `j > 1`.
-/
namespace ECDLP.L104B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One modulus.** -/
theorem modBodyF_spec' {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (SD : ShapeDataF DB P F T SX TX)
    (s : St) (j : ℕ) {n k ℓ cnt : ℕ} (hP : P n s.ar) (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
    (h303 : s.sc 303 = NPof K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k')
    (hD : s.ar 1 k = 0) (hcx : (if 1 / 2 ^ k = numCells (s.ar 1) k (n - k) then 1 else 0) = 0)
    (hcnt : ∀ m, 1 < m → ((SD.D m n k s.ar).inner.value : ZMod m) = (cnt : ZMod m)) :
    (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).1.sc 301 = s.sc 301 +
        (if 2 ≤ j ∧ ¬ j ∣ deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) * cnt then 1 else 0) ∧
      (∀ y < 990, ¬ WM y → (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).1.sc y = s.sc y) ∧
      (∀ a, a ≠ 3 → (Cmd.run (modBody (UP' L0X SX TX)) (s.setSc 300 j)).1.ar a = s.ar a) := by
  set D := deepMult K0u ℓ (F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n)
  set s' := s.setSc 300 j
  set t1 := (Cmd.run (.copy 10 300) s').1
  set t2 := (Cmd.run (.setK 315 2) t1).1
  have g2 : ∀ y, y ≠ 315 → y ≠ 10 → y ≠ 300 → t2.sc y = s.sc y := fun y a b c => by
    simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have j10 : t2.sc 10 = j := by simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy]
  have c315 : t2.sc 315 = 2 := by simp [t2, Cmd.run_setK]
  have hrun : (Cmd.run (modBody (UP' L0X SX TX)) s').1 =
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM (UP' L0X SX TX)) (.seq (dmLoop UP) (cset flagE 301)))) t2).1 := by
    simp only [modBody, Cmd.run_seq]; rfl
  rw [hrun, Cmd.run_ifLt, j10, c315]
  by_cases hj : j < 2
  · rw [if_pos hj, if_neg (by omega), add_zero]
    refine ⟨g2 301 (by norm_num) (by norm_num) (by norm_num), fun y hy hW => ?_, fun a _ => rfl⟩
    simp only [WM] at hW
    exact g2 y (by omega) (by omega) (by omega)
  rw [if_neg hj]
  have hm : 1 < j := by omega
  obtain ⟨c308, cfr, car⟩ := countMF_spec' (L0X := L0X) SD (m := j) (n := n) (k := k) (ℓ := ℓ) (cnt := cnt) t2 (by simpa [t2, t1, s', Cmd.run_setK, Cmd.run_copy] using hP) hm j10
    (by rw [g2 11 (by norm_num) (by norm_num) (by norm_num), h11]) (by rw [g2 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [g2 2 (by norm_num) (by norm_num) (by norm_num), h2]) hkn
    (by rw [g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [g2 316 (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [g2 303 (by norm_num) (by norm_num) (by norm_num), h303])
    (fun v k' h => by have := topOk_lt h; have := h.1; rw [g2 v (by omega) (by omega) (by omega), htok v k' h])
    (hcnt j hm)
  set t3 := (Cmd.run (countM (UP' L0X SX TX)) t2).1
  obtain ⟨dm309, dfr, dar⟩ := dmLoop_spec t3 (ℓ := ℓ) (L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n) (m := j)
    (by omega) (by rw [cfr 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [cfr 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10])
  set t4 := (Cmd.run (dmLoop UP) t3).1
  have ar3 : ∀ a, a ≠ 3 → t4.ar a = s.ar a := fun a ha => by rw [dar, car a ha]; rfl
  have f3 : ∀ y < 990, ¬ WC y → y ≠ 315 → y ≠ 10 → y ≠ 300 → y ≠ 309 → t4.sc y = s.sc y :=
    fun y hy hW a b c e => by
      have hW' := hW
      simp only [WC, WP, WL] at hW'
      rw [dfr y (by omega) (by simp only [WD]; omega) (by omega), cfr y hy hW, g2 y a b c]
  obtain ⟨v4, a4, -⟩ := vw_cset (e := flagE) (by simp [flagE, ifEq, c1E, nsum, xBit, bitRd, VB])
    (show 301 < 1000 by norm_num) t4
  simp only [Cmd.run_seq]
  have m3 : vw t4 10 = j := by
    rw [vw_lt (by norm_num), dfr 10 (by norm_num) (by simp [WD]) (by norm_num),
      cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10]
  have d3 : vw t4 309 % j = D % j := by rw [vw_lt (by norm_num)]; exact dm309
  have e0 : vw t4 0 = n := by
    rw [vw_lt (by norm_num), f3 0 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h0]
  have e2 : vw t4 2 = k := by
    rw [vw_lt (by norm_num), f3 2 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h2]
  have hc1 : eval (vw t4) t4.ar c1E = 0 := by
    rw [eval_c1E (by rw [e2, ar3 1 (by norm_num)]; exact hD) (by rw [e2, e0]; exact hkn), e2, e0,
      ar3 1 (by norm_num)]
    exact hcx
  have r308 : vw t4 308 = ((D : ZMod j) * ((cnt + 0 : ℕ) : ZMod j)).val := by
    rw [vw_lt (by norm_num), dfr 308 (by norm_num) (by simp [WD]) (by norm_num), c308]
    rfl
  have hval : eval (vw t4) t4.ar flagE = vw t4 301 + (if ¬ j ∣ D * cnt then 1 else 0) := by
    rw [flagE, eval_ifEq]
    simp only [Ex.eval, m3, d3, hc1, r308, mul_zero, Nat.zero_mod]
    have key := flag_key (D := D) (c := cnt) (c1 := 0) hm
    simp only [mul_zero, Nat.zero_mod] at key
    by_cases hdv : j ∣ D * cnt
    · rw [if_pos (key.mpr hdv), if_neg (not_not.mpr hdv), add_zero]
    · rw [if_neg (fun h => hdv (key.mp h)), if_pos hdv]
  refine ⟨?_, fun y hy hW => ?_, fun a ha => ?_⟩
  · rw [← vw_lt (show 301 < 1000 by norm_num), v4, Function.update_self, hval, vw_lt (by norm_num),
      f3 301 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    by_cases hdv : j ∣ D * cnt
    · rw [if_neg (not_not.mpr hdv), if_neg (fun h => h.2 hdv)]
    · rw [if_pos hdv, if_pos ⟨by omega, hdv⟩]
  · have hW' : ¬ (WC y ∨ y = 10 ∨ y = 300 ∨ y = 301 ∨ y = 315 ∨ y = 309) := hW
    have y10 : y ≠ 10 := fun h => hW' (Or.inr (Or.inl h))
    have y300 : y ≠ 300 := fun h => hW' (Or.inr (Or.inr (Or.inl h)))
    have y301 : y ≠ 301 := fun h => hW' (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have y315 : y ≠ 315 := fun h => hW' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have y309 : y ≠ 309 := fun h => hW' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    rw [← vw_lt (show y < 1000 by omega), v4, Function.update_of_ne y301, vw_lt (by omega),
      f3 y hy (fun h => hW' (Or.inl h)) y315 y10 y300 y309]
  · rw [a4, ar3 a ha]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The output bit of the counting command, general top.** -/
theorem uniCF_val' {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX)
    (SD : ShapeDataF DB P F T SX TX) (st : St) {cnt : ℕ} (hP : P (st.sc 0) st.ar) (hkn : st.sc 2 < st.sc 0)
    (hD : st.ar 1 (st.sc 2) = 0)
    (hcx : (if 1 / 2 ^ st.sc 2 = numCells (st.ar 1) (st.sc 2) (st.sc 0 - st.sc 2) then 1 else 0) = 0)
    (hlt : cnt < 2 ^ st.sc 0)
    (hcnt : ∀ m, 1 < m → ((SD.D m (st.sc 0) (st.sc 2) st.ar).inner.value : ZMod m) = (cnt : ZMod m)) :
    (Cmd.run (uniC (UP' L0X SX TX)) st).1.sc 3 = if 0 < cnt then 0 else 1 := by
  set n := st.sc 0
  set k := st.sc 2
  set ℓ := ellOf n
  set L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n
  set D := deepMult K0u ℓ L
  obtain ⟨s11, s307, s316, s12, s303, s310, stok, sfr, sar⟩ := setupF_spec' hI st
  set b1 := (Cmd.run (setup (UP' L0X SX TX)) st).1
  obtain ⟨v2, a2, -⟩ := vw_cset (e := mE) (by simp [mE, VB]) (show 314 < 1000 by norm_num) b1
  set b2 := (Cmd.run (cset mE 314) b1).1
  set b3 := (Cmd.run (.setK 301 0) b2).1
  have g3 : ∀ y < 1000, y ≠ 301 → y ≠ 314 → b3.sc y = b1.sc y := fun y hy h1 h2 => by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne h1]
    rw [← vw_lt hy, v2, Function.update_of_ne h2, vw_lt hy]
  have ar3 : b3.ar = st.ar := by simp only [b3, Cmd.run_setK, St.setSc_ar]; rw [a2, sar]
  have b0 : b1.sc 0 = n := sfr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2' : b1.sc 2 = k := sfr 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have M314 : b3.sc 314 = 2 * (n + mlogN K0u ℓ L + 4) + 1 := by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne (show (314 : ℕ) ≠ 301 by norm_num)]
    rw [← vw_lt (show 314 < 1000 by norm_num), v2, Function.update_self]
    simp only [mE, Ex.eval, vw_lt (show 0 < 1000 by norm_num), vw_lt (show 310 < 1000 by norm_num), b0, s310]
    rfl
  -- the moduli loop
  let MI : ℕ → St → Prop := fun j s => s.sc 301 = flagCount D cnt j ∧
    (∀ y < 990, ¬ WM y → s.sc y = b3.sc y) ∧ (∀ a, a ≠ 3 → s.ar a = b3.ar a)
  have hloop := Cmd.loop_inv (b := 314) (c := 300) (body := modBody (UP' L0X SX TX)) (st := b3) MI
    ⟨by simp [b3, Cmd.run_setK, flagCount], fun _ _ _ => rfl, fun _ _ => rfl⟩ (by
      intro j s _ ⟨f301, ffr, far⟩
      have q : ∀ y, y ∈ [11, 0, 2, 307, 316, 12, 303] → s.sc y = b1.sc y := fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rw [ffr y (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 y (by omega) (by omega) (by omega)]
      have sa : ∀ a, a ≠ 3 → s.ar a = st.ar a := fun a ha => by rw [far a ha, ar3]
      have sA : s.ar 1 = st.ar 1 := sa 1 (by norm_num)
      have hsD : s.ar 1 k = 0 := by rw [sA]; exact hD
      have hsx : (if 1 / 2 ^ k = numCells (s.ar 1) k (n - k) then 1 else 0) = 0 := by rw [sA]; exact hcx
      obtain ⟨r301, rfr, rar⟩ := modBodyF_spec' SD s j (n := n) (k := k) (ℓ := ℓ) (cnt := cnt) (SD.hPc n st.ar s.ar sa hP) (by rw [q 11 (by simp), s11])
        (by rw [q 0 (by simp), b0]) (by rw [q 2 (by simp), b2']) hkn (by rw [q 307 (by simp), s307])
        (by rw [q 316 (by simp), s316]) (by rw [q 12 (by simp), s12]) (by rw [q 303 (by simp), s303])
        (fun v k' h => by
          have := topOk_lt h; have := h.1
          rw [ffr v (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 v (by omega) (by omega) (by omega),
            stok v k' h])
        hsD hsx
        (fun m hm => by
          rw [SD.hcong m n k st.ar s.ar sa]
          exact hcnt m hm)
      refine ⟨by rw [r301, f301]; simp only [flagCount]; rw [Finset.sum_range_succ], fun y hy hW => by rw [rfr y hy hW, ffr y hy hW],
        fun a ha => by rw [rar a ha, far a ha]⟩)
  rw [M314] at hloop
  obtain ⟨l301, -, -⟩ := hloop
  set b4 := (Cmd.run (.loop 314 300 (modBody (UP' L0X SX TX))) b3).1
  obtain ⟨v5, -, -⟩ := vw_cset (e := Uni.bitE) (by simp [Uni.bitE, VB]) (show 3 < 1000 by norm_num) b4
  have hrun : (Cmd.run (uniC (UP' L0X SX TX)) st).1 = (Cmd.run (cset Uni.bitE 3) b4).1 := by
    simp only [uniC, Cmd.run_seq]; rfl
  rw [hrun, ← vw_lt (show 3 < 1000 by norm_num), v5, Function.update_self, Uni.bitE, eval_ifLt']
  simp only [Ex.eval, vw_lt (show 301 < 1000 by norm_num), l301]
  exact bit_of_flags (deepMult_pos K0u ℓ L) (deepMult_le K0u ℓ L) hlt

end ECDLP.L104B
