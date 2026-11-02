import ECDLPv2.L115_ModR
import ECDLP.L104_Uni
import ECDLP.L104_Setup
import ECDLP.L104_Keep
import ECDLP.L71_Shift

/-!
# L115 / Sweep: the residue sweep
`swpC S RN RD U` : in the unshifted frame, `setup` and `mE` run once in the frame shifted by `S`, then a loop over `j < M` (`M = 2(n+ML+4)+1`, register 852, counter 851)
runs `(modBodyR U).shift S` and stores `RN[j] = D*cnt mod j`, `RD[j] = D mod j` (arrays `RN, RD < S`, so the engine, which never touches indices `< S`, is undisturbed).
`swp_run` : value (residues for `2 ≤ m < M`), frames below `S`, and the cost `≤ 200 YB^4`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L115
variable {DB : ℕ} [Fact (100 ≤ DB)] {P : ℕ → (ℕ → ℕ → ℕ) → Prop}
open ECDLP.L85A ECDLP.L104A ECDLP.L104B ECDLP.L109 ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni UCost85 Finset SB ECDLP.L60 ECDLP.L58 ECDLP.L85A

attribute [local irreducible] cset

theorem unshift_setSc_low (S : ℕ) (st : St) (x v : ℕ) (hx : x < S) : unshift S (st.setSc x v) = unshift S st := by
  apply St.ext
  · funext i; simp only [unshift_sc, St.setSc_sc]; rw [Function.update_of_ne (by omega)]
  · rfl

theorem unshift_setAr_low (S : ℕ) (st : St) (a i v : ℕ) (ha : a < S) : unshift S (st.setAr a i v) = unshift S st := by
  apply St.ext
  · rfl
  · funext b; simp only [unshift_ar, St.setAr, St.putAr]; rw [Function.update_of_ne (by omega)]

def swpBody (S RN RD : ℕ) (U : UParts) : Cmd :=
  .seq (.copy (S + 300) 851) (.seq ((modBodyR U).shift S) (.seq (.wr RN 851 0 (S + 308)) (.wr RD 851 0 (S + 309))))

def swpC (S RN RD : ℕ) (U : UParts) : Cmd :=
  .seq ((setup U).shift S) (.seq ((cset mE 314).shift S) (.seq (.copy 852 (S + 314)) (.loop 852 851 (swpBody S RN RD U))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem swp_run {F : NetFamily} {T : TopShape} {L0X SX TX : Ex} (hI : TopIfaceF DB P F L0X SX TX) (hS : F.Spec)
    (SD : ShapeDataF DB P F T SX TX) (S RN RD : ℕ) (hS1 : 1400 ≤ S) (hRN : RN < S) (hRD : RD < S) (hne : RN ≠ RD)
    (V : ℕ) (Sf : St) {cnt : ℕ}
    (hP : P ((unshift S Sf).sc 0) (unshift S Sf).ar) (hkn : (unshift S Sf).sc 2 < (unshift S Sf).sc 0)
    (R : F.UniReq V ((unshift S Sf).sc 0))
    (hcnt : ∀ m, 1 < m → ((SD.D m ((unshift S Sf).sc 0) ((unshift S Sf).sc 2) (unshift S Sf).ar).inner.value : ZMod m) = (cnt : ZMod m)) :
    let n := (unshift S Sf).sc 0
    let ℓ := ellOf n
    let L := F.Ltop (Kb K0u ℓ) (Gs K0u ℓ) n
    let r := (Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf).1
    r.sc 852 = 2 * (n + mlogN K0u ℓ L + 4) + 1 ∧
    (∀ m, 2 ≤ m → m < 2 * (n + mlogN K0u ℓ L + 4) + 1 →
      r.ar RN m = (deepMult K0u ℓ L * cnt) % m ∧ r.ar RD m = deepMult K0u ℓ L % m) ∧
    (∀ y, y < S → y ≠ 851 → y ≠ 852 → r.sc y = Sf.sc y) ∧
    (∀ a, a < S → a ≠ RN → a ≠ RD → r.ar a = Sf.ar a) ∧
    (Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf).2 ≤ 200 * YB DB V ^ 4 := by
  intro n ℓ L r
  have htop := R.main.top
  have hM : 2 * F.Mof K0u ℓ n + 1 ≤ V := R.main.hM
  have hnp : NPof K0u ℓ L ≤ V := R.np
  have hlv : lvlV (Kb K0u ℓ) ≤ V := R.lv
  have hsm : n + ℓ + 64 ≤ V := R.small
  have hkb : Kb K0u (ℓ + 1) ^ 40 ≤ V := R.kb
  set st := unshift S Sf with hst
  set D := deepMult K0u ℓ L
  have hW := @le_Wv V
  have hY := YB_ge DB V
  have hPB := PB_le_YB DB V
  have hY2 : YB DB V ^ 2 ≤ YB DB V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY1 : YB DB V ≤ YB DB V ^ 4 := Nat.le_self_pow (by norm_num) _
  have hY3 : YB DB V ≤ YB DB V ^ 3 := Nat.le_self_pow (by norm_num) _
  have hMof : F.Mof K0u ℓ n = n + mlogN K0u ℓ L + 4 := rfl
  have hml : mlogN K0u ℓ L ≤ V := by omega
  have R2 := htop 2 le_rfl (by show 2 ≤ 2 * F.Mof K0u ℓ n + 1; omega)
  -- step 1: setup
  obtain ⟨u1, c1, lo1⟩ := run_shift S (setup (UP' L0X SX TX)) Sf
  set Sf1 := (Cmd.run ((setup (UP' L0X SX TX)).shift S) Sf).1 with hSf1
  have k1 := setupF_cost' hI hS st R2 hml hnp hlv hsm hkb
  obtain ⟨s11, s307, s316, s12, s303, s310, stok, sfr, sar⟩ := setupF_spec' hI st
  set b1 := (Cmd.run (setup (UP' L0X SX TX)) st).1 with hb1
  -- step 2: mE
  obtain ⟨u2, c2, lo2⟩ := run_shift S (cset mE 314) Sf1
  set Sf2 := (Cmd.run ((cset mE 314).shift S) Sf1).1 with hSf2
  rw [u1] at u2 c2
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := mE) (by simp [mE, VB]) (show 314 < 1000 by norm_num) b1
  set b2 := (Cmd.run (cset mE 314) b1).1 with hb2
  have b0 : b1.sc 0 = n := sfr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2' : b1.sc 2 = st.sc 2 := sfr 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have k2' : (Cmd.run (cset mE 314) b1).2 ≤ PB DB V := by
    refine le_trans k2 (cost_le_PB ?_ (by simp [mE, Ex.dp]))
    have e0 : vw b1 0 = n := by rw [vw_lt (by norm_num), b0]
    have e310 : vw b1 310 = mlogN K0u ℓ L := by rw [vw_lt (by norm_num), s310]
    unfold mE
    refine B_add (B_mul (B_lit (by omega)) (B_add (B_add (B_var (by rw [e0]; omega)) (B_var (by rw [e310]; omega))
      (by simp only [Ex.eval, e0, e310]; omega)) (B_lit (by omega)) (by simp only [Ex.eval, e0, e310]; omega))
      (by simp only [Ex.eval, e0, e310]; omega)) (B_lit (by omega)) (by simp only [Ex.eval, e0, e310]; omega)
  have g2 : ∀ y < 1000, y ≠ 314 → b2.sc y = b1.sc y := fun y hy h2 => by
    rw [← vw_lt hy, v2, Function.update_of_ne h2, vw_lt hy]
  have M314 : b2.sc 314 = 2 * (n + mlogN K0u ℓ L + 4) + 1 := by
    rw [← vw_lt (show 314 < 1000 by norm_num), v2, Function.update_self]
    simp only [mE, Ex.eval, vw_lt (show 0 < 1000 by norm_num), vw_lt (show 310 < 1000 by norm_num), b0, s310]
    rfl
  have ar2 : b2.ar = st.ar := by rw [a2, sar]
  -- step 3: copy
  set Sf3 := Sf2.setSc 852 (Sf2.sc (S + 314)) with hSf3
  have hS2 : Sf2.sc (S + 314) = 2 * (n + mlogN K0u ℓ L + 4) + 1 := by
    have : (unshift S Sf2).sc 314 = Sf2.sc (S + 314) := rfl
    rw [← this, u2]; exact M314
  have hMs : Sf3.sc 852 = 2 * (n + mlogN K0u ℓ L + 4) + 1 := by
    rw [hSf3]; simp only [St.setSc_sc, Function.update_self]; exact hS2
  have hu3 : unshift S Sf3 = b2 := by rw [hSf3, unshift_setSc_low S _ _ _ (by omega), u2]
  -- low part of Sf3 agrees with Sf
  have lo3a : ∀ a, a < S → Sf3.ar a = Sf.ar a := fun a ha => by
    have := (lo1.trans lo2).2 a ha
    rw [hSf3]; exact this.symm
  have lo3' : ∀ y, y < S → y ≠ 852 → Sf3.sc y = Sf.sc y := fun y hy h => by
    have := (lo1.trans lo2).1 y hy
    rw [hSf3]; simp only [St.setSc_sc]; rw [Function.update_of_ne h]; exact this.symm
  -- the loop
  let MI : ℕ → St → Prop := fun j s =>
    (∀ y < 990, ¬ WM y → (unshift S s).sc y = b2.sc y) ∧ (∀ a, a ≠ 3 → (unshift S s).ar a = st.ar a) ∧
    (∀ y, y < S → y ≠ 851 → s.sc y = Sf3.sc y) ∧ (∀ a, a < S → a ≠ RN → a ≠ RD → s.ar a = Sf3.ar a) ∧
    (∀ m, 2 ≤ m → m < j → s.ar RN m = (D * cnt) % m ∧ s.ar RD m = D % m)
  have hstep : ∀ j s, j < Sf3.sc 852 → MI j s → MI (j + 1) (Cmd.run (swpBody S RN RD (UP' L0X SX TX)) (s.setSc 851 j)).1 ∧
      (Cmd.run (swpBody S RN RD (UP' L0X SX TX)) (s.setSc 851 j)).2 ≤ 104 * YB DB V ^ 3 := by
    intro j s hj ⟨f1, f2, f3, f4, f5⟩
    rw [hMs] at hj
    set T0 := s.setSc 851 j with hT0
    have e0 : unshift S T0 = unshift S s := unshift_setSc_low S s 851 j (by omega)
    have s851 : T0.sc 851 = j := by simp [hT0]
    set T1 := T0.setSc (S + 300) j with hT1
    have e1 : unshift S T1 = (unshift S s).setSc 300 j := by rw [hT1, unshift_setSc, e0]
    obtain ⟨w1, w2, w3⟩ := run_shift S (modBodyR (UP' L0X SX TX)) T1
    rw [e1] at w1 w2
    generalize hT2 : Cmd.run ((modBodyR (UP' L0X SX TX)).shift S) T1 = T2 at w1 w2 w3
    have t851 : T2.1.sc 851 = j := by
      rw [← w3.1 851 (by omega)]
      simp only [hT1, hT0, St.setSc_sc]
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hrun : Cmd.run (swpBody S RN RD (UP' L0X SX TX)) T0 =
        (((T2.1.setAr RN (T2.1.sc 851 + 0) (T2.1.sc (S + 308))).setAr RD (T2.1.sc 851 + 0) (T2.1.sc (S + 309))),
         1 + (T2.2 + (1 + 1 + 1) + 1) + 1) := by
      simp only [swpBody, Cmd.run_seq, Cmd.run_copy, Cmd.run_wr, s851, ← hT1, hT2, St.setAr_sc]
    have u4 : unshift S ((T2.1.setAr RN (T2.1.sc 851 + 0) (T2.1.sc (S + 308))).setAr RD (T2.1.sc 851 + 0) (T2.1.sc (S + 309))) =
        unshift S T2.1 := by rw [unshift_setAr_low S _ _ _ _ hRD, unshift_setAr_low S _ _ _ _ hRN]
    -- facts on the engine view
    have q : ∀ y, y ∈ [11, 0, 2, 307, 316, 12, 303] → (unshift S s).sc y = b1.sc y := fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [f1 y (by omega) (by simp only [WM, WC, WP, WL]; omega), g2 y (by omega) (by omega)]
    have sa : ∀ a, a ≠ 3 → (unshift S s).ar a = st.ar a := f2
    have hPs : P n (unshift S s).ar := hI.hPc n st.ar _ f2 hP
    obtain ⟨hfr, har, hres, kc⟩ : (∀ y < 990, ¬ WM y → (unshift S T2.1).sc y = (unshift S s).sc y) ∧
        (∀ a, a ≠ 3 → (unshift S T2.1).ar a = (unshift S s).ar a) ∧
        (2 ≤ j → (unshift S T2.1).sc 308 = (D * cnt) % j ∧ (unshift S T2.1).sc 309 = D % j) ∧
        T2.2 ≤ 100 * YB DB V ^ 3 := by
      have kc := modBodyR_cost' hI hS (V := V) (n := n) (k := st.sc 2) (ℓ := ℓ) (unshift S s) hPs j (by rw [q 11 (by simp), s11])
        (by rw [q 0 (by simp), b0]) (by rw [q 2 (by simp), b2']) hkn (by rw [q 307 (by simp), s307]) (by rw [q 316 (by simp), s316])
        (by rw [q 12 (by simp), s12]) (by rw [q 303 (by simp), s303]; exact hnp)
        (fun v k' h => by
          have := topOk_lt h; have := h.1
          rw [f1 v (by omega) (by simp only [WM, WC, WP, WL]; omega), g2 v (by omega) (by omega), stok v k' h])
        (fun h2 => htop j h2 (by show j ≤ 2 * F.Mof K0u ℓ n + 1; omega)) (by omega) (by omega) (by omega) hlv
      rw [w2] at *
      rw [w1]
      refine ?_
      by_cases hj2 : j < 2
      · obtain ⟨m1, m2⟩ := modBodyR_small (UP' L0X SX TX) (unshift S s) j hj2
        exact ⟨m1, fun a _ => m2 a, fun h => absurd h (by omega), kc⟩
      · obtain ⟨r308, r309, m1, m2⟩ := modBodyR_spec2 SD (unshift S s) j (n := n) (k := st.sc 2) (ℓ := ℓ) (cnt := cnt) hPs
          (by rw [q 11 (by simp), s11]) (by rw [q 0 (by simp), b0]) (by rw [q 2 (by simp), b2']) hkn
          (by rw [q 307 (by simp), s307]) (by rw [q 316 (by simp), s316]) (by rw [q 12 (by simp), s12])
          (by rw [q 303 (by simp), s303])
          (fun v k' h => by
            have := topOk_lt h; have := h.1
            rw [f1 v (by omega) (by simp only [WM, WC, WP, WL]; omega), g2 v (by omega) (by omega), stok v k' h])
          (by omega)
          (by rw [SD.hcong j n (st.sc 2) st.ar (unshift S s).ar sa]; exact hcnt j (by omega))
        refine ⟨m1, m2, fun _ => ⟨?_, r309⟩, kc⟩
        rw [r308, ← Nat.cast_mul, ZMod.val_natCast]
    have hT2sc : ∀ y, y < S → y ≠ 851 → T2.1.sc y = s.sc y := fun y hy h851 => by
      rw [← w3.1 y hy]
      simp only [hT1, hT0, St.setSc_sc]
      rw [Function.update_of_ne (by omega), Function.update_of_ne h851]
    have hT2ar : ∀ a, a < S → T2.1.ar a = s.ar a := fun a ha => by
      rw [← w3.2 a ha]; rfl
    rw [hrun]
    refine ⟨⟨fun y hy hW => ?_, fun a ha => ?_, fun y hy h851' => ?_, fun a ha h1 h2 => ?_, fun m hm2 hmj => ?_⟩, by omega⟩
    · rw [u4, hfr y hy hW]; exact f1 y hy hW
    · rw [u4, har a ha]; exact f2 a ha
    · simp only [St.setAr_sc]; rw [hT2sc y hy h851']; exact f3 y hy h851'
    · simp only [St.setAr_ar, St.putAr_ar, St.setAr]
      rw [Function.update_of_ne h2, Function.update_of_ne h1, hT2ar a ha]; exact f4 a ha h1 h2
    · simp only [St.setAr_ar, St.putAr_ar, St.setAr, St.setAr_sc]
      by_cases hmj' : m = j
      · subst hmj'
        obtain ⟨h308, h309⟩ := hres hm2
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne hne, t851, Function.update_self]
          simpa using h308
        · rw [t851]; simp only [add_zero, Function.update_self]; simpa using h309
      · have hlt : m < j := by omega
        obtain ⟨g1, g2'⟩ := f5 m hm2 hlt
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne hne, t851, Function.update_self, add_zero, Function.update_of_ne hmj', hT2ar RN hRN]; exact g1
        · rw [t851, Function.update_self, add_zero, Function.update_of_ne hmj', Function.update_of_ne hne.symm, hT2ar RD hRD]; exact g2'
  -- initial state
  have h0 : MI 0 Sf3 := ⟨fun y hy hW => by rw [hu3], fun a ha => by rw [hu3, ar2], fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun m h1 h2 => absurd h2 (by omega)⟩
  have hL1 := Cmd.loop_inv (b := 852) (c := 851) (body := swpBody S RN RD (UP' L0X SX TX)) (st := Sf3) MI h0
    (fun j s hj hs => (hstep j s hj hs).1)
  have hL2 := Cmd.loop_cost_le (b := 852) (c := 851) (body := swpBody S RN RD (UP' L0X SX TX)) (st := Sf3) MI (104 * YB DB V ^ 3) h0
    (fun j s hj hs => (hstep j s hj hs).1) (fun j s hj hs => (hstep j s hj hs).2)
  rw [hMs] at hL1 hL2
  have hrun : Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf =
      ((Cmd.run (.loop 852 851 (swpBody S RN RD (UP' L0X SX TX))) Sf3).1,
       (Cmd.run ((setup (UP' L0X SX TX)).shift S) Sf).2 + ((Cmd.run ((cset mE 314).shift S) Sf1).2 + (1 + (Cmd.run (.loop 852 851 (swpBody S RN RD (UP' L0X SX TX))) Sf3).2 + 1) + 1) + 1) := by
    simp only [swpC, Cmd.run_seq, Cmd.run_copy]
    rfl
  have hMV : 2 * (n + mlogN K0u ℓ L + 4) + 1 ≤ V := by
    have : F.Mof K0u ℓ n = n + mlogN K0u ℓ L + 4 := rfl
    omega
  have kL' : (Cmd.run (.loop 852 851 (swpBody S RN RD (UP' L0X SX TX))) Sf3).2 ≤ 106 * YB DB V ^ 4 :=
    le_trans hL2 (loop_le (V := V) (k := 104) (e := 3) (le_trans hMV hW))
  have hr : r = (Cmd.run (.loop 852 851 (swpBody S RN RD (UP' L0X SX TX))) Sf3).1 := by
    show (Cmd.run (swpC S RN RD (UP' L0X SX TX)) Sf).1 = _
    rw [hrun]
  rw [hrun, hr]
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hMs ▸ (by simpa using l3 852 (by omega) (by omega) : (Cmd.run (.loop 852 851 (swpBody S RN RD (UP' L0X SX TX))) Sf3).1.sc 852 = Sf3.sc 852)
  · exact fun m h1 h2 => l5 m h1 h2
  · intro y hy h1 h2
    rw [l3 y hy h1, lo3' y hy h2]
  · intro a ha h1 h2
    rw [l4 a ha h1 h2, lo3a a ha]
  · have c1'' : (Cmd.run ((setup (UP' L0X SX TX)).shift S) Sf).2 ≤ 60 * YB DB V ^ 2 := by rw [c1]; exact k1
    have c2'' : (Cmd.run ((cset mE 314).shift S) Sf1).2 ≤ PB DB V := by rw [c2]; exact k2'
    simp only
    omega

end ECDLP.L115
