import ECDLP.L61_Main
import ECDLP.L70_Capstone

/-!
# L77 / Top: the driver with a ONE-TIME gate, `top = G ; ifZero fl NONE (drvZ m c)`

* `drvZ_spec_from` : `drvZ_spec` from an arbitrary start state `st0` that agrees with `St.init` on what the parser reads
  (`sc 0`, `ar 0`, `sc 2, 5, 7, 8 = 0`), i.e. a start state with a dirty frame (the gate's scratch space).
* `GateSpec F G fl Tg` : run on `St.init (encB x)`, `G` leaves `sc 0`, `ar 0`, `sc 2,5,7,8` as the parser wants them, puts a flag in
  scalar `fl` that is `0` iff `¬ F x`, in `Tg |encB x|` steps.
* `ZSpecAt F m c T` : L61's `ZSpec` required only on instances satisfying `F`.
* `top_out`, `top_machine`, `top_subexp` : the correctness, the TM, and the sub-exponential bound of the restructured driver.
-/
namespace ECDLP.L77
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Turing Computability

theorem drvZ_spec_from (m : ℕ) (c : Cmd) (xs π r : List Bool) (hxs : xs = block π ++ r)
    (Z : List Bool → ℕ) (ok : List Bool → Prop) (T : ℕ)
    (hk : Keep c) (ho : Orc c (startingMemory xs) xs.length Z ok T) (hπ : ok π)
    (hW : 0 < Z π → ∀ i, i < m * (xs.length + 1) + 1 → ((stepF Z)^[i] (π, false)).2 = false →
      ok (((stepF Z)^[i] (π, false)).1 ++ [false]) ∧ ok (((stepF Z)^[i] (π, false)).1 ++ [true]))
    (st0 : St) (h0 : st0.sc 0 = xs.length) (hA : st0.ar 0 = startingMemory xs)
    (e2 : st0.sc 2 = 0) (e5 : st0.sc 5 = 0) (e7 : st0.sc 7 = 0) (e8 : st0.sc 8 = 0) :
    outOf ((Cmd.run (drvZ m c) st0).1.ar 2) =
      ECDLP.encOut (if 0 < Z π then some (((stepF Z)^[m * (xs.length + 1) + 1] (π, false)).1) else none) ∧
    (Cmd.run (drvZ m c) st0).2 ≤ drvBound m xs.length T := by
  subst hxs
  simp only [drvZ, Cmd.run_seq, Cmd.run_ifZero]
  set L := (block π ++ r).length with hL
  have hπL : π.length ≤ L := by
    have := block_length π; rw [hL]; simp only [List.length_append]; omega
  obtain ⟨p2, pc, p0, pA, psc, par, pcost⟩ := parse_run π r st0 hA h0 e2 e7 e8
  have p0' : (Cmd.run (.loop 0 1 parseBody) st0).1.sc 0 = L := by rw [p0, h0]
  have pA' : (Cmd.run (.loop 0 1 parseBody) st0).1.ar 0 = startingMemory (block π ++ r) := by rw [pA, hA]
  have p5 : (Cmd.run (.loop 0 1 parseBody) st0).1.sc 5 = 0 := by
    rw [psc 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), e5]
  have pcost' : (Cmd.run (.loop 0 1 parseBody) st0).2 ≤ 21 * L + 1 := by rw [h0] at pcost; exact pcost
  generalize hs1 : Cmd.run (.loop 0 1 parseBody) st0 = s1 at p2 pc p0' pA' p5 pcost' ⊢
  have hv := ho.val s1.1 π p0' pA' p2 pc hπ
  have hkS := hk.sc s1.1
  have hkA := hk.ar s1.1
  generalize hr2 : Cmd.run c s1.1 = r2 at hv hkS hkA ⊢
  have r20 : r2.1.sc 0 = L := by rw [hkS 0 (by norm_num) (by norm_num), p0']
  by_cases hp : 0 < Z π
  · have h3 : r2.1.sc 3 ≠ 0 := by rw [hv.1]; simp [hp]
    simp only [h3, if_false, Cmd.run_seq, hp, if_true]
    obtain ⟨b9, b0, bsc, bar, bcost⟩ := boundCmd_run m r2.1
    rw [r20] at b9 bcost
    set R := m * (L + 1) + 1 with hR
    generalize hsb : Cmd.run (boundCmd m) r2.1 = sb at b9 b0 bsc bar bcost ⊢
    have hRI : RInv (startingMemory (block π ++ r)) L R π false sb.1 := by
      refine ⟨?_, ?_, b9, ?_, ?_, ?_⟩
      · rw [b0, r20]
      · rw [bar 0, hkA 0 (by norm_num), pA']
      · rw [bsc 2 (by norm_num) (by norm_num), hkS 2 (by norm_num) (by norm_num), p2]
      · intro j hj
        rw [bar 1, hkA 1 (by norm_num)]
        exact pc j hj
      · rw [bsc 5 (by norm_num) (by norm_num), hkS 5 (by norm_num) (by norm_num), p5]; simp
    let P : ℕ → St → Prop := fun j s => RInv (startingMemory (block π ++ r)) L R
      ((stepF Z)^[j] (π, false)).1 ((stepF Z)^[j] (π, false)).2 s
    have hstep : ∀ j s, j < sb.1.sc 9 → P j s → P (j + 1) (Cmd.run (roundBody c) (s.setSc 1 j)).1 := by
      intro j s hj hs
      rw [b9] at hj
      have := (round_step c _ L R T Z ok hk ho _ _ (s.setSc 1 j) (RInv_setSc1 hs j) (hW hp j hj))
      show RInv _ L R (((stepF Z)^[j + 1]) (π, false)).1 (((stepF Z)^[j + 1]) (π, false)).2 _
      rw [Function.iterate_succ_apply']
      exact this.1
    have hcost : ∀ j s, j < sb.1.sc 9 → P j s → (Cmd.run (roundBody c) (s.setSc 1 j)).2 ≤ 2 * T + 30 := by
      intro j s hj hs
      rw [b9] at hj
      exact (round_step c _ L R T Z ok hk ho _ _ (s.setSc 1 j) (RInv_setSc1 hs j) (hW hp j hj)).2
    have hP0 : P 0 sb.1 := hRI
    have hI := Cmd.loop_inv (b := 9) (c := 1) (body := roundBody c) P hP0 hstep
    have hC := Cmd.loop_cost_le (b := 9) (c := 1) (body := roundBody c) P (2 * T + 30) hP0 hstep hcost
    rw [b9] at hI hC
    generalize hsl : Cmd.run (.loop 9 1 (roundBody c)) sb.1 = sl at hI hC ⊢
    obtain ⟨_, _, _, i2, ic, _⟩ := hI
    obtain ⟨o1, o2⟩ := someOut_run _ sl.1 i2 ic
    have hlen := iter_len Z π R
    refine ⟨o1, ?_⟩
    simp only [drvBound]
    have hmL : m ≤ m * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hcl : R * (2 * T + 30 + 1) = m * (L + 1) * (2 * T + 31) + 2 * T + 31 := by rw [hR]; ring
    have hlen' : ((stepF Z)^[R] (π, false)).1.length ≤ L + R := by omega
    have e2 : (m + 1) * (2 * L + 4) = 2 * (m * (L + 1)) + 2 * m + 2 * L + 4 := by ring
    have e3 : (m * (L + 1) + 2) * (2 * T + 31) = m * (L + 1) * (2 * T + 31) + 4 * T + 62 := by ring
    have e4 : (m + 2) * (40 * L + 40) = 40 * (m * (L + 1)) + 80 * L + 80 := by ring
    rw [e3, e4]
    omega
  · have h3 : r2.1.sc 3 = 0 := by rw [hv.1]; simp [hp]
    simp only [h3, if_true, hp, if_false]
    obtain ⟨o1, o2⟩ := noneOut_run r2.1
    refine ⟨o1, ?_⟩
    simp only [drvBound]
    have e4 : (m + 2) * (40 * L + 40) = 40 * (m * (L + 1)) + 80 * L + 80 := by ring
    have e3 : (m * (L + 1) + 2) * (2 * T + 31) = m * (L + 1) * (2 * T + 31) + 4 * T + 62 := by ring
    rw [e3, e4]
    omega


/-- The part of `Good` that is not about `p` being prime or the prefix: `Δ ≠ 0` and `R` nonsingular. -/
def Gx2 (x : Inst) : Prop :=
  (Wc x.1 x.2.1 x.2.2.1).Δ ≠ 0 ∧
    (Wc x.1 x.2.1 x.2.2.1).toAffine.Nonsingular ((x.2.2.2.1 : ℕ) : ZMod x.1) ((x.2.2.2.2.1 : ℕ) : ZMod x.1)

/-- The `x`-only part of `Good`: `p` prime, `Δ ≠ 0`, `R` nonsingular. -/
def Gx (x : Inst) : Prop := x.1.Prime ∧ Gx2 x

theorem good_iff (m : ℕ) (x : Inst) (τ : List Bool) : ECDLP.L70.Good m x τ ↔ Gx x ∧ τ.length ≤ nlen m x := by
  unfold ECDLP.L70.Good Gx Gx2
  tauto

/-- If the `x`-part is bad there is no decomposition at all, so `lexLeast = none`. -/
theorem lexLeast_none_of_not_Gx (m : ℕ) (x : Inst) (h : ¬ Gx x) : lexLeast m x = none := by
  have h0 : ¬ 0 < Zc m x (pre x) := fun hp => h ((good_iff m x _).1 (ECDLP.L70.Zc_pos_good m x _ hp)).1
  rw [lexLeast_eq_iter m x 0 (fun hp => absurd hp h0)]
  simp [h0]

/-- **`ZSpec` required only on instances satisfying `F`.** -/
structure ZSpecAt (F : Inst → Prop) (m : ℕ) (c : Cmd) (T : ℕ → ℕ) : Prop where
  keep : Keep c
  spec : ∀ (x : Inst) (st : St) (τ : List Bool), F x → st.sc 0 = (encB x).length →
    st.ar 0 = startingMemory (encB x) → st.sc 2 = τ.length →
    (∀ j, j < τ.length → st.ar 1 j = bitN (τ.getD j false)) → okInst m x τ →
    (Cmd.run c st).1.sc 3 = (if 0 < Zc m x τ then 1 else 0) ∧ (Cmd.run c st).2 ≤ T (encB x).length

theorem driver_out_from (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (F : Inst → Prop) (h : ZSpecAt F m c T) (x : Inst) (hx : F x)
    (st0 : St) (h0 : st0.sc 0 = (encB x).length) (hA : st0.ar 0 = startingMemory (encB x))
    (e2 : st0.sc 2 = 0) (e5 : st0.sc 5 = 0) (e7 : st0.sc 7 = 0) (e8 : st0.sc 8 = 0) :
    outOf ((Cmd.run (drvZ m c) st0).1.ar 2) = encOut (lexLeast m x) ∧
      (Cmd.run (drvZ m c) st0).2 ≤ drvBound m (encB x).length (T (encB x).length) := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  set x : Inst := (p, a, b, xR, yR, π) with hxdef
  have hxs : encB x = block (pre x) ++ [p, a, b, xR, yR].flatMap (fun n => block (encodeNat n)) := rfl
  set L := (encB x).length with hL
  have ho : Orc (c) (startingMemory (encB x)) L (Zc m x) (okInst m x) (T L) :=
    ⟨fun st τ h0 hA h2 hc hok => h.spec x st τ hx h0 hA h2 hc hok⟩
  have hπ : okInst m x (pre x) := ⟨List.prefix_refl _, le_max_right _ _⟩
  have hW : 0 < Zc m x (pre x) → ∀ i, i < m * (L + 1) + 1 → ((stepF (Zc m x))^[i] (pre x, false)).2 = false →
      okInst m x (((stepF (Zc m x))^[i] (pre x, false)).1 ++ [false]) ∧
      okInst m x (((stepF (Zc m x))^[i] (pre x, false)).1 ++ [true]) := by
    intro h0 i _ hd
    obtain ⟨hp, hz⟩ := walk_inv m x h0 i
    have hl := Zc_pos_len m x _ (hz hd)
    refine ⟨⟨hp.trans (List.prefix_append _ _), ?_⟩, ⟨hp.trans (List.prefix_append _ _), ?_⟩⟩ <;>
      simp only [List.length_append, List.length_singleton] <;> omega
  obtain ⟨h1, h2⟩ := drvZ_spec_from m c (encB x) (pre x) _ hxs (Zc m x) (okInst m x) (T L) h.keep ho hπ hW
    st0 h0 hA e2 e5 e7 e8
  refine ⟨?_, h2⟩
  rw [h1]
  congr 1
  rw [lexLeast_eq_iter m x (m * (L + 1) + 1)]
  intro hpos
  have := Zc_pos_len m x _ hpos
  have hn : nlen m x ≤ m * ((encodeNat p).length + 1) := nlen_le m p a b xR yR π
  have hp : (encodeNat p).length ≤ L := len_encB_ge p a b xR yR π
  have : m * ((encodeNat p).length + 1) ≤ m * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The one-time gate.**  Run on the initial state of the input `encB x`, `G` leaves the parser's preconditions
(`sc 0`, `ar 0`, `sc 2,5,7,8`) intact, and a flag in scalar `fl` which is `0` exactly when `¬ F x`. -/
structure GateSpec (F : Inst → Prop) (G : Cmd) (fl : ℕ) (Tg : ℕ → ℕ) : Prop where
  spec : ∀ x : Inst,
    (Cmd.run G (St.init (encB x))).1.sc 0 = (encB x).length ∧
    (Cmd.run G (St.init (encB x))).1.ar 0 = startingMemory (encB x) ∧
    (Cmd.run G (St.init (encB x))).1.sc 2 = 0 ∧ (Cmd.run G (St.init (encB x))).1.sc 5 = 0 ∧
    (Cmd.run G (St.init (encB x))).1.sc 7 = 0 ∧ (Cmd.run G (St.init (encB x))).1.sc 8 = 0 ∧
    ((Cmd.run G (St.init (encB x))).1.sc fl = 0 ↔ ¬ F x) ∧
    (Cmd.run G (St.init (encB x))).2 ≤ Tg (encB x).length

/-- **The restructured driver:** `G ; ifZero fl NONE (drvZ m c)`. -/
def topCmd (G : Cmd) (fl : ℕ) (m : ℕ) (c : Cmd) : Cmd := .seq G (.ifZero fl noneOut (drvZ m c))

theorem top_out (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ) (F : Inst → Prop)
    (hG : GateSpec F G fl Tg) (hc : ZSpecAt F m c T) (hnec : ∀ x, ¬ F x → lexLeast m x = none) (x : Inst) :
    outOf ((srcOut (topCmd G fl m c) (encB x)).ar 2) = encOut (lexLeast m x) ∧
      srcCost (topCmd G fl m c) (encB x) ≤ Tg (encB x).length + drvBound m (encB x).length (T (encB x).length) + 2 := by
  obtain ⟨g0, gA, g2, g5, g7, g8, gf, gc⟩ := hG.spec x
  simp only [srcOut, srcCost, topCmd, Cmd.run_seq, Cmd.run_ifZero]
  generalize Cmd.run G (St.init (encB x)) = r at g0 gA g2 g5 g7 g8 gf gc ⊢
  by_cases hF : F x
  · have hz : r.1.sc fl ≠ 0 := fun h => (gf.1 h) hF
    simp only [hz, if_false]
    obtain ⟨o1, o2⟩ := driver_out_from m c T F hc x hF r.1 g0 gA g2 g5 g7 g8
    refine ⟨o1, ?_⟩
    omega
  · have hz : r.1.sc fl = 0 := gf.2 hF
    simp only [hz, if_true]
    obtain ⟨o1, o2⟩ := noneOut_run r.1
    rw [hnec x hF]
    refine ⟨o1, ?_⟩
    simp only [drvBound]
    omega

theorem top_machine (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ) (F : Inst → Prop)
    (hG : GateSpec F G fl Tg) (hc : ZSpecAt F m c T) (hnec : ∀ x, ¬ F x → lexLeast m x = none) :
    ∃ (M : TM2ComputableInTime encB encOut (lexLeast m)) (Q k0 cc : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ L, M.time L = cc * (Q * (L + k0 + (Tg L + drvBound m L (T L) + 2) + 1) ^ 2 + L + 1) ^ 3 + 1 :=
  tm_of_source encB encOut (lexLeast m) (topCmd G fl m c) 2 (fun L => Tg L + drvBound m L (T L) + 2)
    (fun x => (top_out m c G fl T Tg F hG hc hnec x).1) (fun x => (top_out m c G fl T Tg F hG hc hnec x).2)

set_option maxRecDepth 100000 in
/-- **Sub-exponential corollary** for the gated driver. -/
theorem top_subexp (m : ℕ) (c G : Cmd) (fl : ℕ) (T Tg : ℕ → ℕ) (F : Inst → Prop)
    (hG : GateSpec F G fl Tg) (hc : ZSpecAt F m c T) (hnec : ∀ x, ¬ F x → lexLeast m x = none)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k))
    (hTg : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) :
    ∃ M : TM2ComputableInTime encB encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  obtain ⟨M, Q, k0, cc, hfin, ht⟩ := top_machine m c G fl T Tg F hG hc hnec
  set D := 71 * (m + 2) + 102 with hD
  have hB : ∀ L, Tg L + drvBound m L (T L) + 2 ≤ D * ((L + 1) * ((Tg L + T L) + 1)) := by
    intro L
    have h1 := drvBound_le m L (T L)
    have h2 : (L + 1) * (T L + 1) ≤ (L + 1) * ((Tg L + T L) + 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 1 ≤ (L + 1) * ((Tg L + T L) + 1) := Nat.mul_pos (by omega) (by omega)
    have h4 : Tg L + 2 ≤ 2 * ((L + 1) * ((Tg L + T L) + 1)) := by nlinarith [Nat.zero_le (L * (Tg L + T L))]
    have h5 : (71 * (m + 2) + 100) * ((L + 1) * (T L + 1)) ≤ (71 * (m + 2) + 100) * ((L + 1) * ((Tg L + T L) + 1)) :=
      Nat.mul_le_mul_left _ h2
    have h6 : D * ((L + 1) * ((Tg L + T L) + 1)) =
        (71 * (m + 2) + 100) * ((L + 1) * ((Tg L + T L) + 1)) + 2 * ((L + 1) * ((Tg L + T L) + 1)) := by
      rw [hD]; ring
    omega
  refine ⟨M, hfin, fun k hk => ?_⟩
  obtain ⟨C1, hC1⟩ := hT (12 * k) (by omega)
  obtain ⟨C2, hC2⟩ := hTg (12 * k) (by omega)
  refine ⟨(cc * (Q * (k0 + 1 + D) ^ 2 + 1) ^ 3 + 1) * ((12 * k + 1) ^ 6 * (C1 + C2 + 1) ^ 6), fun L => ?_⟩
  rw [ht L]
  have hpoly := time_poly_aux Q k0 cc D L (Tg L + T L) _ (hB L)
  set P := 2 ^ (L / (12 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (12 * k + 1) * P := by
    have h0 := Factoring.Aux.le_two_pow_div L (12 * k) (by omega)
    rw [← hP] at h0
    have h1 : (12 * k + 1) * P = (12 * k) * P + P := by ring
    omega
  have hv : (Tg L + T L) + 1 ≤ (C1 + C2 + 1) * P := by
    have a := hC1 L; have b := hC2 L; rw [← hP] at a b
    have h1 : (C1 + C2 + 1) * P = C1 * P + C2 * P + P := by ring
    omega
  have h1 : (L + 1) ^ 6 * ((Tg L + T L) + 1) ^ 6 ≤ ((12 * k + 1) * P) ^ 6 * ((C1 + C2 + 1) * P) ^ 6 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hu 6) (Nat.pow_le_pow_left hv 6)
  have h2 : ((12 * k + 1) * P) ^ 6 * ((C1 + C2 + 1) * P) ^ 6 =
      ((12 * k + 1) ^ 6 * (C1 + C2 + 1) ^ 6) * P ^ 12 := by ring
  have h3 : P ^ 12 ≤ 2 ^ (L / k) := pow12_le L k
  calc _ ≤ (cc * (Q * (k0 + 1 + D) ^ 2 + 1) ^ 3 + 1) * ((L + 1) ^ 6 * ((Tg L + T L) + 1) ^ 6) := hpoly
    _ ≤ (cc * (Q * (k0 + 1 + D) ^ 2 + 1) ^ 3 + 1) * (((12 * k + 1) ^ 6 * (C1 + C2 + 1) ^ 6) * P ^ 12) :=
        Nat.mul_le_mul_left _ (h2 ▸ h1)
    _ ≤ (cc * (Q * (k0 + 1 + D) ^ 2 + 1) ^ 3 + 1) * (((12 * k + 1) ^ 6 * (C1 + C2 + 1) ^ 6) * 2 ^ (L / k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = _ := by ring

end ECDLP.L77
