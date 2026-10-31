import ECDLP.L80_Len
import ECDLP.L80_Bits
import ECDLP.L80_BWle
import ECDLP.L72_Init
import ECDLP.L71_Shift

/-!
# L80 / Write: the per-call frame writer
`frameW S` (run after `checkC m`) writes the instance data into the engine frame (arrays `S+k`, scalars `S+0`, `S+2`) in L72's layout.
`Reads72n` is L72's `Reads72` without the clause `A 3 = 0` (see REPORT: the engine's value/cost statements do not use it).
-/
namespace ECDLP.L80
open ECDLP.L76 ECDLP.L71 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

structure Reads72n (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (p a b X xR yR : ℕ) (π : List Bool) (ℓ bW : ℕ) : Prop where
  hp : numCells (A 0) 1 (σ 0) = p
  ha : numCells (A 1) 1 (σ 0) = a
  hb : numCells (A 2) 1 (σ 0) = b
  hxR : numCells (A 4) 1 (σ 0) = xR
  hyR : numCells (A 5) 1 (σ 0) = yR
  hOp : numCells (A 7) 1 (2 * σ 0 + 1) = 2 * p * p
  hX : numCells (A 8) 1 (σ 0) = X
  hlen : numCells (A 9) 1 (σ 0) = π.length
  hl : numCells (A 10) 1 (σ 0) = ℓ
  hbW : numCells (A 11) 1 (σ 0) = bW
  hpi : ∀ (q : ℕ) (h : q < π.length), (A 6 (q + 1) ≠ 0 ↔ π[q] = true)

theorem Reads72n.of_reads72 {σ A p a b X xR yR π ℓ bW} (h : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Reads72n σ A p a b X xR yR π ℓ bW :=
  ⟨h.hp, h.ha, h.hb, h.hxR, h.hyR, h.hOp, h.hX, h.hlen, h.hl, h.hbW, h.hpi⟩

def frameW (S : ℕ) : Cmd :=
  .seq lenC (.seq (padList 710 [(S + 0, 30, 815), (S + 1, 21, 815), (S + 2, 22, 815), (S + 4, 23, 815), (S + 5, 24, 815),
      (S + 7, 56, 817), (S + 8, 47, 815)])
    (.seq (piC (S + 6)) (.seq Bcmd (.seq (.copy 710 815) (.seq (oneA 60) (.seq (bitsC (S + 9) 2) (.seq (bitsC (S + 10) 782)
      (.seq (bitsC (S + 11) 836) (.seq (.copy (S + 0) 815) (.setK (S + 2) 0))))))))))

theorem pw_lt_len (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

set_option maxHeartbeats 4000000 in
theorem frameW_run (S : ℕ) (hS : 1400 ≤ S) (s : St) (W p a b x y X : ℕ) (τ : List Bool)
    (hW : s.sc 710 = W) (h30 : V (s.ar 30) W = p) (h21 : V (s.ar 21) W = a) (h22 : V (s.ar 22) W = b)
    (h23 : V (s.ar 23) W = x) (h24 : V (s.ar 24) W = y) (h47 : V (s.ar 47) W = X) (h56 : V (s.ar 56) W = 2 * (p * p))
    (h782 : s.sc 782 = Nat.size X) (hsc2 : s.sc 2 = τ.length) (hτ : ∀ j, j < τ.length → s.ar 1 j = ECDLP.L61.bitN (τ.getD j false))
    (h2 : 2 ≤ Nat.size p) (hab : a ≠ 0 ∨ b ≠ 0) (hap : a < p) (hbp : b < p) (hxp : x < p) (hyp : y < p) (hXp : X ≤ p) :
    let r := Cmd.run (frameW S) s
    Reads72n (unshift S r.1).sc (unshift S r.1).ar p a b X x y τ (Nat.size X) (ECDLP.L72.bWof (Nat.size p)) ∧
    (unshift S r.1).sc 0 = Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + τ.length + 1 ∧
    (unshift S r.1).sc 2 = 0 ∧ r.2 ≤ 10000 * (W + τ.length + 2) ^ 2 := by
  intro r
  -- stage 1: sizes and length
  obtain ⟨l810, l811, l812, l813, l814, l815, l817, lar, lfr, lcost⟩ := lenC_run s W p a b x y τ.length hW h30 h21 h22 h23 h24 hsc2
  generalize hA : Cmd.run lenC s = A at l810 l811 l812 l813 l814 l815 l817 lar lfr lcost
  obtain ⟨len, hlen⟩ : ∃ len, len = A.1.sc 815 := ⟨_, rfl⟩
  have hnz : ∀ y, ¬ Zlen y → A.1.sc y = s.sc y := lfr
  have A710 : A.1.sc 710 = W := by rw [hnz 710 (by unfold Zlen; omega), hW]
  have A2 : A.1.sc 2 = τ.length := by rw [hnz 2 (by unfold Zlen; omega), hsc2]
  have A782 : A.1.sc 782 = Nat.size X := by rw [hnz 782 (by unfold Zlen; omega), h782]
  -- bounds
  have hpl : Nat.size p ≤ len := by rw [hlen, l815]; omega
  have hlt : ∀ v, v < p → v < 2 ^ len := fun v hv =>
    lt_of_lt_of_le (lt_trans hv (Nat.lt_size_self p)) (Nat.pow_le_pow_right (by norm_num) hpl)
  have hp_len : p < 2 ^ len := lt_of_lt_of_le (Nat.lt_size_self p) (Nat.pow_le_pow_right (by norm_num) hpl)
  have hlen1 : 1 ≤ len := by rw [hlen, l815]; omega
  have hτlen : τ.length < 2 ^ len := lt_of_lt_of_le (Nat.lt_two_pow_self (n := τ.length))
    (Nat.pow_le_pow_right (by norm_num) (by rw [hlen, l815]; omega))
  have hXlen : Nat.size X < 2 ^ len := lt_of_lt_of_le (Nat.lt_two_pow_self (n := Nat.size X))
    (Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.size_le_size hXp) hpl))
  have hpl2 : Nat.size p + 2 ≤ len := by
    have : 1 ≤ Nat.size a ∨ 1 ≤ Nat.size b := by
      rcases hab with h | h
      · left; exact Nat.size_pos.2 (Nat.pos_of_ne_zero h)
      · right; exact Nat.size_pos.2 (Nat.pos_of_ne_zero h)
    rw [hlen, l815]; omega
  have hbWlen : ECDLP.L72.bWof (Nat.size p) < 2 ^ len :=
    lt_of_le_of_lt (bWof_le _ h2) (lt_of_lt_of_le (three_lt_pow _ h2) (Nat.pow_le_pow_right (by norm_num) hpl2))
  -- stage 2: the padded copies
  obtain ⟨P1, P2, P3, P4⟩ := padList_run 710 ⟨by norm_num, by norm_num⟩ W
    [(S + 0, 30, 815), (S + 1, 21, 815), (S + 2, 22, 815), (S + 4, 23, 815), (S + 5, 24, 815), (S + 7, 56, 817), (S + 8, 47, 815)]
    A.1 A710
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    (by simp [List.nodup_cons])
    (by intro q hq q' hq'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq hq'
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
  generalize hB : Cmd.run (padList 710 [(S + 0, 30, 815), (S + 1, 21, 815), (S + 2, 22, 815), (S + 4, 23, 815), (S + 5, 24, 815),
      (S + 7, 56, 817), (S + 8, 47, 815)]) A.1 = B at P1 P2 P3 P4
  have hB710 : B.1.sc 710 = W := by rw [P3 710 (by unfold ZP2; omega)]; exact A710
  have hB2 : B.1.sc 2 = τ.length := by rw [P3 2 (by unfold ZP2; omega)]; exact A2
  have hB782 : B.1.sc 782 = Nat.size X := by rw [P3 782 (by unfold ZP2; omega)]; exact A782
  have hB810 : B.1.sc 810 = Nat.size p := by rw [P3 810 (by unfold ZP2; omega)]; exact l810
  have hB815 : B.1.sc 815 = len := by rw [P3 815 (by unfold ZP2; omega)]; exact hlen.symm
  have hB817 : B.1.sc 817 = 2 * len + 1 := by rw [P3 817 (by unfold ZP2; omega), l817, ← hlen]
  have cells : ∀ (d src n : ℕ), (d, src, n) ∈ [(S + 0, 30, 815), (S + 1, 21, 815), (S + 2, 22, 815), (S + 4, 23, 815), (S + 5, 24, 815),
      (S + 7, 56, 817), (S + 8, 47, 815)] → ∀ i, 1 ≤ i → i ≤ A.1.sc n →
      B.1.ar d i = if i ≤ W then bt (s.ar src) i else 0 := by
    intro d src n hm i h1 h2
    have := P1 (d, src, n) hm i h1 h2
    rw [lar] at this; exact this
  have vP : V (B.1.ar (S + 0)) len = p := V_padval (s.ar 30) _ W len p
    (fun i h1 h2 => cells (S + 0) 30 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h30 hp_len
  have vA : V (B.1.ar (S + 1)) len = a := V_padval (s.ar 21) _ W len a
    (fun i h1 h2 => cells (S + 1) 21 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h21 (hlt a hap)
  have vB : V (B.1.ar (S + 2)) len = b := V_padval (s.ar 22) _ W len b
    (fun i h1 h2 => cells (S + 2) 22 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h22 (hlt b hbp)
  have vX : V (B.1.ar (S + 4)) len = x := V_padval (s.ar 23) _ W len x
    (fun i h1 h2 => cells (S + 4) 23 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h23 (hlt x hxp)
  have vY : V (B.1.ar (S + 5)) len = y := V_padval (s.ar 24) _ W len y
    (fun i h1 h2 => cells (S + 5) 24 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h24 (hlt y hyp)
  have vXX : V (B.1.ar (S + 8)) len = X := V_padval (s.ar 47) _ W len X
    (fun i h1 h2 => cells (S + 8) 47 815 (by simp) i h1 (by rw [← hlen] ; exact h2)) h47
    (lt_of_le_of_lt hXp hp_len)
  have h2pp : 2 * (p * p) < 2 ^ (2 * len + 1) := by
    have h1 : p * p < 2 ^ len * 2 ^ len := Nat.mul_lt_mul'' hp_len hp_len
    have : 2 ^ (2 * len + 1) = 2 * (2 ^ len * 2 ^ len) := by rw [pow_succ, two_mul, pow_add]; ring
    omega
  have vOp : V (B.1.ar (S + 7)) (2 * len + 1) = 2 * (p * p) := V_padval (s.ar 56) _ W (2 * len + 1) _
    (fun i h1 h2 => cells (S + 7) 56 817 (by simp) i h1 (by rw [l817, ← hlen]; exact h2)) h56 h2pp
  -- stage 3: the prefix
  obtain ⟨Q1, Q2, Q3, Q4⟩ := piC_run (S + 6) (by omega) B.1 τ.length hB2
  generalize hC : Cmd.run (piC (S + 6)) B.1 = C at Q1 Q2 Q3 Q4
  have C710 : C.1.sc 710 = W := by rw [Q3 710 (by unfold ZP2; omega)]; exact hB710
  have C2 : C.1.sc 2 = τ.length := by rw [Q3 2 (by unfold ZP2; omega)]; exact hB2
  have C782 : C.1.sc 782 = Nat.size X := by rw [Q3 782 (by unfold ZP2; omega)]; exact hB782
  have C810 : C.1.sc 810 = Nat.size p := by rw [Q3 810 (by unfold ZP2; omega)]; exact hB810
  have C815 : C.1.sc 815 = len := by rw [Q3 815 (by unfold ZP2; omega)]; exact hB815
  -- stage 4: the width bW
  obtain ⟨R1, R2, R3, R4, R5⟩ := Bcmd_run C.1 (Nat.size p) C810 (by omega)
  generalize hD : Cmd.run Bcmd C.1 = D at R1 R2 R3 R4 R5
  have D2 : D.1.sc 2 = τ.length := by rw [R4 2 (by unfold ZBW; omega)]; exact C2
  have D782 : D.1.sc 782 = Nat.size X := by rw [R4 782 (by unfold ZBW; omega)]; exact C782
  have D815 : D.1.sc 815 = len := by rw [R4 815 (by unfold ZBW; omega)]; exact C815
  -- stage 5, 6: width := len, the constant 1
  obtain ⟨F1, F2, F3, F4, F5⟩ := oneA_run 60 (D.1.setSc 710 (D.1.sc 815)) len (by simp [St.setSc, D815]) hlen1
  generalize hF : Cmd.run (oneA 60) (D.1.setSc 710 (D.1.sc 815)) = F at F1 F2 F3 F4 F5
  have F710 : F.1.sc 710 = len := by
    rw [F4 710 (by unfold ZK ZC; omega)]; simp [St.setSc, D815]
  have F2s : F.1.sc 2 = τ.length := by
    rw [F4 2 (by unfold ZK ZC; omega)]; simp [St.setSc, D2]
  have F782 : F.1.sc 782 = Nat.size X := by
    rw [F4 782 (by unfold ZK ZC; omega)]; simp [St.setSc, D782]
  have F836 : F.1.sc 836 = ECDLP.L72.bWof (Nat.size p) := by
    rw [F4 836 (by unfold ZK ZC; omega)]; simp [St.setSc, R1]
  have F815 : F.1.sc 815 = len := by
    rw [F4 815 (by unfold ZK ZC; omega)]; simp [St.setSc, D815]
  -- stage 7..9: the bit arrays
  obtain ⟨G11, G12, G13, G14⟩ := bitsC_run (S + 9) 2 (by omega) (by unfold Zb ZC ZA; omega) (by norm_num) F.1 len F710 F2
  generalize hG1 : Cmd.run (bitsC (S + 9) 2) F.1 = G1 at G11 G12 G13 G14
  have G1_710 : G1.1.sc 710 = len := by rw [G13 710 (by unfold Zb ZC ZA; omega)]; exact F710
  have G1_60 : V (G1.1.ar 60) len = 1 := by rw [G12 60 (by omega)]; exact F2
  have G1_782 : G1.1.sc 782 = Nat.size X := by rw [G13 782 (by unfold Zb ZC ZA; omega)]; exact F782
  have G1_836 : G1.1.sc 836 = ECDLP.L72.bWof (Nat.size p) := by rw [G13 836 (by unfold Zb ZC ZA; omega)]; exact F836
  have G1_815 : G1.1.sc 815 = len := by rw [G13 815 (by unfold Zb ZC ZA; omega)]; exact F815
  obtain ⟨G21, G22, G23, G24⟩ := bitsC_run (S + 10) 782 (by omega) (by unfold Zb ZC ZA; omega) (by norm_num) G1.1 len G1_710 G1_60
  generalize hG2 : Cmd.run (bitsC (S + 10) 782) G1.1 = G2 at G21 G22 G23 G24
  have G2_710 : G2.1.sc 710 = len := by rw [G23 710 (by unfold Zb ZC ZA; omega)]; exact G1_710
  have G2_60 : V (G2.1.ar 60) len = 1 := by rw [G22 60 (by omega)]; exact G1_60
  have G2_836 : G2.1.sc 836 = ECDLP.L72.bWof (Nat.size p) := by rw [G23 836 (by unfold Zb ZC ZA; omega)]; exact G1_836
  have G2_815 : G2.1.sc 815 = len := by rw [G23 815 (by unfold Zb ZC ZA; omega)]; exact G1_815
  obtain ⟨G31, G32, G33, G34⟩ := bitsC_run (S + 11) 836 (by omega) (by unfold Zb ZC ZA; omega) (by norm_num) G2.1 len G2_710 G2_60
  generalize hG3 : Cmd.run (bitsC (S + 11) 836) G2.1 = G3 at G31 G32 G33 G34
  have G3_815 : G3.1.sc 815 = len := by rw [G33 815 (by unfold Zb ZC ZA; omega)]; exact G2_815
  have hr : r.1 = (G3.1.setSc (S + 0) (G3.1.sc 815)).setSc (S + 2) 0 := by
    simp only [r, frameW, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, hA, hB, hC, hD, hF, hG1, hG2, hG3]
  have hfinAr : ∀ a, (unshift S r.1).ar a = G3.1.ar (S + a) := fun a => by rw [hr]; rfl
  have hfin0 : (unshift S r.1).sc 0 = len := by
    rw [hr]; simp [unshift, St.setSc, G3_815]
  have hfin2 : (unshift S r.1).sc 2 = 0 := by
    rw [hr]; simp [unshift, St.setSc]
  -- array bookkeeping
  have keepB : ∀ a, a ≠ S + 6 → a ≠ 60 → a ≠ S + 9 → a ≠ S + 10 → a ≠ S + 11 → G3.1.ar a = B.1.ar a := by
    intro a h6 h60 h9' h10 h11
    rw [G32 a h11, G22 a h10, G12 a h9', F3 a h60]
    have : (D.1.setSc 710 (D.1.sc 815)).ar a = D.1.ar a := rfl
    rw [this, R3, Q2 a h6]
  have keepC : G3.1.ar (S + 6) = C.1.ar (S + 6) := by
    rw [G32 _ (by omega), G22 _ (by omega), G12 _ (by omega), F3 _ (by omega)]
    have : (D.1.setSc 710 (D.1.sc 815)).ar (S + 6) = D.1.ar (S + 6) := rfl
    rw [this, R3]
  have vTau : V (G3.1.ar (S + 9)) len = τ.length := by
    rw [G32 _ (by omega), G22 _ (by omega), G11, F2s, Nat.mod_eq_of_lt hτlen]
  have vEll : V (G3.1.ar (S + 10)) len = Nat.size X := by
    rw [G32 _ (by omega), G21, G1_782, Nat.mod_eq_of_lt hXlen]
  have vBw : V (G3.1.ar (S + 11)) len = ECDLP.L72.bWof (Nat.size p) := by
    rw [G31, G2_836, Nat.mod_eq_of_lt hbWlen]
  have hr2 : r.2 ≤ A.2 + B.2 + C.2 + D.2 + F.2 + G1.2 + G2.2 + G3.2 + 20 := by
    simp only [r, frameW, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, hA, hB, hC, hD, hF, hG1, hG2, hG3]
    omega
  have hcost : r.2 ≤ 10000 * (W + τ.length + 2) ^ 2 := by
    obtain ⟨T, hT⟩ : ∃ T, T = W + τ.length + 2 := ⟨_, rfl⟩
    rw [← hT]
    have szW : ∀ v, V (s.ar 30) W = v → Nat.size v ≤ W := fun v hv => by
      have := V_lt (s.ar 30) W; rw [hv] at this; exact Nat.size_le.2 this
    have sp : Nat.size p ≤ W := szW p h30
    have sa : Nat.size a ≤ W := by have := V_lt (s.ar 21) W; rw [h21] at this; exact Nat.size_le.2 this
    have sb : Nat.size b ≤ W := by have := V_lt (s.ar 22) W; rw [h22] at this; exact Nat.size_le.2 this
    have sx : Nat.size x ≤ W := by have := V_lt (s.ar 23) W; rw [h23] at this; exact Nat.size_le.2 this
    have sy : Nat.size y ≤ W := by have := V_lt (s.ar 24) W; rw [h24] at this; exact Nat.size_le.2 this
    have sX : Nat.size X ≤ Nat.size p := Nat.size_le_size hXp
    have hbWT : ECDLP.L72.bWof (Nat.size p) ≤ 3 * Nat.size p + 3 := bWof_le _ h2
    have hlenT : len ≤ 5 * T := by rw [hlen, l815]; omega
    have hT1 : 1 ≤ T := by omega
    have hTT : T ≤ T * T := Nat.le_mul_self T
    have hn2T : τ.length ≤ T := by omega
    have hLT : Nat.size p ≤ T := by omega
    have h25 : 25 * len + 11 ≤ 136 * T := by omega
    -- stage costs
    have cA : A.2 ≤ 200 * T := by omega
    have cB : B.2 ≤ 400 * T := by
      have := P4
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
      rw [l817, ← hlen] at this
      omega
    have cC : C.2 ≤ 8 * T := by omega
    have cD : D.2 ≤ 1400 * (T * T) := by
      have h1 : Nat.size p * Nat.size p ≤ T * T := Nat.mul_le_mul hLT hLT
      have h2 : 1000 * Nat.size p * Nat.size p = 1000 * (Nat.size p * Nat.size p) := by ring
      rw [h2] at R5
      omega
    have cF : F.2 ≤ 25 * T + 10 := by omega
    have cG1 : G1.2 ≤ 25 * T + 3 + 136 * (T * T) := by
      rw [F2s] at G14
      have := Nat.mul_le_mul hn2T h25
      have e : T * (136 * T) = 136 * (T * T) := by ring
      omega
    have cG2 : G2.2 ≤ 25 * T + 3 + 136 * (T * T) := by
      rw [G1_782] at G24
      have := Nat.mul_le_mul (le_trans sX hLT) h25
      have e : T * (136 * T) = 136 * (T * T) := by ring
      omega
    have cG3 : G3.2 ≤ 25 * T + 3 + 36 * 136 * (T * T) := by
      rw [G2_836] at G34
      have h36 : ECDLP.L72.bWof (Nat.size p) ≤ 36 * T := by omega
      have := Nat.mul_le_mul h36 h25
      have e : 36 * T * (136 * T) = 36 * 136 * (T * T) := by ring
      omega
    have : 10000 * T ^ 2 = 10000 * (T * T) := by ring
    rw [this]
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hfin2, hcost⟩
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vP
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vA
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vB
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vX
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vY
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    have : 2 * p * p = 2 * (p * p) := by ring
    rw [this]; exact vOp
  · rw [hfin0, hfinAr, keepB _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact vXX
  · rw [hfin0, hfinAr]; exact vTau
  · rw [hfin0, hfinAr]; exact vEll
  · rw [hfin0, hfinAr]; exact vBw
  · intro q hq
    rw [hfinAr, keepC]
    have h1 := Q1 q hq
    have h2 : B.1.ar 1 = s.ar 1 := by rw [P2 1 (by simp; omega), lar]
    rw [h1, h2]
    have h3 := hτ q hq
    have h4 : τ.getD q false = τ[q] := by simp [List.getD_eq_getElem?_getD, hq]
    rw [h4] at h3
    cases hb : τ[q] <;> simp [bt, h3, ECDLP.L61.bitN, hb]
  · rw [hfin0, hlen, l815]

end ECDLP.L80
