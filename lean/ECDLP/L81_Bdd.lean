import ECDLP.L81_Idx

/-!
# L81 / Bdd: value bounds (`Bdd V`) of the read expressions and of the oracle `badE`

Hypotheses (numeric): memory cells `<= 1`, `2 <= V`, the scalar `sigma 0`, `2 sigma 0 + 1`, the bit positions `jj + 2` and the values of `bW, |pi|, ell` are `<= V`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L81
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 ECDLP.L76 Cst Slot

section valE
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- the Horner body of `valE` -/
def valBody (k t x y : ℕ) : Ex :=
  .add (.mul (.var y) (.lit 2)) (nbitW (.var k) t (.sub (.sub (.var k) (.lit 1)) (.var x)))

theorem valE_step (k t x y : ℕ) (hxk : x ≠ k) (hyk : y ≠ k) (hxy : x ≠ y) (j s : ℕ) (hj : j < σ k) :
    eval (Function.update (Function.update σ x j) y s) A (valBody k t x y) = s * 2 + bt (A t) (σ k - j) := by
  set n := σ k with hn
  rw [valBody, eval, eval, eval_nbitW]
  simp only [eval, Function.update_self, Function.update_of_ne (Ne.symm hxk), Function.update_of_ne (Ne.symm hyk),
    Function.update_of_ne hxy]
  rw [← hn]
  have e1 : n - 1 - j < n := by omega
  rw [testBit_numCells _ _ _ _ e1]
  have e2 : 1 + (n - 1 - j) = n - j := by omega
  rw [e2]
  unfold bt
  by_cases h : A t (n - j) = 0 <;> simp [h]

theorem valE_key (k t x y : ℕ) (hxk : x ≠ k) (hyk : y ≠ k) (hxy : x ≠ y) :
    ∀ j, j ≤ σ k → iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A (valBody k t x y)) 0 j =
      V (A t) (σ k) / 2 ^ (σ k - j) := by
  intro j
  induction j with
  | zero => intro _; simp [iterF, Nat.div_eq_of_lt (V_lt _ _)]
  | succ j ih =>
    intro hj
    rw [iterF, ih (by omega), valE_step k t x y hxk hyk hxy j _ (by omega), T_step (A t) (σ k) j (by omega)]
    ring

end valE

section bddlemmas
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem bdd_ifLt {e f a b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e < eval σ A f → Bdd V σ A a)
    (h4 : ¬ eval σ A e < eval σ A f → Bdd V σ A b) : Bdd V σ A (.ifLt e f a b) := by
  refine ⟨h1, h2, ?_⟩
  split_ifs with h
  · exact h3 h
  · exact h4 h

theorem bdd_lit {k : ℕ} (h : k ≤ V) : Bdd V σ A (.lit k) := h

theorem bdd_bitRd {t : ℕ} {i : Ex} (hi : Bdd V σ A i) (hiV : eval σ A i ≤ V) (hA : ∀ a i, A a i ≤ 1) (h1 : 1 ≤ V) :
    Bdd V σ A (bitRd t i) :=
  bdd_ifLt (bdd_lit (Nat.zero_le V)) ⟨hi, le_trans (hA _ _) h1⟩ (fun _ => bdd_lit h1) (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_nbitW {w : Ex} {t : ℕ} {i : Ex} (hw : Bdd V σ A w) (hi : Bdd V σ A i) (hwV : eval σ A w ≤ V)
    (hA : ∀ a i, A a i ≤ 1) (h1 : 1 ≤ V) : Bdd V σ A (nbitW w t i) :=
  bdd_ifLt hi hw
    (fun h => bdd_bitRd ⟨hi, h1, by simp only [Ex.eval]; omega⟩ (by simp only [Ex.eval]; omega) hA h1)
    (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_eqE {x y : Ex} (hx : Bdd V σ A x) (hy : Bdd V σ A y) (h1 : 1 ≤ V) : Bdd V σ A (eqE x y) :=
  bdd_ifLt hx hy (fun _ => bdd_lit (Nat.zero_le V))
    (fun _ => bdd_ifLt hy hx (fun _ => bdd_lit (Nat.zero_le V)) (fun _ => bdd_lit h1))






/-- `valE`: the number in an array, read by the Horner scan, is bounded (partial values never exceed the value) -/
theorem bdd_valE (k t x y : ℕ) (hxk : x ≠ k) (hyk : y ≠ k) (hxy : x ≠ y) (hA : ∀ a i, A a i ≤ 1) (h2 : 2 ≤ V)
    (hk : σ k ≤ V) (hv : numCells (A t) 1 (σ k) ≤ V) : Bdd V σ A (valE (.var k) t x y) := by
  show Bdd V σ A (.iter x y (.var k) (.lit 0) (valBody k t x y))
  simp only [Bdd, Ex.eval]
  refine ⟨hk, Nat.zero_le V, fun j hj => ?_⟩
  have key := valE_key (σ := σ) (A := A) k t x y hxk hyk hxy j hj.le
  set s := iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A (valBody k t x y)) 0 j with hs
  have hsle : s ≤ V := by
    rw [key]; exact le_trans (Nat.div_le_self _ _) hv
  have hnext : s * 2 + bt (A t) (σ k - j) ≤ V := by
    have := T_step (A t) (σ k) j hj
    rw [← key] at this
    have hvV : ECDLP.L76.V (A t) (σ k) ≤ V := hv
    have h3 : ECDLP.L76.V (A t) (σ k) / 2 ^ (σ k - (j + 1)) ≤ ECDLP.L76.V (A t) (σ k) := Nat.div_le_self _ _
    omega
  have e1 : ∀ z, z ≠ x → z ≠ y → Function.update (Function.update σ x j) y s z = σ z := by
    intro z hzx hzy; simp [Function.update_apply, hzx, hzy]
  have ex : Function.update (Function.update σ x j) y s x = j := by simp [Function.update_apply, hxy]
  have ey : Function.update (Function.update σ x j) y s y = s := by simp
  have ek : Function.update (Function.update σ x j) y s k = σ k := e1 k (Ne.symm hxk) (Ne.symm hyk)
  have hjV : j ≤ V := by omega
  have hbit : Bdd V (Function.update (Function.update σ x j) y s) A
      (nbitW (.var k) t (.sub (.sub (.var k) (.lit 1)) (.var x))) := by
    refine bdd_nbitW (w := .var k) ?_ ?_ ?_ hA (by omega)
    · simp only [Bdd, ek]; exact hk
    · simp only [Bdd, ex, ek]; exact ⟨⟨hk, (show 1 ≤ V by omega)⟩, hjV⟩
    · simp only [Ex.eval, ek]; exact hk
  have hbitv : eval (Function.update (Function.update σ x j) y s) A
      (nbitW (.var k) t (.sub (.sub (.var k) (.lit 1)) (.var x))) = bt (A t) (σ k - j) := by
    have := valE_step (σ := σ) (A := A) k t x y hxk hyk hxy j s hj
    simp only [valBody, Ex.eval] at this
    simp only [ey] at this
    omega
  simp only [valBody, Bdd]
  refine ⟨⟨?_, ?_, ?_⟩, hbit, ?_⟩
  · simp only [Bdd, ey]; exact hsle
  · exact (show 2 ≤ V from h2)
  · simp only [Ex.eval, ey]; omega
  · simp only [Ex.eval, ey, hbitv]; exact hnext


/-- numeric side conditions of the value bounds of the read expressions at a state `σ`, memory `A` -/
structure BN (V : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (n : ℕ) : Prop where
  h2 : 2 ≤ V
  hA : ∀ a i, A a i ≤ 1
  h0 : 2 * σ 0 + 2 ≤ V
  hpi : numCells (A 9) 1 (σ 0) ≤ V
  hl : numCells (A 10) 1 (σ 0) ≤ V
  hbW : numCells (A 11) 1 (σ 0) ≤ V
  hn : (n + 2) * (numCells (A 10) 1 (σ 0) + 2) ≤ V
  hq : 13 + 2 * n ≤ V

theorem eval_nbitW_le' (w : Ex) (t : ℕ) (i : Ex) : eval σ A (nbitW w t i) ≤ 1 := by
  rw [eval_nbitW]; cases (numCells (A t) 1 (eval σ A w)).testBit _ <;> simp

theorem eval_c0B_le (i : Ex) : eval σ A (c0B lay72 i) ≤ 1 := by
  unfold c0B nbit; exact eval_nbitW_le' _ _ _

theorem BN.upd {n : ℕ} (H : BN V σ A n) {x : ℕ} (hx : x ≠ 0) (v : ℕ) : BN V (Function.update σ x v) A n := by
  have e : Function.update σ x v 0 = σ 0 := Function.update_of_ne (Ne.symm hx) _ _
  exact ⟨H.h2, H.hA, by rw [e]; exact H.h0, by rw [e]; exact H.hpi, by rw [e]; exact H.hl, by rw [e]; exact H.hbW,
    by rw [e]; exact H.hn, H.hq⟩

theorem eval_ellE' : eval σ A lay72.ellE = numCells (A 10) 1 (σ 0) := by
  show eval σ A (valE (.var 0) 10 920 921) = _
  rw [eval_valE 0 10 920 921 (by norm_num) (by norm_num) (by norm_num)]

section rd
variable {n : ℕ} (H : BN V σ A n)
include H

theorem bdd_nbit (t : ℕ) {i : Ex} (hi : Bdd V σ A i) :
    Bdd V σ A (nbit lay72 t i) :=
  bdd_nbitW (by simp only [Bdd, lay72]; have := H.h0; omega) hi (by simp only [lay72, Ex.eval]; have := H.h0; omega) H.hA
    (by have := H.h2; omega)

theorem bdd_bWE : Bdd V σ A bWE := bdd_valE 0 11 920 921 (by norm_num) (by norm_num) (by norm_num) H.hA H.h2
  (by have := H.h0; omega) H.hbW

theorem bdd_ellE : Bdd V σ A lay72.ellE := bdd_valE 0 10 920 921 (by norm_num) (by norm_num) (by norm_num) H.hA H.h2
  (by have := H.h0; omega) H.hl

theorem bdd_piE : Bdd V σ A lay72.piE := bdd_valE 0 9 920 921 (by norm_num) (by norm_num) (by norm_num) H.hA H.h2
  (by have := H.h0; omega) H.hpi

theorem eval_ellE_le : eval σ A lay72.ellE ≤ V := eval_le_of_Bdd A _ σ (bdd_ellE H)

theorem bdd_c0B {i : Ex} (hi : Bdd V σ A i) (hiV : eval σ A i + 2 ≤ V) : Bdd V σ A (c0B lay72 i) := by
  refine bdd_nbit H _ ⟨hi, (show 1 ≤ V by have := H.h2; omega), ?_⟩
  simp only [Ex.eval]; omega


theorem bdd_cvBitE (c : Cst) {j : Ex} (hj : Bdd V σ A j) (hjV : eval σ A j + 2 ≤ V) : Bdd V σ A (cvBitE lay72 c j) := by
  have h1 : 1 ≤ V := by have := H.h2; omega
  have hjv : eval σ A j ≤ V := by omega
  cases c with
  | one => exact bdd_ifLt hj (bdd_lit h1) (fun _ => bdd_lit h1) (fun _ => bdd_lit (Nat.zero_le V))
  | cp => exact bdd_nbit H _ hj
  | ca => exact bdd_nbit H _ hj
  | cb => exact bdd_nbit H _ hj
  | cX => exact bdd_nbit H _ hj
  | cRx => exact bdd_nbit H _ hj
  | cRy => exact bdd_nbit H _ hj
  | cOp =>
    have hw : Bdd V σ A lay72.w2E := by
      have := H.h0
      simp only [lay72, Bdd, Ex.eval]
      refine ⟨⟨(show 2 ≤ V by omega), (show σ 0 ≤ V by omega), by omega⟩, h1, by omega⟩
    exact bdd_nbitW hw hj (by simp only [lay72, Ex.eval]; have := H.h0; omega) H.hA h1
  | cN =>
    refine bdd_ifLt hj (bdd_lit h1) (fun _ => bdd_lit h1) (fun _ => bdd_ifLt hj (bdd_lit H.h2) (fun _ => bdd_lit (Nat.zero_le V)) (fun _ => ?_))
    exact bdd_nbit H _ ⟨hj, bdd_lit H.h2⟩
  | cc0 => exact bdd_c0B H hj hjV
  | cc1 =>
    simp only [cvBitE, Bdd]
    have hc0 : Bdd V σ A (c0B lay72 j) := bdd_c0B H hj hjV
    have hprod : Bdd V σ A (.prod lay72.vb j (.lit 2) (c0B lay72 (.var lay72.vb))) := by
      refine ⟨hj, bdd_lit H.h2, fun i hi => ?_, fun i _ => ?_⟩
      · refine bdd_c0B (H.upd (show lay72.vb ≠ 0 by simp [lay72]) i) ?_ ?_
        · simp only [Bdd, lay72, Function.update_self]; omega
        · simp only [Ex.eval, lay72, Function.update_self]; omega
      · exact le_trans (ECDLP.L63.foldProd_two_le _ _) h1
    have e1 := eval_c0B_le (σ := σ) (A := A) j
    have e2 : eval σ A (.prod lay72.vb j (.lit 2) (c0B lay72 (.var lay72.vb))) ≤ 1 := by
      exact ECDLP.L63.foldProd_two_le _ _
    exact ⟨⟨hc0, hprod, by omega⟩, (bdd_lit (σ := σ) (A := A) H.h2 : Bdd V σ A (.lit 2))⟩


theorem bdd_pidx {i q : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) (hq : Bdd V σ A q)
    (hqv : eval σ A q ≤ numCells (A 10) 1 (σ 0)) :
    Bdd V σ A (pidx lay72 i q) ∧ eval σ A (pidx lay72 i q) + 2 ≤ V := by
  have hn := H.hn
  have hl := eval_ellE' (σ := σ) (A := A)
  have hb := bdd_ellE H
  set l := numCells (A 10) 1 (σ 0) with hl'
  have h1 : eval σ A i * (l + 1) ≤ n * (l + 1) := Nat.mul_le_mul_right _ hiv
  have h3 : n * (l + 1) + l + 2 ≤ (n + 2) * (l + 2) := by nlinarith
  have hsum : eval σ A i * (l + 1) + eval σ A q + 2 ≤ V := by omega
  refine ⟨?_, ?_⟩
  · refine ⟨⟨hi, ⟨hb, (show 1 ≤ V by have := H.h2; omega), by simp only [Ex.eval, hl]; omega⟩, ?_⟩, hq, ?_⟩
    · simp only [Ex.eval, hl]; omega
    · simp only [Ex.eval, hl]; omega
  · simp only [pidx, Ex.eval, hl]; omega

theorem bdd_pfBit {k : Ex} (hk : Bdd V σ A k) (hkv : eval σ A k + 2 ≤ V) : Bdd V σ A (pfBit lay72 k) :=
  bdd_bitRd ⟨hk, (show 1 ≤ V by have := H.h2; omega), by simp only [Ex.eval]; omega⟩ (by simp only [Ex.eval]; omega) H.hA
    (by have := H.h2; omega)

theorem bdd_sgE {i : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) : Bdd V σ A (sgE lay72 i) := by
  have hp := bdd_pidx H hi hiv (bdd_ellE H) (by rw [eval_ellE'])
  have h2 := H.h2
  refine bdd_ifLt hp.1 (bdd_piE H) (fun _ => ?_) (fun _ => bdd_lit (Nat.zero_le V))
  refine bdd_ifLt (bdd_lit (Nat.zero_le V)) ⟨⟨hp.1, (show 1 ≤ V by omega), by simp only [Ex.eval]; omega⟩, ?_⟩
    (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (by omega))
  exact le_trans (H.hA _ _) (by omega)

theorem bdd_xcDef {i jj : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) (hj : Bdd V σ A jj) (hjv : eval σ A jj + 2 ≤ V) :
    Bdd V σ A (xcDefE lay72 i jj) := by
  have h2 := H.h2
  have hl := eval_ellE' (σ := σ) (A := A)
  have hq : Bdd V σ A (qOf lay72 jj) := by
    refine ⟨bdd_ellE H, ⟨hj, (show 1 ≤ V by omega), by simp only [Ex.eval]; omega⟩⟩
  have hqv : eval σ A (qOf lay72 jj) ≤ numCells (A 10) 1 (σ 0) := by
    simp only [qOf, Ex.eval, hl]; omega
  have hp := bdd_pidx H hi hiv hq hqv
  refine bdd_ifLt hj (bdd_ellE H) (fun _ => ?_) (fun _ => bdd_lit (Nat.zero_le V))
  exact bdd_ifLt hp.1 (bdd_piE H) (fun _ => bdd_lit (by omega)) (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_xcBit {i jj : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) (hj : Bdd V σ A jj) (hjv : eval σ A jj + 2 ≤ V) :
    Bdd V σ A (xcBitE lay72 i jj) := by
  have h2 := H.h2
  have hl := eval_ellE' (σ := σ) (A := A)
  have hq : Bdd V σ A (qOf lay72 jj) := by
    refine ⟨bdd_ellE H, ⟨hj, (show 1 ≤ V by omega), by simp only [Ex.eval]; omega⟩⟩
  have hqv : eval σ A (qOf lay72 jj) ≤ numCells (A 10) 1 (σ 0) := by
    simp only [qOf, Ex.eval, hl]; omega
  have hp := bdd_pidx H hi hiv hq hqv
  exact bdd_pfBit H hp.1 (by omega)


theorem eqE_le' (x y : Ex) : eval σ A (eqE x y) ≤ 1 := by rw [eval_eqE]; split_ifs <;> omega

theorem bdd_tgIn {i jj nb : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) (hj : Bdd V σ A jj) (hnb : Bdd V σ A nb) :
    Bdd V σ A (tgIn i jj nb) := by
  have h2 := H.h2
  exact bdd_ifLt (bdd_sgE H hi hiv) (bdd_lit (by omega)) (fun _ =>
    bdd_ifLt hj (bdd_bWE H) (fun _ => bdd_ifLt hnb (bdd_lit (by omega)) (fun _ => bdd_lit (by omega))
      (fun _ => bdd_lit (Nat.zero_le V))) (fun _ => bdd_lit (Nat.zero_le V))) (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_xIn {i jj nb : Ex} (hi : Bdd V σ A i) (hiv : eval σ A i ≤ n) (hj : Bdd V σ A jj) (hjv : eval σ A jj + 2 ≤ V)
    (hnb : Bdd V σ A nb) : Bdd V σ A (xIn i jj nb) := by
  have h2 := H.h2
  refine ⟨bdd_eqE (bdd_xcDef H hi hiv hj hjv) (bdd_lit (by omega)) (by omega),
    bdd_eqE (bdd_xcBit H hi hiv hj hjv) hnb (by omega), ?_⟩
  have e1 := eqE_le' H (xcDefE lay72 i jj) (.lit 1)
  have e2 := eqE_le' H (xcBitE lay72 i jj) nb
  calc _ ≤ 1 * 1 := Nat.mul_le_mul e1 e2
    _ ≤ V := by omega

theorem bdd_cstIn (c : Cst) {jj nb : Ex} (hj : Bdd V σ A jj) (hjv : eval σ A jj + 2 ≤ V) (hnb : Bdd V σ A nb) :
    Bdd V σ A (cstIn c jj nb) := by
  have h2 := H.h2
  exact bdd_ifLt hj (bdd_bWE H) (fun _ => bdd_eqE (bdd_cvBitE H c hj hjv) hnb (by omega))
    (fun _ => bdd_lit (Nat.zero_le V))

theorem bdd_cstDisp {q jj nb : Ex} (hq : Bdd V σ A q) (hj : Bdd V σ A jj) (hjv : eval σ A jj + 2 ≤ V)
    (hnb : Bdd V σ A nb) : Bdd V σ A (cstDisp q jj nb) := by
  have h2 := H.hq
  have hl : ∀ k, k ≤ 10 → Bdd V σ A (.lit k) := fun k hk => bdd_lit (by omega)
  have hc := fun c => bdd_cstIn H c hj hjv hnb
  unfold cstDisp
  refine bdd_ifLt hq (hl 1 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 2 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 3 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 4 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 5 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 6 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 7 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 8 (by omega)) (fun _ => hc _) (fun _ => ?_)
  refine bdd_ifLt hq (hl 9 (by omega)) (fun _ => hc _) (fun _ => ?_)
  exact bdd_ifLt hq (hl 10 (by omega)) (fun _ => hc _) (fun _ => hc _)

/-- **value bound of the oracle** -/
theorem bdd_badE (u : ℕ) (hq : σ (u + 16) ≤ V) (hj : σ (u + 32) + 2 ≤ V) (hv : σ (u + 33) ≤ 1) :
    Bdd V σ A (badE u n) := by
  have h2 := H.hq
  have hqB : Bdd V σ A (.var (u + 16)) := hq
  have hjB : Bdd V σ A (.var (u + 32)) := by simp only [Bdd]; omega
  have hjv : eval σ A (.var (u + 32)) + 2 ≤ V := by simp only [Ex.eval]; omega
  have hnb : Bdd V σ A (.sub (.lit 1) (.var (u + 33))) := ⟨bdd_lit (by omega), by simp only [Bdd]; omega⟩
  simp only [badE]
  refine bdd_ifLt hqB (bdd_lit (by omega)) (fun _ => bdd_cstDisp H hqB hjB hjv hnb) (fun h1 => ?_)
  refine bdd_ifLt hqB (bdd_lit (by omega)) (fun h => ?_) (fun h3 => ?_)
  · simp only [Ex.eval] at h1 h
    exact bdd_tgIn H ⟨hqB, bdd_lit (by omega)⟩ (by simp only [Ex.eval]; omega) hjB hnb
  · refine bdd_ifLt hqB (bdd_lit (by omega)) (fun h => ?_) (fun _ => bdd_lit (Nat.zero_le V))
    simp only [Ex.eval] at h1 h3 h
    exact bdd_xIn H ⟨hqB, bdd_lit (by omega)⟩ (by simp only [Ex.eval]; omega) hjB hjv hnb

end rd

/-- **`bnd` for the source gates of the real network**: the weight expression `srcE u (badE u n)` of a source node is bounded by `V`. -/
theorem bdd_srcSlot {n : ℕ} (H : BN V σ A n) {u : ℕ} {h b As s code : ℕ}
    (hh : σ (u + 13) = h) (hb : σ (u + 14) = b) (hA : σ (u + 12) = As) (hs : σ (u + 17) = s)
    (hc : σ (u + 7) = code) (hsA : s < As) (hq : σ (u + 16) ≤ V)
    (hcV : code ≤ V) (hjj : h * As * b + 2 ≤ V) (hpw : 2 ^ (b * h) ≤ V) (hhV : h ≤ V) (hbV : b ≤ V) :
    Bdd V σ A (srcE u (badE u n)) := by
  refine bdd_srcE hh hb hA hs hc hsA H.h2 hcV (by omega) hpw hhV hbV ?_
  intro t ht bt hbt
  have hbpos : 1 ≤ b := by omega
  have hj : (t * As + s) * b + bt < h * As * b := by
    have : (t * As + s + 1) * b ≤ h * As * b := Nat.mul_le_mul_right _ (by nlinarith)
    nlinarith
  set σ' := env4 σ u t bt ((t * As + s) * b + bt) (code / 2 ^ (b * t + bt) % 2) with hσ'
  have H' : BN V σ' A n := by
    unfold env4 at hσ'
    rw [hσ']
    exact (((H.upd (show u + 30 ≠ 0 by omega) t).upd (show u + 31 ≠ 0 by omega) bt).upd (show u + 32 ≠ 0 by omega) _).upd
      (show u + 33 ≠ 0 by omega) _
  refine bdd_badE H' u ?_ ?_ ?_
  · simp [hσ', env4, Function.update_apply, hq]
  · simp [hσ', env4, Function.update_apply]; omega
  · simp [hσ', env4, Function.update_apply]; omega

end bddlemmas

end ECDLP.L81
