import ECDLP.L76_Ops
import ECDLP.L61_Parse
import FactoringAux.Trial.Bits

/-!
# L76 / Parse: reading the blocks of `encB` into bit arrays

`blkRd dst` reads one self-delimiting block (`true b` pairs, then `false`) starting at the bit position in scalar 760 of array 0 (length in scalar 0),
writing the bits to cells `1..` of `dst`; afterwards scalar 760 is past the block and scalar 765 holds its length.  Scratch scalars `760 .. 765`.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L61 Factoring.Aux.Trial Computability

def blkBody (dst : ℕ) : Cmd :=
  .ifZero 762
    (.seq (.rd 763 0 760 1)
      (.ifZero 763 (.seq (.setK 762 1) (.incr 760))
        (.seq (.rd 764 0 760 2) (.seq (.wr dst 765 1 764) (.seq (.incr 765) (.seq (.incr 760) (.incr 760)))))))
    .skip

def blkRd (dst : ℕ) : Cmd := .seq (.setK 762 0) (.seq (.setK 765 0) (.loop 0 761 (blkBody dst)))

/-- cells of `startingMemory (L ++ block xs ++ r)` inside the block -/
theorem blk_cells (L xs r : List Bool) :
    let A := startingMemory (L ++ (block xs ++ r))
    (∀ i, i < xs.length → A (L.length + 2 * i + 1) ≠ 0 ∧ A (L.length + 2 * i + 2) = bitN (xs.getD i false)) ∧
    A (L.length + 2 * xs.length + 1) = 0 := by
  intro A
  have hS : ∀ q, A (q + 1) = bitN ((L ++ (block xs ++ r)).getD q false) := fun q => ECDLP.L61.startingMemory_succ _ q
  have sh : ∀ k, (L ++ (block xs ++ r)).getD (L.length + k) false = (block xs ++ r).getD k false := fun k => by
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [hS, sh (2 * i), block_getD_even r xs i hi]; simp [bitN]
  · have h2 : L.length + 2 * i + 2 = (L.length + (2 * i + 1)) + 1 := by ring
    rw [h2, hS, sh (2 * i + 1), block_getD_odd r xs i hi]
  · rw [hS, sh (2 * xs.length), block_getD_end r xs]; simp [bitN]

def ptrF (p0 n j : ℕ) : ℕ := if j ≤ n then p0 + 2 * j else p0 + 2 * n + 1
def doneF (n j : ℕ) : ℕ := if j ≤ n then 0 else 1
def cntF (n j : ℕ) : ℕ := if j ≤ n then j else n
/-- the destination after `c` bits -/
def pmF (xs : List Bool) (d0 : ℕ → ℕ) (c : ℕ) : ℕ → ℕ := fun i => if 1 ≤ i ∧ i ≤ c then bitN (xs.getD (i - 1) false) else d0 i

theorem pmF_update (xs : List Bool) (d0 : ℕ → ℕ) (c : ℕ) (hc : c < xs.length) :
    Function.update (pmF xs d0 c) (c + 1) (bitN (xs.getD c false)) = pmF xs d0 (c + 1) := by
  funext i
  by_cases h : i = c + 1
  · subst h; simp [pmF]
  · simp only [Function.update_apply, if_neg h, pmF]
    by_cases h2 : 1 ≤ i ∧ i ≤ c
    · simp [h2, show i ≤ c + 1 by omega]
    · simp [h2, show ¬ (1 ≤ i ∧ i ≤ c + 1) by omega]

def BInv (dst p0 : ℕ) (xs : List Bool) (st : St) (j : ℕ) (s : St) : Prop :=
  s.sc 0 = st.sc 0 ∧ s.ar 0 = st.ar 0 ∧ s.sc 760 = ptrF p0 xs.length j ∧ s.sc 762 = doneF xs.length j ∧
  s.sc 765 = cntF xs.length j ∧ s.ar dst = pmF xs (st.ar dst) (cntF xs.length j) ∧ (∀ a, a ≠ dst → s.ar a = st.ar a) ∧
  (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → s.sc y = st.sc y)

theorem blk_turn_data (dst : ℕ) (s : St) (j : ℕ) (h762 : s.sc 762 = 0) (hc : s.ar 0 (s.sc 760 + 1) ≠ 0) :
    let r := Cmd.run (blkBody dst) (s.setSc 761 j)
    r.1.sc 760 = s.sc 760 + 2 ∧ r.1.sc 762 = 0 ∧ r.1.sc 765 = s.sc 765 + 1 ∧
    r.1.ar = Function.update s.ar dst (Function.update (s.ar dst) (s.sc 765 + 1) (s.ar 0 (s.sc 760 + 2))) ∧
    (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → r.1.sc y = s.sc y) ∧ r.2 ≤ 13 := by
  intro r
  simp [r, blkBody, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_wr, Cmd.run_incr, Cmd.run_setK, Cmd.run_skip,
    Function.update_apply, h762, hc]
  intro y hy
  split_ifs <;> first | rfl | (exfalso; omega)

theorem blk_turn_end (dst : ℕ) (s : St) (j : ℕ) (h762 : s.sc 762 = 0) (hc : s.ar 0 (s.sc 760 + 1) = 0) :
    let r := Cmd.run (blkBody dst) (s.setSc 761 j)
    r.1.sc 760 = s.sc 760 + 1 ∧ r.1.sc 762 = 1 ∧ r.1.sc 765 = s.sc 765 ∧ r.1.ar = s.ar ∧
    (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → r.1.sc y = s.sc y) ∧ r.2 ≤ 13 := by
  intro r
  simp [r, blkBody, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_rd, Cmd.run_wr, Cmd.run_incr, Cmd.run_setK, Cmd.run_skip,
    Function.update_apply, h762, hc]
  intro y hy
  split_ifs <;> first | rfl | (exfalso; omega)

theorem blk_turn_skip (dst : ℕ) (s : St) (j : ℕ) (h762 : s.sc 762 ≠ 0) :
    let r := Cmd.run (blkBody dst) (s.setSc 761 j)
    r.1.sc 760 = s.sc 760 ∧ r.1.sc 762 = s.sc 762 ∧ r.1.sc 765 = s.sc 765 ∧ r.1.ar = s.ar ∧
    (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → r.1.sc y = s.sc y) ∧ r.2 ≤ 13 := by
  intro r
  simp [r, blkBody, Cmd.run_ifZero, Cmd.run_skip, Function.update_apply, h762]
  intro y hy h
  exfalso; omega

theorem blk_step (dst : ℕ) (hd : dst ≠ 0) (L xs r : List Bool) (st : St) (hA : st.ar 0 = startingMemory (L ++ (block xs ++ r)))
    (j : ℕ) (s : St) (hs : BInv dst L.length xs st j s) :
    BInv dst L.length xs st (j + 1) (Cmd.run (blkBody dst) (s.setSc 761 j)).1 ∧
    (Cmd.run (blkBody dst) (s.setSc 761 j)).2 ≤ 13 := by
  obtain ⟨h0, hA0, hp, hdn, hc, hd', har, hsc⟩ := hs
  obtain ⟨cl, ct⟩ := blk_cells L xs r
  have hA' : s.ar 0 = startingMemory (L ++ (block xs ++ r)) := by rw [hA0, hA]
  have hn := xs.length
  rcases lt_trichotomy j xs.length with hj | hj | hj
  · -- a data pair
    have e1 : ptrF L.length xs.length j = L.length + 2 * j := by simp [ptrF, hj.le]
    have e2 : doneF xs.length j = 0 := by simp [doneF, hj.le]
    have e3 : cntF xs.length j = j := by simp [cntF, hj.le]
    have e1' : ptrF L.length xs.length (j + 1) = L.length + 2 * (j + 1) := by simp [ptrF]; omega
    have e2' : doneF xs.length (j + 1) = 0 := by simp [doneF]; omega
    have e3' : cntF xs.length (j + 1) = j + 1 := by simp [cntF]; omega
    rw [e1] at hp; rw [e2] at hdn; rw [e3] at hc hd'
    obtain ⟨c1, c2⟩ := cl j hj
    have c1' : s.ar 0 (s.sc 760 + 1) ≠ 0 := by rw [hA', hp]; exact c1
    have c2' : s.ar 0 (s.sc 760 + 2) = bitN (xs.getD j false) := by
      rw [hA', hp]; exact c2
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := blk_turn_data dst s j hdn c1'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t6⟩
    · rw [t5 0 (by omega)]; exact h0
    · rw [t4]; simp [Function.update_apply, hd.symm]; exact hA0
    · rw [t1, hp, e1']; ring
    · rw [t2, e2']
    · rw [t3, hc, e3']
    · rw [t4, e3']; simp only [Function.update_self]; rw [hd', hc, c2']
      exact pmF_update xs (st.ar dst) j hj
    · intro a ha; rw [t4]; simp [Function.update_apply, ha]; exact har a ha
    · intro y hy; rw [t5 y hy]; exact hsc y hy
  · -- the terminator
    subst hj
    have e1 : ptrF L.length xs.length xs.length = L.length + 2 * xs.length := by simp [ptrF]
    have e2 : doneF xs.length xs.length = 0 := by simp [doneF]
    have e3 : cntF xs.length xs.length = xs.length := by simp [cntF]
    have e1' : ptrF L.length xs.length (xs.length + 1) = L.length + 2 * xs.length + 1 := by simp [ptrF]
    have e2' : doneF xs.length (xs.length + 1) = 1 := by simp [doneF]
    have e3' : cntF xs.length (xs.length + 1) = xs.length := by simp [cntF]
    rw [e1] at hp; rw [e2] at hdn; rw [e3] at hc hd'
    have c1' : s.ar 0 (s.sc 760 + 1) = 0 := by rw [hA', hp]; exact ct
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := blk_turn_end dst s xs.length hdn c1'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t6⟩
    · rw [t5 0 (by omega)]; exact h0
    · rw [t4]; exact hA0
    · rw [t1, hp, e1']
    · rw [t2, e2']
    · rw [t3, hc, e3']
    · rw [t4, e3']; exact hd'
    · intro a ha; rw [t4]; exact har a ha
    · intro y hy; rw [t5 y hy]; exact hsc y hy
  · -- finished
    have e1 : ptrF L.length xs.length j = L.length + 2 * xs.length + 1 := by simp [ptrF]; omega
    have e2 : doneF xs.length j = 1 := by simp [doneF]; omega
    have e3 : cntF xs.length j = xs.length := by simp [cntF]; omega
    have e1' : ptrF L.length xs.length (j + 1) = L.length + 2 * xs.length + 1 := by simp [ptrF]; omega
    have e2' : doneF xs.length (j + 1) = 1 := by simp [doneF]; omega
    have e3' : cntF xs.length (j + 1) = xs.length := by simp [cntF]; omega
    rw [e1] at hp; rw [e2] at hdn; rw [e3] at hc hd'
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := blk_turn_skip dst s j (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t6⟩
    · rw [t5 0 (by omega)]; exact h0
    · rw [t4]; exact hA0
    · rw [t1, hp, e1']
    · rw [t2, hdn, e2']
    · rw [t3, hc, e3']
    · rw [t4, e3']; exact hd'
    · intro a ha; rw [t4]; exact har a ha
    · intro y hy; rw [t5 y hy]; exact hsc y hy

theorem blkRd_run (dst : ℕ) (hd : dst ≠ 0) (L xs r : List Bool) (st : St)
    (hA : st.ar 0 = startingMemory (L ++ (block xs ++ r))) (hN : st.sc 0 = (L ++ (block xs ++ r)).length)
    (hp : st.sc 760 = L.length) :
    let r' := Cmd.run (blkRd dst) st
    r'.1.sc 760 = L.length + 2 * xs.length + 1 ∧ r'.1.sc 765 = xs.length ∧ r'.1.sc 0 = st.sc 0 ∧ r'.1.ar 0 = st.ar 0 ∧
    r'.1.ar dst = pmF xs (st.ar dst) xs.length ∧ (∀ a, a ≠ dst → r'.1.ar a = st.ar a) ∧
    (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → r'.1.sc y = st.sc y) ∧ r'.2 ≤ 14 * st.sc 0 + 5 := by
  intro r'
  set s0 : St := (st.setSc 762 0).setSc 765 0 with hs0
  have b0 : BInv dst L.length xs st 0 s0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a _ => rfl, ?_⟩
    · simp [hs0, St.setSc, Function.update_apply]
    · rfl
    · simp [hs0, St.setSc, Function.update_apply, ptrF, hp]
    · simp [hs0, St.setSc, doneF]
    · simp [hs0, St.setSc, cntF]
    · funext i; simp [pmF, hs0, St.setSc, cntF]; intro h1 h2; exfalso; omega
    · intro y hy; simp only [not_and_or, not_le] at hy
      simp [hs0, St.setSc, Function.update_apply]
      split_ifs <;> first | rfl | (exfalso; omega)
  have hstep : ∀ j t, j < s0.sc 0 → BInv dst L.length xs st j t →
      BInv dst L.length xs st (j + 1) (Cmd.run (blkBody dst) (t.setSc 761 j)).1 :=
    fun j t _ ht => (blk_step dst hd L xs r st hA j t ht).1
  have hI := Cmd.loop_inv (b := 0) (c := 761) (body := blkBody dst) (BInv dst L.length xs st) b0 hstep
  have hC := Cmd.loop_cost_le (b := 0) (c := 761) (body := blkBody dst) (BInv dst L.length xs st) 13 b0 hstep
    (fun j t _ ht => (blk_step dst hd L xs r st hA j t ht).2)
  have hs00 : s0.sc 0 = st.sc 0 := by simp [hs0, St.setSc, Function.update_apply]
  rw [hs00] at hI hC
  obtain ⟨i0, iA, ip, id, ic, idst, iar, isc⟩ := hI
  have hlen : (L ++ (block xs ++ r)).length = L.length + (2 * xs.length + 1) + r.length := by
    simp [block_length]; ring
  have hj : xs.length < st.sc 0 := by rw [hN, hlen]; omega
  have e1 : ptrF L.length xs.length (st.sc 0) = L.length + 2 * xs.length + 1 := by simp [ptrF]; omega
  have e3 : cntF xs.length (st.sc 0) = xs.length := by simp [cntF]; omega
  have hr : r' = ((Cmd.run (.loop 0 761 (blkBody dst)) s0).1, 1 + (1 + (Cmd.run (.loop 0 761 (blkBody dst)) s0).2 + 1) + 1) := by
    simp only [r', blkRd, Cmd.run_seq, Cmd.run_setK, hs0]
  rw [hr]
  refine ⟨by rw [ip, e1], by rw [ic, e3], by rw [i0], by rw [iA], by rw [idst, e3], iar, isc, ?_⟩
  simp only
  omega

/-- value of a block written to a zeroed array -/
theorem V_pmF (xs : List Bool) (d0 : ℕ → ℕ) (W : ℕ) (hW : xs.length ≤ W) (hz : ∀ c, xs.length < c → c ≤ W → d0 c = 0) :
    V (pmF xs d0 xs.length) W = valL xs := by
  have h1 : ∀ (ys : List Bool) (f : ℕ → ℕ), (∀ i, i < ys.length → f (i + 1) = bitN (ys.getD i false)) →
      V f ys.length = valL ys := by
    intro ys
    induction ys with
    | nil => intro f _; simp [V, numCells]
    | cons b ys ih =>
      intro f hf
      rw [List.length_cons, V, numCells_succ, valL_cons]
      have e := ih (fun i => f (i + 1)) (fun i hi => by simpa [List.getD_cons_succ] using hf (i + 1) (by simp; omega))
      have e0 := hf 0 (by simp)
      have : numCells f (1 + 1) ys.length = V (fun i => f (i + 1)) ys.length := by
        unfold V numCells; refine Finset.sum_congr rfl fun j _ => ?_
        rw [show 1 + 1 + j = 1 + j + 1 by ring]
      rw [this, e]
      simp only [List.getD_cons_zero, bitN] at e0
      cases b <;> simp_all [Bool.toNat]
  have h2 : V (pmF xs d0 xs.length) xs.length = valL xs := h1 xs _ (fun i hi => by
    simp only [pmF]; rw [if_pos ⟨by omega, by omega⟩]; simp)
  have h3 : ∀ k, xs.length + k ≤ W → V (pmF xs d0 xs.length) (xs.length + k) = valL xs := by
    intro k
    induction k with
    | zero => intro _; simpa using h2
    | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, V_snoc, ih (by omega)]
      have : bt (pmF xs d0 xs.length) (xs.length + k + 1) = 0 := by
        simp only [bt, pmF]
        have hz' := hz (xs.length + k + 1) (by omega) (by omega)
        simp [if_neg (show ¬ (1 ≤ xs.length + k + 1 ∧ xs.length + k + 1 ≤ xs.length) by omega), hz']
      rw [this]; simp
  have := h3 (W - xs.length) (by omega)
  rwa [show xs.length + (W - xs.length) = W by omega] at this

/-! ### all five numbers -/

/-- raw arrays: `p, a, b, xR, yR` -/
def aRP : ℕ := 30
def aRA : ℕ := 31
def aRB : ℕ := 32
def aRX : ℕ := 33
def aRY : ℕ := 34
def aJunk : ℕ := 29

/-- registers of the parse -/
def ZPa (y : ℕ) : Prop := ZC y ∨ (760 ≤ y ∧ y ≤ 765)

theorem encB_eq (π : List Bool) (p a b x y : ℕ) :
    encB (p, a, b, x, y, π) = block π ++ (block (encodeNat p) ++ (block (encodeNat a) ++ (block (encodeNat b) ++
      (block (encodeNat x) ++ block (encodeNat y))))) := by
  simp [encB, List.append_assoc]

/-- five zeroings -/
def zero5 : Cmd := .seq (zeroA aRP) (.seq (zeroA aRA) (.seq (zeroA aRB) (.seq (zeroA aRX) (zeroA aRY))))

theorem zero5_run (st : St) (W : ℕ) (hW : st.sc 710 = W) :
    let r := Cmd.run zero5 st
    (∀ d, (d = aRP ∨ d = aRA ∨ d = aRB ∨ d = aRX ∨ d = aRY) → ∀ i, 1 ≤ i → i ≤ W → r.1.ar d i = 0) ∧
    ArK (fun c => c = aRP ∨ c = aRA ∨ c = aRB ∨ c = aRX ∨ c = aRY) st r.1 ∧ ScKeep ZC st r.1 ∧ r.2 ≤ 25 * W + 10 := by
  intro r
  obtain ⟨a1, -, a3, a4, a5⟩ := zeroA_run aRP st W hW
  have c1 := zeroA_cells aRP st W hW
  generalize hs1 : Cmd.run (zeroA aRP) st = s1 at a1 a3 a4 a5 c1
  have w1 : s1.1.sc 710 = W := by rw [a4 710 (by simp [ZC])]; exact hW
  obtain ⟨b1, -, b3, b4, b5⟩ := zeroA_run aRA s1.1 W w1
  have d1 := zeroA_cells aRA s1.1 W w1
  generalize hs2 : Cmd.run (zeroA aRA) s1.1 = s2 at b1 b3 b4 b5 d1
  have w2 : s2.1.sc 710 = W := by rw [b4 710 (by simp [ZC])]; exact w1
  obtain ⟨c1', -, c3, c4, c5⟩ := zeroA_run aRB s2.1 W w2
  have e1 := zeroA_cells aRB s2.1 W w2
  generalize hs3 : Cmd.run (zeroA aRB) s2.1 = s3 at c1' c3 c4 c5 e1
  have w3 : s3.1.sc 710 = W := by rw [c4 710 (by simp [ZC])]; exact w2
  obtain ⟨d1', -, d3, d4, d5⟩ := zeroA_run aRX s3.1 W w3
  have f1 := zeroA_cells aRX s3.1 W w3
  generalize hs4 : Cmd.run (zeroA aRX) s3.1 = s4 at d1' d3 d4 d5 f1
  have w4 : s4.1.sc 710 = W := by rw [d4 710 (by simp [ZC])]; exact w3
  obtain ⟨e1', -, e3, e4, e5⟩ := zeroA_run aRY s4.1 W w4
  have g1 := zeroA_cells aRY s4.1 W w4
  generalize hs5 : Cmd.run (zeroA aRY) s4.1 = s5 at e1' e3 e4 e5 g1
  simp only [r, zero5, Cmd.run_seq, hs1, hs2, hs3, hs4, hs5]
  refine ⟨?_, ?_, ?_, by omega⟩
  · intro d hd i h1 h2
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · rw [e3 aRP (by simp [aRP, aRY]), d3 aRP (by simp [aRP, aRX]), c3 aRP (by simp [aRP, aRB]), b3 aRP (by simp [aRP, aRA])]
      exact c1 i h1 h2
    · rw [e3 aRA (by simp [aRA, aRY]), d3 aRA (by simp [aRA, aRX]), c3 aRA (by simp [aRA, aRB])]
      exact d1 i h1 h2
    · rw [e3 aRB (by simp [aRB, aRY]), d3 aRB (by simp [aRB, aRX])]
      exact e1 i h1 h2
    · rw [e3 aRX (by simp [aRX, aRY])]
      exact f1 i h1 h2
    · exact g1 i h1 h2
  · intro c hc
    have n1 : c ≠ aRP := fun h => hc (Or.inl h)
    have n2 : c ≠ aRA := fun h => hc (Or.inr (Or.inl h))
    have n3 : c ≠ aRB := fun h => hc (Or.inr (Or.inr (Or.inl h)))
    have n4 : c ≠ aRX := fun h => hc (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have n5 : c ≠ aRY := fun h => hc (Or.inr (Or.inr (Or.inr (Or.inr h))))
    rw [e3 c n5, d3 c n4, c3 c n3, b3 c n2, a3 c n1]
  · intro y hy
    rw [e4 y hy, d4 y hy, c4 y hy, b4 y hy, a4 y hy]

def parseAll : Cmd :=
  .seq zero5 (.seq (.setK 760 0) (.seq (blkRd aJunk) (.seq (blkRd aRP) (.seq (blkRd aRA) (.seq (blkRd aRB)
      (.seq (blkRd aRX) (blkRd aRY)))))))

theorem blk_chain (dst : ℕ) (hd : dst ≠ 0) (L xs r e0 : List Bool) (he : e0 = L ++ (block xs ++ r)) (W : ℕ) (st : St)
    (hA : st.ar 0 = startingMemory e0) (hN : st.sc 0 = e0.length) (hp : st.sc 760 = L.length)
    (hz : ∀ i, 1 ≤ i → i ≤ W → st.ar dst i = 0) (hxW : xs.length ≤ W) :
    let r' := Cmd.run (blkRd dst) st
    r'.1.sc 760 = (L ++ block xs).length ∧ r'.1.ar 0 = st.ar 0 ∧ r'.1.sc 0 = st.sc 0 ∧ V (r'.1.ar dst) W = valL xs ∧
    (∀ a, a ≠ dst → r'.1.ar a = st.ar a) ∧ (∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → r'.1.sc y = st.sc y) ∧ r'.2 ≤ 14 * st.sc 0 + 5 := by
  intro r'
  subst he
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := blkRd_run dst hd L xs r st hA hN hp
  refine ⟨?_, b4, b3, ?_, b6, b7, b8⟩
  · rw [b1]; simp [block_length]; ring
  · have := V_pmF xs (st.ar dst) W hxW (fun c h1 h2 => hz c (by omega) h2)
    rw [b5]; exact this

set_option maxHeartbeats 1600000 in
theorem parseAll_run (π : List Bool) (p a b xR yR : ℕ) (st : St) (W : ℕ) (hW : st.sc 710 = W)
    (hA : st.ar 0 = startingMemory (encB (p, a, b, xR, yR, π))) (hN : st.sc 0 = (encB (p, a, b, xR, yR, π)).length)
    (hNW : (encB (p, a, b, xR, yR, π)).length ≤ W) :
    let r := Cmd.run parseAll st
    V (r.1.ar aRP) W = p ∧ V (r.1.ar aRA) W = a ∧ V (r.1.ar aRB) W = b ∧ V (r.1.ar aRX) W = xR ∧ V (r.1.ar aRY) W = yR ∧
    r.1.sc 0 = st.sc 0 ∧ r.1.sc 710 = W ∧ r.1.ar 0 = st.ar 0 ∧
    ArK (fun c => c = aJunk ∨ c = aRP ∨ c = aRA ∨ c = aRB ∨ c = aRX ∨ c = aRY) st r.1 ∧ ScKeep ZPa st r.1 ∧
    r.2 ≤ 120 * W + 100 := by
  intro r
  have hE := encB_eq π p a b xR yR
  obtain ⟨z1, z2, z3, z4⟩ := zero5_run st W hW
  generalize hs1 : Cmd.run zero5 st = s1 at z1 z2 z3 z4
  have w710 : s1.1.sc 710 = W := by rw [z3 710 (by simp [ZC])]; exact hW
  have wA : s1.1.ar 0 = st.ar 0 := z2 0 (by simp [aRP, aRA, aRB, aRX, aRY])
  have wN : s1.1.sc 0 = st.sc 0 := z3 0 (by simp [ZC])
  set s1' : St := s1.1.setSc 760 0 with hs1'
  have v0 : s1'.sc 0 = st.sc 0 := by simp [hs1', St.setSc, Function.update_apply, wN]
  have vA : s1'.ar 0 = st.ar 0 := by simp [hs1', St.setSc, wA]
  have v760 : s1'.sc 760 = 0 := by simp [hs1', St.setSc]
  -- junk block (the prefix of the instance)
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ := blkRd_run aJunk (by decide) [] π
    (block (encodeNat p) ++ (block (encodeNat a) ++ (block (encodeNat b) ++ (block (encodeNat xR) ++ block (encodeNat yR)))))
    s1' (by rw [vA, hA, hE]; simp) (by rw [v0, hN, hE]; simp) (by simpa using v760)
  generalize hs2 : Cmd.run (blkRd aJunk) s1' = s2 at j1 j2 j3 j4 j5 j6 j7 j8
  have lenE : (encB (p, a, b, xR, yR, π)).length = (block π).length + (block (encodeNat p)).length +
      (block (encodeNat a)).length + (block (encodeNat b)).length + (block (encodeNat xR)).length +
      (block (encodeNat yR)).length := by
    rw [hE]; simp; ring
  have lp : (encodeNat p).length ≤ W := by have := block_length (encodeNat p); omega
  have la : (encodeNat a).length ≤ W := by have := block_length (encodeNat a); omega
  have lb : (encodeNat b).length ≤ W := by have := block_length (encodeNat b); omega
  have lx : (encodeNat xR).length ≤ W := by have := block_length (encodeNat xR); omega
  have ly : (encodeNat yR).length ≤ W := by have := block_length (encodeNat yR); omega
  have hA2 : s2.1.ar 0 = startingMemory (encB (p, a, b, xR, yR, π)) := by rw [j4, vA, hA]
  have hN2 : s2.1.sc 0 = (encB (p, a, b, xR, yR, π)).length := by rw [j3, v0, hN]
  have hp2 : s2.1.sc 760 = (block π).length := by rw [j1]; simp [block_length]
  -- block of p
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := blk_chain aRP (by decide) (block π) (encodeNat p)
    (block (encodeNat a) ++ (block (encodeNat b) ++ (block (encodeNat xR) ++ block (encodeNat yR))))
    (encB (p, a, b, xR, yR, π)) (by rw [hE]) W s2.1 hA2 hN2 hp2
    (fun i h1 h2 => by rw [j6 aRP (by decide), show s1'.ar aRP = s1.1.ar aRP from rfl]; exact z1 aRP (Or.inl rfl) i h1 h2) lp
  generalize hs3 : Cmd.run (blkRd aRP) s2.1 = s3 at k1 k2 k3 k4 k5 k6 k7
  -- block of a
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := blk_chain aRA (by decide) (block π ++ block (encodeNat p)) (encodeNat a)
    (block (encodeNat b) ++ (block (encodeNat xR) ++ block (encodeNat yR)))
    (encB (p, a, b, xR, yR, π)) (by rw [hE]; simp [List.append_assoc]) W s3.1 (by rw [k2, hA2]) (by rw [k3, hN2]) k1
    (fun i h1 h2 => by rw [k5 aRA (by decide), j6 aRA (by decide), show s1'.ar aRA = s1.1.ar aRA from rfl]; exact z1 aRA (Or.inr (Or.inl rfl)) i h1 h2) la
  generalize hs4 : Cmd.run (blkRd aRA) s3.1 = s4 at m1 m2 m3 m4 m5 m6 m7
  -- block of b
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := blk_chain aRB (by decide) (block π ++ block (encodeNat p) ++ block (encodeNat a)) (encodeNat b)
    (block (encodeNat xR) ++ block (encodeNat yR))
    (encB (p, a, b, xR, yR, π)) (by rw [hE]; simp [List.append_assoc]) W s4.1 (by rw [m2, k2, hA2]) (by rw [m3, k3, hN2]) m1
    (fun i h1 h2 => by rw [m5 aRB (by decide), k5 aRB (by decide), j6 aRB (by decide), show s1'.ar aRB = s1.1.ar aRB from rfl]; exact z1 aRB (Or.inr (Or.inr (Or.inl rfl))) i h1 h2) lb
  generalize hs5 : Cmd.run (blkRd aRB) s4.1 = s5 at n1 n2 n3 n4 n5 n6 n7
  -- block of xR
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := blk_chain aRX (by decide) (block π ++ block (encodeNat p) ++ block (encodeNat a) ++ block (encodeNat b)) (encodeNat xR)
    (block (encodeNat yR))
    (encB (p, a, b, xR, yR, π)) (by rw [hE]; simp [List.append_assoc]) W s5.1 (by rw [n2, m2, k2, hA2]) (by rw [n3, m3, k3, hN2]) n1
    (fun i h1 h2 => by rw [n5 aRX (by decide), m5 aRX (by decide), k5 aRX (by decide), j6 aRX (by decide), show s1'.ar aRX = s1.1.ar aRX from rfl]; exact z1 aRX (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) i h1 h2) lx
  generalize hs6 : Cmd.run (blkRd aRX) s5.1 = s6 at o1 o2 o3 o4 o5 o6 o7
  -- block of yR
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := blk_chain aRY (by decide) (block π ++ block (encodeNat p) ++ block (encodeNat a) ++ block (encodeNat b) ++ block (encodeNat xR)) (encodeNat yR)
    []
    (encB (p, a, b, xR, yR, π)) (by rw [hE]; simp [List.append_assoc]) W s6.1 (by rw [o2, n2, m2, k2, hA2]) (by rw [o3, n3, m3, k3, hN2]) o1
    (fun i h1 h2 => by rw [o5 aRY (by decide), n5 aRY (by decide), m5 aRY (by decide), k5 aRY (by decide), j6 aRY (by decide), show s1'.ar aRY = s1.1.ar aRY from rfl]; exact z1 aRY (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) i h1 h2) ly
  generalize hs7 : Cmd.run (blkRd aRY) s6.1 = s7 at q1 q2 q3 q4 q5 q6 q7
  have hc0 : st.sc 0 ≤ W := by rw [hN]; exact hNW
  have cs2 : s2.2 ≤ 14 * W + 5 := by have := j8; rw [v0] at this; omega
  have cs3 : s3.2 ≤ 14 * W + 5 := by have := k7; rw [j3, v0] at this; omega
  have cs4 : s4.2 ≤ 14 * W + 5 := by have := m7; rw [k3, j3, v0] at this; omega
  have cs5 : s5.2 ≤ 14 * W + 5 := by have := n7; rw [m3, k3, j3, v0] at this; omega
  have cs6 : s6.2 ≤ 14 * W + 5 := by have := o7; rw [n3, m3, k3, j3, v0] at this; omega
  have cs7 : s7.2 ≤ 14 * W + 5 := by have := q7; rw [o3, n3, m3, k3, j3, v0] at this; omega
  have d1 : ∀ c, c ≠ aJunk → c ≠ aRP → c ≠ aRA → c ≠ aRB → c ≠ aRX → c ≠ aRY → s7.1.ar c = s1.1.ar c := by
    intro c h0 h1 h2 h3 h4 h5
    rw [q5 c h5, o5 c h4, n5 c h3, m5 c h2, k5 c h1, j6 c h0]; rfl
  have d2 : ∀ y, ¬ (760 ≤ y ∧ y ≤ 765) → s7.1.sc y = s1'.sc y := by
    intro y hy
    rw [q6 y hy, o6 y hy, n6 y hy, m6 y hy, k6 y hy, j7 y hy]
  simp only [r, parseAll, Cmd.run_seq, Cmd.run_setK, hs1]
  rw [← hs1', hs2, hs3, hs4, hs5, hs6, hs7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q5 aRP (by decide), o5 aRP (by decide), n5 aRP (by decide), m5 aRP (by decide), ← valL_encodeNat p]; exact k4
  · rw [q5 aRA (by decide), o5 aRA (by decide), n5 aRA (by decide), ← valL_encodeNat a]; exact m4
  · rw [q5 aRB (by decide), o5 aRB (by decide), ← valL_encodeNat b]; exact n4
  · rw [q5 aRX (by decide), ← valL_encodeNat xR]; exact o4
  · rw [← valL_encodeNat yR]; exact q4
  · rw [q3, o3, n3, m3, k3, j3, v0]
  · rw [d2 710 (by omega), hs1']; simp only [St.setSc_sc]
    rw [Function.update_of_ne (by norm_num)]; rw [z3 710 (by simp [ZC])]; exact hW
  · rw [q2, o2, n2, m2, k2, j4, vA]
  · intro c hc
    have n0 : c ≠ aJunk := fun h => hc (Or.inl h)
    have n1 : c ≠ aRP := fun h => hc (Or.inr (Or.inl h))
    have n2' : c ≠ aRA := fun h => hc (Or.inr (Or.inr (Or.inl h)))
    have n3' : c ≠ aRB := fun h => hc (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have n4' : c ≠ aRX := fun h => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have n5' : c ≠ aRY := fun h => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    rw [d1 c n0 n1 n2' n3' n4' n5']
    exact z2 c (fun h => by rcases h with h | h | h | h | h; exact n1 h; exact n2' h; exact n3' h; exact n4' h; exact n5' h)
  · intro y hy
    have h1 : ¬ ZC y := fun h => hy (Or.inl h)
    have h2 : ¬ (760 ≤ y ∧ y ≤ 765) := fun h => hy (Or.inr h)
    rw [d2 y h2, hs1']
    simp only [St.setSc_sc]
    rw [Function.update_of_ne (by omega)]
    exact z3 y h1
  · omega

end ECDLP.L76
