import ECDLP.L71_Prime
import ECDLP.L61_Parse

/-!
# L71 / Feed: parse the block `encodeNat p` out of `encB`, into a pristine shifted frame and a scratch copy

`encB x = block π ++ block (encodeNat p) ++ …`.  `feed S q` scans the input (array 0, length in scalar 0) with a three-phase
loop (phase 0: skip the prefix block; phase 1: copy the bits of the next block into array `q` (cells `1..`) and array `S` (cells `1..`);
phase 2: idle), then writes the length into cell `0` of both arrays and into scalar `S`.
Scalars used: `1300` (pointer), `1301` (phase), `1302` (length), `1303, 1304` (temporaries), `1305` (loop counter),
`1307` (= 2), `1308` (= 0).
-/
namespace ECDLP.L71
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability ECDLP.L61

def feedBody (S q : ℕ) : Cmd :=
  .seq (.rd 1303 0 1300 1)
    (.ifZero 1301
      (.ifZero 1303 (.seq (.setK 1301 1) (.incr 1300)) (.seq (.incr 1300) (.incr 1300)))
      (.ifLt 1301 1307
        (.ifZero 1303 (.seq (.setK 1301 2) (.incr 1300))
          (.seq (.rd 1304 0 1300 2) (.seq (.wr q 1302 1 1304) (.seq (.wr S 1302 1 1304)
            (.seq (.incr 1302) (.seq (.incr 1300) (.incr 1300)))))))
        .skip))

def feedFin (S q : ℕ) : Cmd := .seq (.wr q 1308 0 1302) (.seq (.wr S 1308 0 1302) (.copy S 1302))

def feed (S q : ℕ) : Cmd :=
  .seq (.setK 1300 0) (.seq (.setK 1301 0) (.seq (.setK 1302 0) (.seq (.setK 1307 2) (.seq (.setK 1308 0)
    (.seq (.loop 0 1305 (feedBody S q)) (feedFin S q))))))

/-- common frame of a turn -/
def TurnFrame (s r : St) (j : ℕ) : Prop :=
  r.sc 0 = s.sc 0 ∧ r.sc 1307 = s.sc 1307 ∧ r.sc 1305 = j ∧ r.sc 1308 = s.sc 1308 ∧
    (∀ y, y ≠ 1300 → y ≠ 1301 → y ≠ 1302 → y ≠ 1303 → y ≠ 1304 → y ≠ 1305 → r.sc y = s.sc y)

theorem turnA (S q : ℕ) (s : St) (j : ℕ) (p0 : s.sc 1301 = 0) (pv : s.ar 0 (s.sc 1300 + 1) = 0) :
    TurnFrame s (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 j ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1301 = 1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1300 = s.sc 1300 + 1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1302 = s.sc 1302 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar = s.ar ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 12 := by
  simp [TurnFrame, feedBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_incr,
    Function.update_apply, p0, pv]
  intro y h1 h2 h3 h4 h5 h6; simp [h1, h2, h3, h4, h5, h6]

theorem turnB (S q : ℕ) (s : St) (j : ℕ) (p0 : s.sc 1301 = 0) (pv : s.ar 0 (s.sc 1300 + 1) ≠ 0) :
    TurnFrame s (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 j ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1301 = 0 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1300 = s.sc 1300 + 2 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1302 = s.sc 1302 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar = s.ar ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 12 := by
  simp [TurnFrame, feedBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_incr,
    Function.update_apply, p0, pv]
  intro y h1 h2 h3 h4 h5 h6; simp [h1, h2, h3, h4, h5, h6]

theorem turnC (S q : ℕ) (s : St) (j : ℕ) (h7 : s.sc 1307 = 2) (p1 : s.sc 1301 = 1) (pv : s.ar 0 (s.sc 1300 + 1) = 0) :
    TurnFrame s (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 j ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1301 = 2 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1300 = s.sc 1300 + 1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1302 = s.sc 1302 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar = s.ar ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 12 := by
  simp [TurnFrame, feedBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_ifLt, Cmd.run_setK, Cmd.run_incr,
    Function.update_apply, p1, pv, h7]
  intro y h1 h2 h3 h4 h5 h6; simp [h1, h2, h3, h4, h5, h6]

theorem turnD (S q : ℕ) (hqS : q ≠ S) (s : St) (j : ℕ) (h7 : s.sc 1307 = 2) (p1 : s.sc 1301 = 1)
    (pv : s.ar 0 (s.sc 1300 + 1) ≠ 0) :
    TurnFrame s (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 j ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1301 = 1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1300 = s.sc 1300 + 2 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1302 = s.sc 1302 + 1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar S = Function.update (s.ar S) (s.sc 1302 + 1) (s.ar 0 (s.sc 1300 + 2)) ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar q = Function.update (s.ar q) (s.sc 1302 + 1) (s.ar 0 (s.sc 1300 + 2)) ∧
    (∀ a, a ≠ S → a ≠ q → (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar a = s.ar a) ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 24 := by
  simp [TurnFrame, feedBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_wr, Cmd.run_ifZero, Cmd.run_ifLt, Cmd.run_setK, Cmd.run_incr,
    Function.update_apply, p1, pv, h7, hqS, hqS.symm]
  refine ⟨fun y h1 h2 h3 h4 h5 h6 => by simp [h1, h2, h3, h4, h5, h6], fun a h1 h2 => by simp [h1, h2]⟩

theorem turnE (S q : ℕ) (s : St) (j : ℕ) (h7 : s.sc 1307 = 2) (p2 : 2 ≤ s.sc 1301) :
    TurnFrame s (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 j ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1301 = s.sc 1301 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1300 = s.sc 1300 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.sc 1302 = s.sc 1302 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).1.ar = s.ar ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 12 := by
  have hn : s.sc 1301 ≠ 0 := by omega
  have hn2 : ¬ s.sc 1301 < 2 := by omega
  simp [TurnFrame, feedBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_ifLt, Cmd.run_skip,
    Function.update_apply, hn, hn2, h7]
  intro y h1 h2 h3 h4 h5 h6; simp [h1, h2, h3, h4, h5, h6]


/-! ### The cells of `startingMemory (block π ++ block xs ++ r)` -/

theorem getD_shift (l l' : List Bool) (k : ℕ) :
    (l ++ l').getD (l.length + k) false = l'.getD k false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem cells (π xs r : List Bool) :
    let A := startingMemory (block π ++ block xs ++ r)
    (∀ j, j < π.length → A (2 * j + 1) ≠ 0) ∧ A (2 * π.length + 1) = 0 ∧
    (∀ i, i < xs.length → A (2 * π.length + 1 + 2 * i + 1) ≠ 0 ∧
        A (2 * π.length + 1 + 2 * i + 2) = ECDLP.L61.bitN (xs.getD i false)) ∧
    A (2 * π.length + 1 + 2 * xs.length + 1) = 0 := by
  intro A
  have hW : block π ++ block xs ++ r = block π ++ (block xs ++ r) := by simp
  have hu : (block π).length = 2 * π.length + 1 := block_length π
  have hS : ∀ q, A (q + 1) = ECDLP.L61.bitN ((block π ++ (block xs ++ r)).getD q false) := fun q => by
    simp only [A, hW]; exact ECDLP.L61.startingMemory_succ _ q
  refine ⟨fun j hj => ?_, ?_, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [hS, block_getD_even (block xs ++ r) π j hj]; simp [ECDLP.L61.bitN]
  · have := block_getD_end (block xs ++ r) π
    rw [hS, this]; simp [ECDLP.L61.bitN]
  · have e := getD_shift (block π) (block xs ++ r) (2 * i)
    rw [hu, block_getD_even r xs i hi] at e
    rw [hS (2 * π.length + 1 + 2 * i), e]; simp [ECDLP.L61.bitN]
  · have e := getD_shift (block π) (block xs ++ r) (2 * i + 1)
    rw [hu, block_getD_odd r xs i hi] at e
    have h2 : 2 * π.length + 1 + 2 * i + 2 = (2 * π.length + 1 + (2 * i + 1)) + 1 := by ring
    rw [h2, hS, e]
  · have e := getD_shift (block π) (block xs ++ r) (2 * xs.length)
    rw [hu, block_getD_end r xs] at e
    rw [hS (2 * π.length + 1 + 2 * xs.length), e]; simp [ECDLP.L61.bitN]


/-! ### The loop invariant -/

def ptrF (a1 a2 j : ℕ) : ℕ := if j ≤ a1 then 2 * j else if j ≤ a1 + a2 + 1 then 2 * a1 + 1 + 2 * (j - a1 - 1) else 2 * a1 + 2 * a2 + 2
def phF (a1 a2 j : ℕ) : ℕ := if j ≤ a1 then 0 else if j ≤ a1 + a2 + 1 then 1 else 2
def lenF (a1 a2 j : ℕ) : ℕ := if j ≤ a1 then 0 else if j ≤ a1 + a2 + 1 then j - a1 - 1 else a2

/-- the array `S` after `l` bits of `xs` were copied -/
def pm (xs : List Bool) (l : ℕ) : ℕ → ℕ := fun c => if c = 0 then 0 else if c ≤ l then startingMemory xs c else 0

def FInv (S q : ℕ) (π xs : List Bool) (st s0 : St) (j : ℕ) (s : St) : Prop :=
  (∀ y, y ≠ 1300 → y ≠ 1301 → y ≠ 1302 → y ≠ 1303 → y ≠ 1304 → y ≠ 1305 → s.sc y = s0.sc y) ∧
  s.sc 1300 = ptrF π.length xs.length j ∧ s.sc 1301 = phF π.length xs.length j ∧
  s.sc 1302 = lenF π.length xs.length j ∧ s.ar 0 = st.ar 0 ∧
  s.ar S = pm xs (lenF π.length xs.length j) ∧
  (∀ c, 1 ≤ c → c ≤ lenF π.length xs.length j → s.ar q c = startingMemory xs c) ∧
  (∀ a, a ≠ S → a ≠ q → s.ar a = st.ar a)

theorem pm_update (xs : List Bool) (l : ℕ) (hl : l < xs.length) :
    Function.update (pm xs l) (l + 1) (startingMemory xs (l + 1)) = pm xs (l + 1) := by
  funext c
  by_cases h0 : c = 0
  · subst h0; simp [pm, Function.update_apply]
  · by_cases h1 : c = l + 1
    · subst h1; simp [pm]
    · simp only [Function.update_apply, if_neg h1, pm, if_neg h0]
      by_cases h2 : c ≤ l
      · simp [h2, show c ≤ l + 1 by omega]
      · simp [h2, show ¬ c ≤ l + 1 by omega]

theorem feed_step (S q : ℕ) (hS : 0 < S) (hq1 : 1 ≤ q) (hqS : q ≠ S) (π xs r : List Bool) (st s0 : St)
    (hA : st.ar 0 = startingMemory (block π ++ block xs ++ r)) (h70 : s0.sc 1307 = 2)
    (j : ℕ) (s : St) (hs : FInv S q π xs st s0 j s) :
    FInv S q π xs st s0 (j + 1) (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 ∧
    (Cmd.run (feedBody S q) (s.setSc 1305 j)).2 ≤ 24 := by
  obtain ⟨hsc, h1300, h1301, h1302, har0, harS, harq, harO⟩ := hs
  obtain ⟨cA, cT, cB, cE⟩ := cells π xs r
  set a1 := π.length with ha1
  set a2 := xs.length with ha2
  have h7 : s.sc 1307 = 2 := by rw [hsc 1307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h70
  have hA' : s.ar 0 = startingMemory (block π ++ block xs ++ r) := by rw [har0, hA]
  rw [← hA'] at cA cT cB cE
  by_cases c1 : j < a1
  · -- pair of the first block
    have hp : s.sc 1300 = 2 * j := by rw [h1300]; simp only [ptrF]; split_ifs <;> omega
    have ph : s.sc 1301 = 0 := by rw [h1301]; simp only [phF]; split_ifs <;> omega
    have pv : s.ar 0 (s.sc 1300 + 1) ≠ 0 := by rw [hp]; exact cA j c1
    obtain ⟨⟨f0, f7, f5, f8, fy⟩, t1, t2, t3, t4, t5⟩ := turnB S q s j ph pv
    refine ⟨⟨fun y h1 h2 h3 h4 h5 h6 => by rw [fy y h1 h2 h3 h4 h5 h6]; exact hsc y h1 h2 h3 h4 h5 h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t5.trans (by norm_num)⟩
    · rw [t2, hp]; simp only [ptrF]; split_ifs <;> omega
    · rw [t1]; simp only [phF]; split_ifs <;> omega
    · rw [t3, h1302]; simp only [lenF]; split_ifs <;> omega
    · rw [t4, har0]
    · rw [t4, harS]; have : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
      rw [this]
    · intro c hc1 hc2; rw [t4]; have : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
      rw [this] at hc2; exact harq c hc1 hc2
    · intro a ha1' ha2'; rw [t4]; exact harO a ha1' ha2'
  by_cases c2 : j = a1
  · -- terminator of the first block
    have hp : s.sc 1300 = 2 * a1 := by rw [h1300]; simp only [ptrF]; split_ifs <;> omega
    have ph : s.sc 1301 = 0 := by rw [h1301]; simp only [phF]; split_ifs <;> omega
    have pv : s.ar 0 (s.sc 1300 + 1) = 0 := by rw [hp]; exact cT
    obtain ⟨⟨f0, f7, f5, f8, fy⟩, t1, t2, t3, t4, t5⟩ := turnA S q s j ph pv
    refine ⟨⟨fun y h1 h2 h3 h4 h5 h6 => by rw [fy y h1 h2 h3 h4 h5 h6]; exact hsc y h1 h2 h3 h4 h5 h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t5.trans (by norm_num)⟩
    · rw [t2, hp]; simp only [ptrF]; split_ifs <;> omega
    · rw [t1]; simp only [phF]; split_ifs <;> omega
    · rw [t3, h1302]; simp only [lenF]; split_ifs <;> omega
    · rw [t4, har0]
    · rw [t4, harS]; have : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
      rw [this]
    · intro c hc1 hc2; rw [t4]; have : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
      rw [this] at hc2; exact harq c hc1 hc2
    · intro a ha1' ha2'; rw [t4]; exact harO a ha1' ha2'
  by_cases c3 : j ≤ a1 + a2
  · -- a pair of the second block, i = j - a1 - 1
    have hp : s.sc 1300 = 2 * a1 + 1 + 2 * (j - a1 - 1) := by rw [h1300]; simp only [ptrF]; split_ifs <;> omega
    have ph : s.sc 1301 = 1 := by rw [h1301]; simp only [phF]; split_ifs <;> omega
    have hl : s.sc 1302 = j - a1 - 1 := by rw [h1302]; simp only [lenF]; split_ifs <;> omega
    obtain ⟨cv, cw⟩ := cB (j - a1 - 1) (by omega)
    have pv : s.ar 0 (s.sc 1300 + 1) ≠ 0 := by rw [hp]; exact cv
    have pw : s.ar 0 (s.sc 1300 + 2) = startingMemory xs (j - a1 - 1 + 1) := by
      rw [hp, cw, ECDLP.L61.startingMemory_succ]
    obtain ⟨⟨f0, f7, f5, f8, fy⟩, t1, t2, t3, tS, tq, tO, t5⟩ := turnD S q hqS s j h7 ph pv
    have hlen : lenF a1 a2 (j + 1) = j - a1 - 1 + 1 := by simp only [lenF]; split_ifs <;> omega
    have hlen0 : lenF a1 a2 j = j - a1 - 1 := by simp only [lenF]; split_ifs <;> omega
    refine ⟨⟨fun y h1 h2 h3 h4 h5 h6 => by rw [fy y h1 h2 h3 h4 h5 h6]; exact hsc y h1 h2 h3 h4 h5 h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t5⟩
    · rw [t2, hp]; simp only [ptrF]; split_ifs <;> omega
    · rw [t1]; simp only [phF]; split_ifs <;> omega
    · rw [t3, hl, hlen]
    · rw [tO 0 (by omega) (by omega), har0]
    · rw [tS, harS, hlen0, hl, pw, hlen]; exact pm_update xs _ (by omega)
    · intro c hc1 hc2
      rw [tq, hl, pw]
      by_cases hc : c = j - a1 - 1 + 1
      · subst hc; simp
      · rw [Function.update_of_ne hc]; exact harq c hc1 (by rw [hlen0]; rw [hlen] at hc2; omega)
    · intro a ha1' ha2'; rw [tO a ha1' ha2']; exact harO a ha1' ha2'
  by_cases c4 : j = a1 + a2 + 1
  · -- terminator of the second block
    have hp : s.sc 1300 = 2 * a1 + 1 + 2 * a2 := by rw [h1300]; simp only [ptrF]; split_ifs <;> omega
    have ph : s.sc 1301 = 1 := by rw [h1301]; simp only [phF]; split_ifs <;> omega
    have pv : s.ar 0 (s.sc 1300 + 1) = 0 := by rw [hp]; exact cE
    obtain ⟨⟨f0, f7, f5, f8, fy⟩, t1, t2, t3, t4, t5⟩ := turnC S q s j h7 ph pv
    have hl : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
    refine ⟨⟨fun y h1 h2 h3 h4 h5 h6 => by rw [fy y h1 h2 h3 h4 h5 h6]; exact hsc y h1 h2 h3 h4 h5 h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t5.trans (by norm_num)⟩
    · rw [t2, hp]; simp only [ptrF]; split_ifs <;> omega
    · rw [t1]; simp only [phF]; split_ifs <;> omega
    · rw [t3, h1302, hl]
    · rw [t4, har0]
    · rw [t4, harS, hl]
    · intro c hc1 hc2; rw [t4]; rw [hl] at hc2; exact harq c hc1 hc2
    · intro a ha1' ha2'; rw [t4]; exact harO a ha1' ha2'
  · -- idle
    have ph : 2 ≤ s.sc 1301 := by rw [h1301]; simp only [phF]; split_ifs <;> omega
    obtain ⟨⟨f0, f7, f5, f8, fy⟩, t1, t2, t3, t4, t5⟩ := turnE S q s j h7 ph
    have hl : lenF a1 a2 (j + 1) = lenF a1 a2 j := by simp only [lenF]; split_ifs <;> omega
    refine ⟨⟨fun y h1 h2 h3 h4 h5 h6 => by rw [fy y h1 h2 h3 h4 h5 h6]; exact hsc y h1 h2 h3 h4 h5 h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t5.trans (by norm_num)⟩
    · rw [t2, h1300]; simp only [ptrF]; split_ifs <;> omega
    · rw [t1, h1301]; simp only [phF]; split_ifs <;> omega
    · rw [t3, h1302, hl]
    · rw [t4, har0]
    · rw [t4, harS, hl]
    · intro c hc1 hc2; rw [t4]; rw [hl] at hc2; exact harq c hc1 hc2
    · intro a ha1' ha2'; rw [t4]; exact harO a ha1' ha2'


theorem sm_gt (xs : List Bool) (c : ℕ) (h : xs.length < c) : startingMemory xs c = 0 := startingMemory_gt xs h

/-- **The feed.**  From a state holding `encB`-shaped input (`block π ++ block xs ++ r`) in array 0 and a pristine `S`-frame,
`feed S q` leaves the `S`-frame equal to `St.init xs` and array `q` holding `startingMemory xs` on cells `0 … |xs|`. -/
theorem feed_run (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (π xs r : List Bool) (st : St)
    (hA : st.ar 0 = startingMemory (block π ++ block xs ++ r))
    (hL : st.sc 0 = (block π ++ block xs ++ r).length) (hpr : unshift S st = St.init []) :
    unshift S (Cmd.run (feed S q) st).1 = St.init xs ∧
    (∀ i, i ≤ xs.length → (Cmd.run (feed S q) st).1.ar q i = startingMemory xs i) ∧
    (Cmd.run (feed S q) st).1.ar 0 = st.ar 0 ∧ (Cmd.run (feed S q) st).1.sc 0 = st.sc 0 ∧
    (Cmd.run (feed S q) st).2 ≤ 25 * st.sc 0 + 40 := by
  set a1 := π.length with ha1
  set a2 := xs.length with ha2
  set s0 := (((((st.setSc 1300 0).setSc 1301 0).setSc 1302 0).setSc 1307 2).setSc 1308 0) with hs0
  have hs0sc : ∀ y, y ≠ 1300 → y ≠ 1301 → y ≠ 1302 → y ≠ 1307 → y ≠ 1308 → s0.sc y = st.sc y := by
    intro y h1 h2 h3 h4 h5; simp [hs0, Function.update_apply, h1, h2, h3, h4, h5]
  have h70 : s0.sc 1307 = 2 := by simp [hs0, Function.update_apply]
  have h80 : s0.sc 1308 = 0 := by simp [hs0]
  have hL0 : s0.sc 0 = st.sc 0 := hs0sc 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSa : st.ar S = fun _ => 0 := by
    have := congrArg (fun u => u.ar 0) hpr
    simp only [unshift_ar, St.init_ar_zero, add_zero] at this
    rw [this]; funext c; simp [startingMemory]
  have hpS : ∀ a, 0 < a → st.ar (S + a) = fun _ => 0 := fun a ha => by
    have := congrArg (fun u => u.ar a) hpr
    simp only [unshift_ar, St.init] at this
    rw [this]; simp [Nat.pos_iff_ne_zero.mp ha]
  have hpsc : ∀ i, 0 < i → st.sc (S + i) = 0 := fun i hi => by
    have := congrArg (fun u => u.sc i) hpr
    simp only [unshift_sc, St.init] at this
    rw [this]; simp [Nat.pos_iff_ne_zero.mp hi]
  have hlenL : a1 + a2 + 2 ≤ st.sc 0 := by
    rw [hL]; have := block_length π; have := block_length xs
    simp only [List.length_append]; omega
  have hI0 : FInv S q π xs st s0 0 s0 := by
    refine ⟨fun y _ _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, fun c h1 h2 => ?_, fun a _ _ => ?_⟩
    · simp [hs0, ptrF]
    · simp [hs0, phF]
    · simp [hs0, lenF]
    · simp [hs0]
    · simp only [hs0, St.setSc_ar]; rw [hSa]; funext c; by_cases hc : c = 0 <;> simp [pm, lenF, hc]
    · simp [lenF] at h2; omega
    · simp [hs0]
  have hstep : ∀ j s, j < s0.sc 0 → FInv S q π xs st s0 j s →
      FInv S q π xs st s0 (j + 1) (Cmd.run (feedBody S q) (s.setSc 1305 j)).1 := fun j s _ hs =>
    (feed_step S q (by omega) hq1 (by omega) π xs r st s0 hA h70 j s hs).1
  have hI := Cmd.loop_inv (b := 0) (c := 1305) (body := feedBody S q) (st := s0) (FInv S q π xs st s0) hI0 hstep
  have hC := Cmd.loop_cost_le (b := 0) (c := 1305) (body := feedBody S q) (st := s0) (FInv S q π xs st s0) 24 hI0 hstep
    (fun j s _ hs => (feed_step S q (by omega) hq1 (by omega) π xs r st s0 hA h70 j s hs).2)
  generalize hr : Cmd.run (.loop 0 1305 (feedBody S q)) s0 = r1 at hI hC
  rw [hL0] at hI hC
  obtain ⟨i0, i1, i2, i3, i4, iS, iq, iO⟩ := hI
  have hp3 : lenF a1 a2 (st.sc 0) = a2 := by simp only [lenF]; split_ifs <;> omega
  rw [hp3] at i3 iS iq
  have e1 : (Cmd.run (feed S q) st).1 = (Cmd.run (feedFin S q) r1.1).1 := by
    simp only [feed, Cmd.run_seq, Cmd.run_setK]
    rw [← hs0, hr]
  have e2 : (Cmd.run (feed S q) st).2 ≤ r1.2 + (Cmd.run (feedFin S q) r1.1).2 + 20 := by
    simp only [feed, Cmd.run_seq, Cmd.run_setK]
    rw [← hs0, hr]
    omega
  have f1308 : r1.1.sc 1308 = 0 := by
    rw [i0 1308 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h80
  have hT : (Cmd.run (feedFin S q) r1.1).1 = (((r1.1.setAr q 0 a2).setAr S 0 a2).setSc S a2) := by
    simp [feedFin, Cmd.run_seq, Cmd.run_wr, Cmd.run_copy, f1308, i3]
  have hTc : (Cmd.run (feedFin S q) r1.1).2 ≤ 8 := by
    simp [feedFin, Cmd.run_seq, Cmd.run_wr, Cmd.run_copy]
  rw [hT] at e1
  have hqS' : q ≠ S := by omega
  have hqS0 : S ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  set T := (((r1.1.setAr q 0 a2).setAr S 0 a2).setSc S a2) with hTdef
  have tar : ∀ a, T.ar a = if a = S then Function.update (r1.1.ar S) 0 a2 else if a = q then Function.update (r1.1.ar q) 0 a2 else r1.1.ar a := by
    intro a
    simp only [hTdef, St.setSc_ar, St.setAr_ar, Function.update_apply]
    by_cases h1 : a = S
    · subst h1; simp [Ne.symm hqS']
    · by_cases h2 : a = q
      · subst h2; simp [h1]
      · simp [h1, h2]
  have tsc : ∀ y, y ≠ S → T.sc y = r1.1.sc y := by
    intro y hy; simp [hTdef, Function.update_apply, hy]
  have tsS : T.sc S = a2 := by simp [hTdef]
  have hAS : r1.1.ar S = pm xs a2 := iS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    apply St.ext
    · funext i
      simp only [unshift_sc, St.init]
      by_cases hi : i = 0
      · subst hi; simp [tsS, ha2]
      · have hSi : S + i ≠ S := by omega
        rw [tsc (S + i) hSi, if_neg hi]
        have h1 : ∀ y, y ≠ 1300 → y ≠ 1301 → y ≠ 1302 → y ≠ 1303 → y ≠ 1304 → y ≠ 1305 → r1.1.sc y = s0.sc y := i0
        rw [h1 (S + i) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hs0sc (S + i) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hpsc i (by omega)
    · funext a
      simp only [unshift_ar, St.init]
      by_cases ha : a = 0
      · subst ha
        rw [add_zero, tar S, if_pos rfl, hAS]
        funext c
        by_cases hc : c = 0
        · subst hc; simp [startingMemory, ha2]
        · simp only [Function.update_apply, if_neg hc, pm]
          by_cases hc2 : c ≤ a2
          · simp [hc, hc2]
          · simp [hc, hc2, sm_gt xs c (by omega)]
      · rw [tar (S + a), if_neg (by omega), if_neg (by omega), iO (S + a) (by omega) (by omega)]
        rw [hpS a (by omega)]; simp [ha]
  · intro i hi
    rw [e1, tar q, if_neg hqS', if_pos rfl]
    by_cases hi0 : i = 0
    · subst hi0; simp [startingMemory, ha2]
    · rw [Function.update_of_ne hi0]; exact iq i (by omega) hi
  · rw [e1, tar 0, if_neg (by omega), if_neg (by omega), i4]
  · rw [e1, tsc 0 (by omega), i0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      hs0sc 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · omega

end ECDLP.L71
