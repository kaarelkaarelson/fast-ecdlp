import ECDLP.L76_Compute
import ECDLP.L78_Piece
import ECDLP.L76_Parse

/-!
# L78 / Frame: static write sets of the length test (so that `Keep` holds from every state)
-/
namespace ECDLP.L78
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L76

def GoodW (c : Cmd) : Prop := (∀ x ∈ Cmd.wsc c, 10 ≤ x) ∧ (∀ a ∈ Cmd.war c, 3 ≤ a)

theorem powSeq_good (k : ℕ) : GoodW (powSeq 47 48 49 41 45 46 k) := by
  induction k with
  | zero => simp [GoodW, powSeq, Cmd.wsc, Cmd.war]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun x hx => ?_, fun a ha => ?_⟩
    · simp [powSeq, powStep, mulMod, mulBody, copyA, copyBody, zeroA, zeroBody, addMod, dblMod, addC, addBody, condSub, geC, Cmd.wsc] at hx
      rcases hx with hx | hx
      · exact h1 x hx
      · omega
    · simp [powSeq, powStep, mulMod, mulBody, copyA, copyBody, zeroA, zeroBody, addMod, dblMod, addC, addBody, condSub, geC, Cmd.war] at ha
      rcases ha with ha | ha
      · exact h2 a ha
      · omega


set_option maxRecDepth 100000 in
theorem computeC_good (m : ℕ) : GoodW (computeC m) := by
  obtain ⟨h1, h2⟩ := powSeq_good (m - 1)
  refine ⟨fun x hx => ?_, fun a ha => ?_⟩
  · by_cases hm : x ∈ Cmd.wsc (powSeq 47 48 49 41 45 46 (m - 1))
    · exact h1 x hm
    · simp [computeC, powSeq, powStep, mulMod, mulBody, copyA, copyBody, zeroA, zeroBody, addMod, dblMod, addC, addBody, condSub, geC, oneA, powA, constA, setBits, setBit, rootC, rootBody, Cmd.wsc, hm] at hx
      omega
  · by_cases hm : a ∈ Cmd.war (powSeq 47 48 49 41 45 46 (m - 1))
    · exact h2 a hm
    · simp [computeC, powSeq, powStep, mulMod, mulBody, copyA, copyBody, zeroA, zeroBody, addMod, dblMod, addC, addBody, condSub, geC, oneA, powA, constA, setBits, setBit, rootC, rootBody, Cmd.war, hm] at ha
      omega


/-- writes only scalars `≥ 10` or `3`, and arrays `≥ 3` -/
def Good3 (c : Cmd) : Prop := (∀ x ∈ Cmd.wsc c, 10 ≤ x ∨ x = 3) ∧ (∀ a ∈ Cmd.war c, 3 ≤ a)

theorem addN_good (k : ℕ) : GoodW (addN k) := by
  induction k with
  | zero => simp [GoodW, addN, Cmd.wsc, Cmd.war]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun x hx => ?_, fun a ha => ?_⟩
    · by_cases hm : x ∈ Cmd.wsc (addN k)
      · exact h1 x hm
      · simp [addN, addTo, Cmd.seqs, Cmd.wsc, hm] at hx
        omega
    · simp [addN, addTo, Cmd.seqs, Cmd.war] at ha
      exact h2 a ha

theorem decrM_good (k : ℕ) : GoodW (decrM k) := by
  induction k with
  | zero => simp [GoodW, decrM, Cmd.wsc, Cmd.war]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun x hx => ?_, fun a ha => ?_⟩
    · by_cases hm : x ∈ Cmd.wsc (decrM k)
      · exact h1 x hm
      · simp [decrM, Cmd.wsc, hm] at hx
        omega
    · simp [decrM, Cmd.war] at ha
      exact h2 a ha

set_option maxRecDepth 100000 in
theorem parseAll_good : GoodW parseAll := by
  refine ⟨fun x hx => ?_, fun a ha => ?_⟩
  · simp [parseAll, zero5, blkRd, blkBody, zeroA, zeroBody, aRP, aRA, aRB, aRX, aRY, aJunk, Cmd.wsc] at hx
    omega
  · simp [parseAll, zero5, blkRd, blkBody, zeroA, zeroBody, aRP, aRA, aRB, aRX, aRY, aJunk, Cmd.war] at ha
    omega

theorem scanC_good : GoodW scanC := by
  refine ⟨fun x hx => ?_, fun a ha => ?_⟩
  · simp [scanC, scanBody, Cmd.wsc] at hx
    omega
  · simp [scanC, scanBody, Cmd.war] at ha

theorem finC_good (m : ℕ) : Good3 (finC m) := by
  obtain ⟨h1, h2⟩ := decrM_good m
  refine ⟨fun x hx => ?_, fun a ha => ?_⟩
  · simp [finC, Cmd.wsc] at hx
    rcases hx with hx | hx | hx | hx | hx
    all_goals first | omega | (have := h1 x hx; omega)
  · simp [finC, Cmd.war] at ha
    exact h2 a ha

end ECDLP.L78
