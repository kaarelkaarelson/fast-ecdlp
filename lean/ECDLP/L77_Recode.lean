import ECDLP.L77_Q
import FactoringAux.Simulate.Main
import FactoringAux.SProg.Machine
import FactoringAux.UniFinal
import ECDLP.L61_Machine

/-!
# L77 / Recode: from a source command on `encB` to a `TM2ComputableInTime` on L35's `enc` (`Option Bool` alphabet)

`tm_of_source_opt` is `L61.tm_of_source` for the input code `ECDLP.enc` (alphabet `Option Bool`, prefix last, `none` separators).
The machine is `tmRec R` for `R = Qprog ; fullP P`: phase 0 recodes the input (`|enc x| + 1` steps), `Qprog` rebuilds Rudich's input stack
`encB x` (`≤ 2|encB x| + 1` steps), then Rudich's compiled machine runs (`fullP`).
-/
namespace ECDLP.L77
open ECDLP ECDLP.L61 Turing Computability Function Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem enc_shape (p a b x y : ℕ) (π : List Bool) :
    ECDLP.enc (p, a, b, x, y, π) =
      (encodeNat p).map some ++ none :: ((encodeNat a).map some ++ none :: ((encodeNat b).map some ++ none ::
        ((encodeNat x).map some ++ none :: ((encodeNat y).map some ++ none :: π.map some)))) := by
  simp [ECDLP.enc]

theorem encB_shape (p a b x y : ℕ) (π : List Bool) :
    encB (p, a, b, x, y, π) =
      (π.flatMap fun c => [true, c]) ++ false :: (codeB (encodeNat p) ++ codeB (encodeNat a) ++ codeB (encodeNat b) ++
        codeB (encodeNat x) ++ codeB (encodeNat y)) := by
  simp [encB, block, codeB]

theorem len_enc (p a b x y : ℕ) (π : List Bool) :
    (ECDLP.enc (p, a, b, x, y, π)).length =
      ((encodeNat p).length + 1) + ((encodeNat a).length + 1) + ((encodeNat b).length + 1) + ((encodeNat x).length + 1) +
        ((encodeNat y).length + 1) + π.length := by
  rw [enc_shape]; simp; omega

theorem len_encB (p a b x y : ℕ) (π : List Bool) :
    (encB (p, a, b, x, y, π)).length =
      2 * ((encodeNat p).length + (encodeNat a).length + (encodeNat b).length + (encodeNat x).length +
        (encodeNat y).length + π.length) + 6 := by
  rw [encB_shape]; simp [codeB]; omega

theorem recode_wf (P : Program) : (SProg.seq (Qprog (Sim.nK P) (Sim.nK P + 1)) (Sim.fullP P)).WF = true := by
  have h16 : 16 ≤ Sim.nK P := by unfold Sim.nK; omega
  have hw := Sim.fullP_wf P
  simp only [SProg.WF, Qprog, transfer, Bool.and_eq_true, hw, and_true, Bool.not_eq_true']
  simp [SProg.uses]
  omega

theorem recode_stacks (P : Program) :
    (SProg.seq (Qprog (Sim.nK P) (Sim.nK P + 1)) (Sim.fullP P)).StacksBelow (Sim.nK P + 2) = true := by
  have h16 : 16 ≤ Sim.nK P := by unfold Sim.nK; omega
  have hs := stacksBelow_mono (Nat.le_add_right (Sim.nK P) 2) _ (Sim.fullP_stacks P)
  simp only [SProg.StacksBelow, Qprog, transfer, Bool.and_eq_true, hs, and_true]
  simp [SProg.StacksBelow]

def outputs_cast (tm : FinTM2) (l l' : List (tm.Γ tm.k₀)) (o o' : List (tm.Γ tm.k₁)) (T : ℕ) (hl : l' = l)
    (ho : o' = o) (h : TM2OutputsInTime tm l (some o) T) : TM2OutputsInTime tm l' (some o') T := by
  subst hl; subst ho; exact h

set_option maxHeartbeats 2000000 in
/-- **The recoding machine.**  `L61.tm_of_source` for the input code `ECDLP.enc` of L35's audit statement. -/
theorem tm_of_source_opt (s : Cmd) (out : ℕ) (f : Inst → Option (List Bool)) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (encB a)).ar out) = encOut (f a))
    (hS : ∀ a, srcCost s (encB a) ≤ S (ECDLP.enc a).length) :
    ∃ (M : TM2ComputableInTime ECDLP.enc encOut f) (Q k0 cc : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ L, M.time L = cc * (Q * ((2 * L + 1) + k0 + S L + 1) ^ 2 + (2 * L + 1) + 1) ^ 3 + 1 := by
  obtain ⟨Q, k0, hT⟩ := timeComp_wrapFn s out (fun xs => outOf ((srcOut s xs).ar out)) (srcCost s)
    (fun _ => rfl) (fun _ => le_rfl)
  set P := wrapFn s out with hP
  set a1 := Sim.nK P with ha1
  have h16 : 16 ≤ a1 := by rw [ha1]; unfold Sim.nK; omega
  set R := SProg.seq (Qprog a1 (a1 + 1)) (Sim.fullP P) with hR
  have hK : 0 < a1 + 2 := by omega
  have hwf : R.WF = true := recode_wf P
  have hst : R.StacksBelow (a1 + 2) = true := recode_stacks P
  have hl : a1 < a1 + 2 := by omega
  have hl2 : a1 + 1 < a1 + 2 := by omega
  set cc : ℕ := 2000 * (Sim.lits P + 1) + 16 with hcc
  -- the per-input run
  have key : ∀ a : Inst, ∃ N, N ≤ cc * (Q * ((2 * (ECDLP.enc a).length + 1) + k0 + S (ECDLP.enc a).length + 1) ^ 2 +
        (2 * (ECDLP.enc a).length + 1) + 1) ^ 3 + 1 ∧
      (flip Option.bind (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩).step)^[N]
        (some (initList (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩) (ECDLP.enc a))) =
      some (haltList (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩) (encOut (f a))) := by
    intro a
    obtain ⟨p, a_, b_, x, y, π⟩ := a
    set L' := (ECDLP.enc (p, a_, b_, x, y, π)).length with hL'
    have hlen := len_enc p a_ b_ x y π
    have hlenB := len_encB p a_ b_ x y π
    set xs := encB (p, a_, b_, x, y, π) with hxs
    have hexQ := (exec_Q a1 (a1 + 1) (by omega) (by omega) (by omega)
        ((codeB (encodeNat p) ++ codeB (encodeNat a_) ++ codeB (encodeNat b_) ++ codeB (encodeNat x) ++
          codeB (encodeNat y)).reverse)
        ((π.flatMap fun c => [true, c]).reverse))
    simp only [List.reverse_reverse] at hexQ
    rw [← encB_shape] at hexQ
    set s0 : Stacks := s0Of' a1 (a1 + 1) ((codeB (encodeNat p) ++ codeB (encodeNat a_) ++ codeB (encodeNat b_) ++
      codeB (encodeNat x) ++ codeB (encodeNat y)).reverse) ((π.flatMap fun c => [true, c]).reverse) with hs0
    have hexec : R.exec s0 = SProg.initStacks (encOut (f (p, a_, b_, x, y, π))) := by
      show (Sim.fullP P).exec ((Qprog a1 (a1 + 1)).exec s0) = _
      rw [hexQ.1, (Sim.fullP_spec P xs).1, (hT xs).1]
      exact congrArg _ (hout _)
    have hrun := run_all R hK hst hwf hl hl2 (by omega) (encodeNat p) (encodeNat a_) (encodeNat b_) (encodeNat x)
      (encodeNat y) π (encOut (f (p, a_, b_, x, y, π))) s0 rfl hexec
    rw [← enc_shape] at hrun
    refine ⟨_, ?_, hrun⟩
    -- cost bound
    have hcost : R.cost s0 = (Qprog a1 (a1 + 1)).cost s0 + (Sim.fullP P).cost (SProg.initStacks xs) := by
      show (Qprog a1 (a1 + 1)).cost s0 + (Sim.fullP P).cost ((Qprog a1 (a1 + 1)).exec s0) = _
      rw [hexQ.1]
    have hQc := hexQ.2
    simp only [List.length_reverse, List.length_append] at hQc
    have hfc := (Sim.fullP_spec P xs).2
    have hst2 := (hT xs).2
    have hS2 : srcCost s xs ≤ S L' := hS (p, a_, b_, x, y, π)
    set Xv := Q * ((2 * L' + 1) + k0 + S L' + 1) ^ 2 + (2 * L' + 1) + 1 with hXv
    have hn : xs.length ≤ 2 * L' + 1 := by rw [hxs, hlenB]; omega
    have hsteps : steps P xs ≤ Q * ((2 * L' + 1) + k0 + S L' + 1) ^ 2 := by
      refine le_trans hst2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
      omega
    have hbase : steps P xs + xs.length + 1 ≤ Xv := by omega
    have hfc2 : (Sim.fullP P).cost (SProg.initStacks xs) ≤ 2000 * (Sim.lits P + 1) * Xv ^ 3 :=
      le_trans hfc (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 3))
    have hX1 : 2 * L' + 2 ≤ Xv := by omega
    have hX3 : Xv ≤ Xv ^ 3 := Nat.le_self_pow (by norm_num) _
    have hlen2 : (codeB (encodeNat p) ++ codeB (encodeNat a_) ++ codeB (encodeNat b_) ++ codeB (encodeNat x) ++
        codeB (encodeNat y)).length + (π.flatMap fun c => [true, c]).length + 1 = xs.length := by
      rw [hxs, encB_shape]; simp; omega
    have e3 : cc * Xv ^ 3 = 2000 * (Sim.lits P + 1) * Xv ^ 3 + 16 * Xv ^ 3 := by rw [hcc]; ring
    generalize Xv ^ 3 = W at hX3 e3 hfc2 ⊢
    simp only [List.length_append] at hlen2
    rw [hcost]
    omega
  choose N hN hrun using key
  refine ⟨{ tm := tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩
            inputAlphabet := Equiv.refl (Option Bool)
            outputAlphabet := Equiv.refl Bool
            time := fun L => cc * (Q * ((2 * L + 1) + k0 + S L + 1) ^ 2 + (2 * L + 1) + 1) ^ 3 + 1
            outputsFun := fun a => ?_ }, Q, k0, cc, ?_, fun L => rfl⟩
  · have e1 : List.map (Equiv.refl (Option Bool)).invFun (ECDLP.enc a) = ECDLP.enc a := List.map_id _
    have e2 : List.map (Equiv.refl Bool).invFun (encOut (f a)) = encOut (f a) := List.map_id _
    have h : TM2OutputsInTime (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩) (ECDLP.enc a) (some (encOut (f a)))
        (cc * (Q * ((2 * (ECDLP.enc a).length + 1) + k0 + S (ECDLP.enc a).length + 1) ^ 2 +
          (2 * (ECDLP.enc a).length + 1) + 1) ^ 3 + 1) :=
      { steps := N a
        evals_in_steps := hrun a
        steps_le_m := hN a }
    exact outputs_cast _ _ _ _ _ _ e1 e2 h
  · intro k
    cases k with
    | none => exact inferInstanceAs (Finite (Option Bool))
    | some j => exact inferInstanceAs (Finite Bool)

end ECDLP.L77
