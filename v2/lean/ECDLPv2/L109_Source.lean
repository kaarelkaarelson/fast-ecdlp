import ECDLP.L77_Final
import ECDLPv2.L109_CountChallenge

/-!
# L109 / Source: from a source command to the counting machine (general output code)

`tm_of_source_gen` is L77 `tm_of_source_opt` with the output code `encOut` replaced by an arbitrary `eb : β → List Bool`
(the proof is the same, verbatim apart from the substitution); `opt_subexp_gen` is L77 `opt_subexp` likewise.
`countingRate_of_source` : a source command computing `encodeNat (count m x)` in array `out` within a sub-exponential source cost
gives the audited claim `ECDLP109.countingRate m`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L109
open ECDLP ECDLP.L61 ECDLP.L77 Turing Computability Function Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

set_option maxHeartbeats 2000000 in
/-- **The recoding machine.**  `L61.tm_of_source` for the input code `ECDLP.enc` of L35's audit statement. -/
theorem tm_of_source_gen {β : Type} (eb : β → List Bool) (s : Cmd) (out : ℕ) (f : Inst → β) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (encB a)).ar out) = eb (f a))
    (hS : ∀ a, srcCost s (encB a) ≤ S (ECDLP.enc a).length) :
    ∃ (M : TM2ComputableInTime ECDLP.enc eb f) (Q k0 cc : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
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
      some (haltList (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩) (eb (f a))) := by
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
    have hexec : R.exec s0 = SProg.initStacks (eb (f (p, a_, b_, x, y, π))) := by
      show (Sim.fullP P).exec ((Qprog a1 (a1 + 1)).exec s0) = _
      rw [hexQ.1, (Sim.fullP_spec P xs).1, (hT xs).1]
      exact congrArg _ (hout _)
    have hrun := run_all R hK hst hwf hl hl2 (by omega) (encodeNat p) (encodeNat a_) (encodeNat b_) (encodeNat x)
      (encodeNat y) π (eb (f (p, a_, b_, x, y, π))) s0 rfl hexec
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
    have e2 : List.map (Equiv.refl Bool).invFun (eb (f a)) = eb (f a) := List.map_id _
    have h : TM2OutputsInTime (tmRec R hK ⟨a1, hl⟩ ⟨a1 + 1, hl2⟩) (ECDLP.enc a) (some (eb (f a)))
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

theorem opt_subexp_gen {β : Type} (eb : β → List Bool) (s : Cmd) (out : ℕ) (f : Inst → β) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (encB a)).ar out) = eb (f a))
    (hS : ∀ a, srcCost s (encB a) ≤ S (ECDLP.enc a).length)
    (hSs : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, S L ≤ C * 2 ^ (L / k)) :
    ∃ M : TM2ComputableInTime ECDLP.enc eb f, (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  obtain ⟨M, Q, k0, cc, hfin, ht⟩ := tm_of_source_gen eb s out f S hout hS
  refine ⟨M, hfin, fun k hk => ?_⟩
  obtain ⟨C1, hC1⟩ := hSs (12 * k) (by omega)
  refine ⟨(cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6)), fun L => ?_⟩
  rw [ht L]
  have hpoly := time_poly_aux Q k0 cc 1 (2 * L + 1) (S L) (S L) (by
    have : 1 ≤ (2 * L + 1 + 1) := by omega
    nlinarith)
  set P := 2 ^ (L / (12 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (12 * k + 1) * P := by
    have h0 := Factoring.Aux.le_two_pow_div L (12 * k) (by omega)
    rw [← hP] at h0
    have h1 : (12 * k + 1) * P = (12 * k) * P + P := by ring
    omega
  have hv : S L + 1 ≤ (C1 + 1) * P := by
    have a := hC1 L; rw [← hP] at a
    have h1 : (C1 + 1) * P = C1 * P + P := by ring
    omega
  have h0 : (2 * L + 1 + 1) ^ 6 = 64 * (L + 1) ^ 6 := by ring
  have h1 : (L + 1) ^ 6 * (S L + 1) ^ 6 ≤ ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hu 6) (Nat.pow_le_pow_left hv 6)
  have h2 : ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 =
      ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12 := by ring
  have h3 : P ^ 12 ≤ 2 ^ (L / k) := pow12_le L k
  calc _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * ((2 * L + 1 + 1) ^ 6 * (S L + 1) ^ 6) := hpoly
    _ = (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * ((L + 1) ^ 6 * (S L + 1) ^ 6)) := by rw [h0]; ring
    _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h2 ▸ h1))
    _ ≤ (cc * (Q * (k0 + 1 + 1) ^ 2 + 1) ^ 3 + 1) * (64 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * 2 ^ (L / k))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3))
    _ = _ := by ring

/-- **Reduction.** A source command `s` that leaves `encodeNat (count m x)` in array `out` on the input code `encB x`, with a
source cost `S (|enc x|)` that is `≤ C_k 2^(L/k)` for every `k`, gives the audited claim. -/
theorem countingRate_of_source (m : ℕ) (s : Cmd) (out : ℕ) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (encB a)).ar out) = encodeNat (ECDLP109.count m a))
    (hS : ∀ a, srcCost s (encB a) ≤ S (ECDLP.enc a).length)
    (hSs : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, S L ≤ C * 2 ^ (L / k)) :
    type_of% (ECDLP109.countingRate m) :=
  opt_subexp_gen ECDLP109.encCount s out (ECDLP109.count m) S hout hS hSs

end ECDLP.L109
#print axioms ECDLP.L109.countingRate_of_source
