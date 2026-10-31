import FactoringAux.Simulate.Main
import FactoringAux.SProg.Machine
import FactoringAux.UniFinal

/-!
# L61 / Machine: from a source command to a Mathlib `TM2ComputableInTime`, for any `Bool`-coded problem

Generalises `Factoring.Aux.Sim.factoringInTime_of_timeComp` (`FactoringAux/Simulate/Main.lean:156`) and
`Factoring.Aux.SProg.factoringInTime_of_sprog` (`FactoringAux/SProg/Machine.lean:218`), which are stated for
`encodeNat`/`Nat.minFac` only, to arbitrary encodings `ea : α → List Bool`, `eb : β → List Bool`.  The proof is
Rudich's: one compile (`timeComp_wrapFn`), one simulation (`fullP_spec`), the machine `tmOf (fullP P)`.
-/
namespace ECDLP.L61
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Turing Computability

theorem tm_of_source {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (s : Cmd) (out : ℕ) (S : ℕ → ℕ)
    (hout : ∀ a, outOf ((srcOut s (ea a)).ar out) = eb (f a))
    (hS : ∀ a, srcCost s (ea a) ≤ S (ea a).length) :
    ∃ (M : TM2ComputableInTime ea eb f) (Q k0 cc : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ L, M.time L = cc * (Q * (L + k0 + S L + 1) ^ 2 + L + 1) ^ 3 + 1 := by
  obtain ⟨Q, k0, hT⟩ := timeComp_wrapFn s out (fun xs => outOf ((srcOut s xs).ar out)) (srcCost s)
    (fun _ => rfl) (fun _ => le_rfl)
  set P := wrapFn s out with hP
  have hexec : ∀ a, (Sim.fullP P).exec (SProg.initStacks (ea a)) = SProg.initStacks (eb (f a)) := by
    intro a
    rw [(Sim.fullP_spec P (ea a)).1, (hT (ea a)).1]
    exact congrArg _ (hout a)
  have hbound : ∀ a, (Sim.fullP P).cost (SProg.initStacks (ea a)) + 1 ≤
      (2000 * (Sim.lits P + 1)) * (Q * ((ea a).length + k0 + S (ea a).length + 1) ^ 2 + (ea a).length + 1) ^ 3 + 1 := by
    intro a
    have h1 := (Sim.fullP_spec P (ea a)).2
    have h2 : steps P (ea a) ≤ Q * ((ea a).length + k0 + S (ea a).length + 1) ^ 2 := by
      refine le_trans (hT (ea a)).2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
      have := hS a; omega
    have h3 : (steps P (ea a) + (ea a).length + 1) ^ 3 ≤
        (Q * ((ea a).length + k0 + S (ea a).length + 1) ^ 2 + (ea a).length + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have h4 := Nat.mul_le_mul_left (2000 * (Sim.lits P + 1)) h3
    omega
  have hK : 0 < Sim.nK P := by unfold Sim.nK; omega
  let M : TM2ComputableInTime ea eb f :=
    { tm := SProg.tmOf (Sim.fullP P) (Sim.nK P) hK
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := fun L => (2000 * (Sim.lits P + 1)) * (Q * (L + k0 + S L + 1) ^ 2 + L + 1) ^ 3 + 1
      outputsFun := fun a => by
        have e1 : List.map (Equiv.refl Bool).invFun (ea a) = ea a := List.map_id _
        have e2 : List.map (Equiv.refl Bool).invFun (eb (f a)) = eb (f a) := List.map_id _
        exact cast (by rw [e1, e2]) (SProg.outputsInTime_mono
          (SProg.outputsInTime (Sim.fullP P) (Sim.nK P) hK (Sim.fullP_wf P) (Sim.fullP_stacks P) (ea a)
            (eb (f a)) (hexec a)) (hbound a)) }
  exact ⟨M, Q, k0, 2000 * (Sim.lits P + 1), fun _ => inferInstanceAs (Finite Bool), fun _ => rfl⟩

end ECDLP.L61

#print axioms ECDLP.L61.tm_of_source
