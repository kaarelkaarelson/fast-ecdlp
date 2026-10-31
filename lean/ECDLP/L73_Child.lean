import ECDLP.L73_Par

/-!
# L73 / Child: the children of fa, mid, ib gates (same identity, next kind) and the source output
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  (φ : ∀ c, ιc c → ι)

theorem child_fa {c : Fin K} {j : ιc c} {s : Fin N0.A} {qb : CG ι ιc N0.A}
    (h : CG.gt c (Gate.fa j s) ∈ paC (w := w) φ qb) : ∃ k : Fin N0.A, qb = CG.gt c (Gate.mid k) := by
  cases qb with
  | src i s' => simp [paC] at h
  | gt c' g' =>
    rcases (mem_paC_iff φ c' g' _).1 h with ⟨q, hq, hh⟩ | hh
    · have hc : c = c' := by injection hh
      subst hc
      have hq' : q = Gate.fa j s := by injection hh with _ h2; exact h2.symm
      subst hq'
      cases g' with
      | fa j' s' => exact absurd ((paG_fa c j' s' _).1 hq) id
      | mid k => exact ⟨k, rfl⟩
      | ib k => obtain ⟨k', hk⟩ := (paG_ib c k _).1 hq; cases hk
      | car k =>
        rcases (paG_car c k _).1 hq with h1 | ⟨_, h1⟩ <;> cases h1
    · cases g' with
      | fa j' s' => have := (extra_fa φ c' j' s' _).1 hh; cases this
      | mid k => exact absurd ((extra_mid φ c' k _).1 hh) id
      | ib k => exact absurd ((extra_ib φ c' k _).1 hh) id
      | car k => exact absurd ((extra_car φ c' k _).1 hh) id

theorem child_mid {c : Fin K} {k : Fin N0.A} {qb : CG ι ιc N0.A}
    (h : CG.gt c (Gate.mid k) ∈ paC (w := w) φ qb) : ∃ j : Fin N0.A, qb = CG.gt c (Gate.ib j) := by
  cases qb with
  | src i s' => simp [paC] at h
  | gt c' g' =>
    rcases (mem_paC_iff φ c' g' _).1 h with ⟨q, hq, hh⟩ | hh
    · have hc : c = c' := by injection hh
      subst hc
      have hq' : q = Gate.mid k := by injection hh with _ h2; exact h2.symm
      subst hq'
      cases g' with
      | fa j' s' => exact absurd ((paG_fa c j' s' _).1 hq) id
      | mid k' => obtain ⟨i, s, hk⟩ := (paG_mid c k' _).1 hq; cases hk
      | ib j' => exact ⟨j', rfl⟩
      | car k' =>
        rcases (paG_car c k' _).1 hq with h1 | ⟨_, h1⟩ <;> cases h1
    · cases g' with
      | fa j' s' => have := (extra_fa φ c' j' s' _).1 hh; cases this
      | mid k' => exact absurd ((extra_mid φ c' k' _).1 hh) id
      | ib k' => exact absurd ((extra_ib φ c' k' _).1 hh) id
      | car k' => exact absurd ((extra_car φ c' k' _).1 hh) id

theorem child_ib {c : Fin K} {j : Fin N0.A} {qb : CG ι ιc N0.A}
    (h : CG.gt c (Gate.ib j) ∈ paC (w := w) φ qb) : ∃ j' : Fin (N0.A * N0.A), qb = CG.gt c (Gate.car j') := by
  cases qb with
  | src i s' => simp [paC] at h
  | gt c' g' =>
    rcases (mem_paC_iff φ c' g' _).1 h with ⟨q, hq, hh⟩ | hh
    · have hc : c = c' := by injection hh
      subst hc
      have hq' : q = Gate.ib j := by injection hh with _ h2; exact h2.symm
      subst hq'
      cases g' with
      | fa j' s' => exact absurd ((paG_fa c j' s' _).1 hq) id
      | mid k' => obtain ⟨i, s, hk⟩ := (paG_mid c k' _).1 hq; cases hk
      | ib j' => obtain ⟨k', hk⟩ := (paG_ib c j' _).1 hq; cases hk
      | car k' => exact ⟨k', rfl⟩
    · cases g' with
      | fa j' s' => have := (extra_fa φ c' j' s' _).1 hh; cases this
      | mid k' => exact absurd ((extra_mid φ c' k' _).1 hh) id
      | ib k' => exact absurd ((extra_ib φ c' k' _).1 hh) id
      | car k' => exact absurd ((extra_car φ c' k' _).1 hh) id

end
end ECDLP.L73
end
