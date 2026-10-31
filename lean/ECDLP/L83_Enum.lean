import ECDLP.L81_Idx
import ECDLP.L63_Slots

/-!
# L83 / Enum: explicit arithmetic enumerations `Cn n ~ Fin (18n+12)` and `Slot n ~ Fin (24n+23)`

`varIdx : Var n -> N` (a bijection onto `[0, 11n+5)`), `cnNum : Cn n -> N`, `slotNum : Slot n -> N`; the equivalences are built from
injectivity and the cardinalities of L63.  `slotNum` satisfies L81's `SlotIdx` (constants `0..10`, sign slacks `11+i`, `x` variables `12+n+i`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L83
open Finset ECDLP.L44 ECDLP.L54 ECDLP.L81 Slot Cst

variable {n : ℕ}

/-- index of a variable in `[0, 11 n + 5)` -/
def varIdx : Var n → ℕ
  | .x i => i
  | .y i => (n + 1) + i
  | .sx i => 2 * (n + 1) + i
  | .sy i => 3 * (n + 1) + i
  | .qc i => 4 * (n + 1) + i
  | .w k => 5 * (n + 1) + k
  | .l k => 5 * (n + 1) + n + k
  | .q0 k => 5 * (n + 1) + 2 * n + k
  | .q1 k => 5 * (n + 1) + 3 * n + k
  | .q2 k => 5 * (n + 1) + 4 * n + k
  | .q3 k => 5 * (n + 1) + 5 * n + k

theorem varIdx_lt (a : Var n) : varIdx a < 11 * n + 5 := by
  cases a <;> simp only [varIdx] <;> omega

theorem varIdx_inj : Function.Injective (varIdx (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [varIdx] at h <;> first | (exfalso; omega) | (congr 1; ext; omega)

/-- number of a variable slot -/
def vNum : Var n → ℕ
  | .x i => 12 + n + i
  | .y i => (13 + 2 * n) + i
  | .sx i => (13 + 2 * n) + (n + 1) + i
  | .sy i => (13 + 2 * n) + 2 * (n + 1) + i
  | .qc i => (13 + 2 * n) + 3 * (n + 1) + i
  | .w k => (13 + 2 * n) + 4 * (n + 1) + k
  | .l k => (13 + 2 * n) + 5 * n + 4 + k
  | .q0 k => (13 + 2 * n) + 6 * n + 4 + k
  | .q1 k => (13 + 2 * n) + 7 * n + 4 + k
  | .q2 k => (13 + 2 * n) + 8 * n + 4 + k
  | .q3 k => (13 + 2 * n) + 9 * n + 4 + k

/-- number of a slot: constants `0..10`, `tg i = 11 + i`, `x i = 12 + n + i`, then the other variables, the range slacks, the squares -/
def slotNum : Slot n → ℕ
  | .cst c => cIdx c
  | .tg i => 11 + i
  | .v a => vNum a
  | .sl a => (13 + 2 * n) + 10 * n + 4 + varIdx a
  | .u i => (13 + 2 * n) + 21 * n + 9 + i

theorem vNum_ge (a : Var n) : 12 + n ≤ vNum a := by
  cases a <;> simp only [vNum] <;> omega

theorem vNum_lt (a : Var n) : vNum a < (13 + 2 * n) + 10 * n + 4 := by
  cases a <;> simp only [vNum] <;> omega

theorem vNum_inj : Function.Injective (vNum (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [vNum] at h <;> first | (exfalso; omega) | (simp [Fin.ext_iff]; omega)

theorem slotNum_lt (s : Slot n) : slotNum s < 24 * n + 23 := by
  cases s with
  | cst c => have := cIdx_lt c; simp only [slotNum]; omega
  | tg i => have := i.2; simp only [slotNum]; omega
  | u i => have := i.2; simp only [slotNum]; omega
  | sl a => simp only [slotNum]; have := varIdx_lt a; omega
  | v a => simp only [slotNum]; have := vNum_lt a; omega

theorem slotNum_inj : Function.Injective (slotNum (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [slotNum] at h
  all_goals first
    | (exfalso; omega)
    | (exfalso; rename_i x y; first
        | (have := vNum_ge x; have := cIdx_lt y; omega) | (have := vNum_ge y; have := cIdx_lt x; omega)
        | (have := vNum_ge x; omega) | (have := vNum_ge y; omega)
        | (have := varIdx_lt x; omega) | (have := varIdx_lt y; omega)
        | (have := cIdx_lt x; omega) | (have := cIdx_lt y; omega)
        | (have := vNum_lt x; omega) | (have := vNum_lt y; omega))
    | (exfalso; rename_i x; have := cIdx_lt x; omega)
    | (rename_i c d; have := cIdx_inj h; subst this; rfl)
    | (rename_i i j; congr 1; ext; omega)
    | (rename_i a b; have := vNum_inj h; subst this; rfl)
    | (rename_i a b; have := varIdx_inj (by omega : varIdx a = varIdx b); subst this; rfl)

/-- the explicit slot enumeration -/
def slotEquiv (n : ℕ) : Slot n ≃ Fin (24 * n + 23) :=
  Equiv.ofBijective (fun s => ⟨slotNum s, slotNum_lt s⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => slotNum_inj (congrArg Fin.val h), ?_⟩
    simp [ECDLP.L63.card_Slot])

@[simp] theorem slotEquiv_val (s : Slot n) : (slotEquiv n s : ℕ) = slotNum s := rfl

theorem slotIdx_slotEquiv (n : ℕ) : SlotIdx n (fun i => (slotEquiv n i : ℕ)) where
  hc c := rfl
  ht i := rfl
  hx i := rfl
  hr s h1 h2 h3 := by
    simp only [slotEquiv_val]
    cases s with
    | cst c => exact absurd rfl (h1 c)
    | tg i => exact absurd rfl (h2 i)
    | u i => simp only [slotNum]; omega
    | sl a => simp only [slotNum]; omega
    | v a => cases a with
      | x i => exact absurd rfl (h3 i)
      | _ => simp only [slotNum, vNum]; omega

/-! ### identities -/

/-- number of an identity: `rng` (by `varIdx`), `uEq`, `curve`, `s0x, s0y, sRx, sRy`, `e0..e3`, `sign` -/
def cnNum : Cn n → ℕ
  | .rng a => varIdx a
  | .uEq i => 11 * n + 5 + i
  | .curve i => 12 * n + 6 + i
  | .s0x => 13 * n + 7
  | .s0y => 13 * n + 8
  | .sRx => 13 * n + 9
  | .sRy => 13 * n + 10
  | .e0 k => 13 * n + 11 + k
  | .e1 k => 14 * n + 11 + k
  | .e2 k => 15 * n + 11 + k
  | .e3 k => 16 * n + 11 + k
  | .sign i => 17 * n + 11 + i

theorem cnNum_lt (c : Cn n) : cnNum c < 18 * n + 12 := by
  cases c <;> simp only [cnNum] <;> first | omega | (have := varIdx_lt ‹Var n›; omega)

theorem cnNum_inj : Function.Injective (cnNum (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [cnNum] at h
  all_goals first
    | (exfalso; omega)
    | (exfalso; rename_i x; have := varIdx_lt x; omega)
    | (exfalso; rename_i x y; first | (have := varIdx_lt x; omega) | (have := varIdx_lt y; omega))
    | (rename_i a b; have := varIdx_inj h; subst this; rfl)
    | rfl
    | (simp [Fin.ext_iff]; omega)

/-- the explicit enumeration of the identities -/
def cnEquiv (n : ℕ) : Cn n ≃ Fin (18 * n + 12) :=
  Equiv.ofBijective (fun c => ⟨cnNum c, cnNum_lt c⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => cnNum_inj (congrArg Fin.val h), ?_⟩
    simp [ECDLP.L63.card_Cn])

@[simp] theorem cnEquiv_val (c : Cn n) : (cnEquiv n c : ℕ) = cnNum c := rfl

end ECDLP.L83
end
