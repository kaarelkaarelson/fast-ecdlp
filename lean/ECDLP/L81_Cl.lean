import ECDLP.L81_Src

/-!
# L81 / Cl: the bit-constraint oracle `badE` for L44's slots (`Cl I bW sg xc`) from L76's read expressions (`lay72`)

Slot numbering `eι` (hypotheses `SlotIdx`): `cst c ↦ cIdx c < 11`, `tg i ↦ 11 + i`, `v (x i) ↦ 12 + n + i`, every other slot `≥ 13 + 2n`.
`badE u n` : with the slot index in `u+16`, the bit position `jj` in `u+32` and the bit value `v` in `u+33`, it is `1` iff
`(jj, decide (v = 0)) ∈ Cl (instOf p a b xR yR m) bW (sgOf ℓ π) (xcOf ℓ π) slot`  (`eval_badE`).
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L81
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 ECDLP.L76 Cst Slot
open ECDLP.L63 (sgCode sgDec sgDec_code)

/-- equality test of two expressions -/
def eqE (x y : Ex) : Ex := .ifLt x y (.lit 0) (.ifLt y x (.lit 0) (.lit 1))

theorem eval_eqE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (x y : Ex) :
    Ex.eval σ A (eqE x y) = if Ex.eval σ A x = Ex.eval σ A y then 1 else 0 := by
  simp only [eqE, Ex.eval]
  split_ifs <;> first | rfl | omega

/-- the number `bW` as an expression (bit array 11) -/
def bWE : Ex := valE (.var 0) 11 920 921

theorem eval_bWE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) : Ex.eval σ A bWE = bW := by
  show Ex.eval σ A (valE (.var 0) 11 920 921) = _
  rw [eval_valE 0 11 920 921 (by norm_num) (by norm_num) (by norm_num)]; exact h.hbW

/-- numbering of the constants -/
def cIdx : Cst → ℕ
  | .one => 0 | .cp => 1 | .ca => 2 | .cb => 3 | .cOp => 4 | .cX => 5 | .cN => 6 | .cRx => 7 | .cRy => 8
  | .cc0 => 9 | .cc1 => 10

/-- the constants in numbering order -/
def cstOf : ℕ → Cst
  | 0 => .one | 1 => .cp | 2 => .ca | 3 => .cb | 4 => .cOp | 5 => .cX | 6 => .cN | 7 => .cRx | 8 => .cRy
  | 9 => .cc0 | _ => .cc1

theorem cstOf_cIdx (c : Cst) : cstOf (cIdx c) = c := by cases c <;> rfl

/-- `jj < bW` and the bit of the constant is the (negated) bit -/
def cstIn (c : Cst) (jj nb : Ex) : Ex := .ifLt jj bWE (eqE (cvBitE lay72 c jj) nb) (.lit 0)

/-- dispatch over the constants by slot index `q` -/
def cstDisp (q jj nb : Ex) : Ex :=
  .ifLt q (.lit 1) (cstIn .one jj nb) (.ifLt q (.lit 2) (cstIn .cp jj nb) (.ifLt q (.lit 3) (cstIn .ca jj nb)
  (.ifLt q (.lit 4) (cstIn .cb jj nb) (.ifLt q (.lit 5) (cstIn .cOp jj nb) (.ifLt q (.lit 6) (cstIn .cX jj nb)
  (.ifLt q (.lit 7) (cstIn .cN jj nb) (.ifLt q (.lit 8) (cstIn .cRx jj nb) (.ifLt q (.lit 9) (cstIn .cRy jj nb)
  (.ifLt q (.lit 10) (cstIn .cc0 jj nb) (cstIn .cc1 jj nb))))))))))

/-- sign slack pinned to `0`: `sg i = none`, `jj < bW`, bit `0` -/
def tgIn (i jj nb : Ex) : Ex :=
  .ifLt (sgE lay72 i) (.lit 1) (.ifLt jj bWE (.ifLt nb (.lit 1) (.lit 1) (.lit 0)) (.lit 0)) (.lit 0)

def xIn (i jj nb : Ex) : Ex := .mul (eqE (xcDefE lay72 i jj) (.lit 1)) (eqE (xcBitE lay72 i jj) nb)

/-- **the oracle**: `1` iff `(jj, decide (v = 0)) ∈ Cl ..` for the slot with index `u+16` -/
def badE (u n : ℕ) : Ex :=
  let q : Ex := .var (u + 16)
  let jj : Ex := .var (u + 32)
  let nb : Ex := .sub (.lit 1) (.var (u + 33))
  .ifLt q (.lit 11) (cstDisp q jj nb)
    (.ifLt q (.lit (12 + n)) (tgIn (.sub q (.lit 11)) jj nb)
      (.ifLt q (.lit (13 + 2 * n)) (xIn (.sub q (.lit (12 + n))) jj nb) (.lit 0)))

/-- the slot numbering that the oracle assumes -/
structure SlotIdx (n : ℕ) (eι : Slot n → ℕ) : Prop where
  hc : ∀ c, eι (.cst c) = cIdx c
  ht : ∀ i : Fin (n + 1), eι (.tg i) = 11 + i
  hx : ∀ i : Fin (n + 1), eι (.v (.x i)) = 12 + n + i
  hr : ∀ s, (∀ c, s ≠ .cst c) → (∀ i, s ≠ .tg i) → (∀ i, s ≠ .v (.x i)) → 13 + 2 * n ≤ eι s


section sem
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_cstDisp {u : ℕ} (c : Cst) (q jj nb : Ex) (hq : Ex.eval σ A q = cIdx c) :
    Ex.eval σ A (cstDisp q jj nb) = Ex.eval σ A (cstIn c jj nb) := by
  cases c <;> simp [cstDisp, cIdx, Ex.eval, hq] at hq ⊢

theorem toNat_nb {v : ℕ} (hv : v ≤ 1) : (decide (v = 0)).toNat = 1 - v := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hv with h | h <;> simp [h]

theorem tg_in (i jj nb : Ex) :
    Ex.eval σ A (tgIn i jj nb) = if Ex.eval σ A (sgE lay72 i) = 0 ∧ Ex.eval σ A jj < Ex.eval σ A bWE ∧
      Ex.eval σ A nb = 0 then 1 else 0 := by
  simp only [tgIn, Ex.eval]
  generalize Ex.eval σ A (sgE lay72 i) = x
  generalize Ex.eval σ A jj = y
  generalize Ex.eval σ A bWE = z
  generalize Ex.eval σ A nb = w
  by_cases h1 : x = 0 <;> by_cases h2 : y < z <;> by_cases h3 : w = 0 <;> simp [h1, h2, h3] <;> omega

theorem x_in (i jj nb : Ex) :
    Ex.eval σ A (xIn i jj nb) = if Ex.eval σ A (xcDefE lay72 i jj) = 1 ∧ Ex.eval σ A (xcBitE lay72 i jj) = Ex.eval σ A nb
      then 1 else 0 := by
  simp only [xIn, Ex.eval, eval_eqE]
  generalize Ex.eval σ A (xcDefE lay72 i jj) = x
  generalize Ex.eval σ A (xcBitE lay72 i jj) = y
  generalize Ex.eval σ A nb = w
  by_cases h1 : x = 1 <;> by_cases h2 : y = w <;> simp [h1, h2]

open Classical in
/-- **the oracle is the membership in `Cl`** (for odd `p`, `X = Bd p m`) -/
theorem eval_badE {n : ℕ} {eι : Slot n → ℕ} (hI : SlotIdx n eι) (u : ℕ)
    {p a b X xR yR m : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (hX : X = Bd p m) (hodd : p % 2 = 1)
    (i : Slot n) (jj v : ℕ) (hq : σ (u + 16) = eι i) (hj : σ (u + 32) = jj) (hv : σ (u + 33) = v) (hv1 : v ≤ 1) :
    Ex.eval σ A (badE u n) = if (jj, decide (v = 0)) ∈ Cl (instOf p a b xR yR m) bW
      (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) i then 1 else 0 := by
  have hr := reads_of_reads72 hR
  have hbW := eval_bWE hR
  have hnb : Ex.eval σ A (.sub (.lit 1) (.var (u + 33))) = 1 - v := by
    simp only [Ex.eval, hv]
  have hjE : Ex.eval σ A (.var (u + 32)) = jj := by simp [Ex.eval, hj]
  have other : ∀ s : Slot n, (∀ c, s ≠ .cst c) → (∀ i, s ≠ .tg i) → (∀ i, s ≠ .v (.x i)) → σ (u + 16) = eι s →
      Ex.eval σ A (badE u n) = if (jj, decide (v = 0)) ∈ Cl (instOf p a b xR yR m) bW
        (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) s then 1 else 0 := by
    intro s h1 h2 h3 hs
    have hge := hI.hr s h1 h2 h3
    rw [ECDLP.L63.Cl_other _ _ _ _ s ⟨h1, h2, h3⟩]
    have h4 : ¬ (σ (u + 16) < 11) := by omega
    have h5 : ¬ (σ (u + 16) < 12 + n) := by omega
    have h6 : ¬ (σ (u + 16) < 13 + 2 * n) := by omega
    simp [badE, Ex.eval, h4, h5, h6]
  cases i with
  | cst c =>
    have hq' : σ (u + 16) = cIdx c := by rw [hq, hI.hc]
    have lt : cIdx c < 11 := by cases c <;> decide
    have e1 : Ex.eval σ A (badE u n) = Ex.eval σ A (cstDisp (.var (u + 16)) (.var (u + 32))
        (.sub (.lit 1) (.var (u + 33)))) := by
      simp [badE, Ex.eval, hq', lt]
    rw [e1, eval_cstDisp (u := u) c _ _ _ (by simp [Ex.eval, hq'])]
    have hm := Cl_cst_iff (n := n) lay72 lay72_ok (m := m) (bW := bW) hr hX hodd c (.var (u + 32)) (decide (v = 0))
    rw [toNat_nb hv1] at hm
    simp only [Ex.eval, hj] at hm
    simp only [cstIn, Ex.eval, eval_eqE, hbW, hj, hnb]
    simp only [hm]
    split_ifs <;> simp_all
  | tg i =>
    have hq' : σ (u + 16) = 11 + i := by rw [hq, hI.ht]
    have hi := i.2
    have e1 : Ex.eval σ A (badE u n) = Ex.eval σ A (tgIn (.sub (.var (u + 16)) (.lit 11)) (.var (u + 32))
        (.sub (.lit 1) (.var (u + 33)))) := by
      simp [badE, Ex.eval, hq']; omega
    rw [e1, tg_in]
    have hm := Cl_tg_iff (n := n) lay72 hr (m := m) (bW := bW) i (.var (u + 32)) (decide (v = 0))
    have hs : Ex.eval σ A (sgE lay72 (.sub (.var (u + 16)) (.lit 11))) = Ex.eval σ A (sgE lay72 (.lit (i : ℕ))) := by
      rw [eval_sgE lay72 hr, eval_sgE lay72 hr]
      simp [Ex.eval, hq']
    rw [hs]
    rw [toNat_nb hv1] at hm
    simp only [Ex.eval, hj, hbW, hnb, hv] at hm ⊢
    simp only [hm]
  | v a =>
    cases a with
    | x i =>
      have hq' : σ (u + 16) = 12 + n + i := by rw [hq, hI.hx]
      have hi := i.2
      have e1 : Ex.eval σ A (badE u n) = Ex.eval σ A (xIn (.sub (.var (u + 16)) (.lit (12 + n))) (.var (u + 32))
          (.sub (.lit 1) (.var (u + 33)))) := by
        have h1 : ¬ (12 + n + (i : ℕ) < 11) := by omega
        have h2 : ¬ (12 + n + (i : ℕ) < 12 + n) := by omega
        have h3 : 12 + n + (i : ℕ) < 13 + 2 * n := by omega
        simp [badE, Ex.eval, hq', h1, h2, h3]
      rw [e1, x_in]
      have hm := xc_iff lay72 hr (.sub (.var (u + 16)) (.lit (12 + n))) (.var (u + 32)) (decide (v = 0))
      have hi' : Ex.eval σ A (.sub (.var (u + 16)) (.lit (12 + n))) = i := by simp [Ex.eval, hq']
      rw [hi'] at hm
      simp only [Ex.eval, hj] at hm
      have hmem : (jj, decide (v = 0)) ∈ Cl (instOf p a b xR yR m) bW
          (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) (.v (.x i)) ↔
          (jj, decide (v = 0)) ∈ xcOf ℓ π i := Iff.rfl
      have hm2 : (jj, decide (v = 0)) ∈ Cl (instOf p a b xR yR m) bW
          (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) (.v (.x i)) ↔
          (Ex.eval σ A (xcDefE lay72 (.sub (.var (u + 16)) (.lit (12 + n))) (.var (u + 32))) = 1 ∧
           Ex.eval σ A (xcBitE lay72 (.sub (.var (u + 16)) (.lit (12 + n))) (.var (u + 32))) =
             Ex.eval σ A (.sub (.lit 1) (.var (u + 33)))) := by
        rw [hmem, hm, hnb, toNat_nb hv1]
      exact (if_congr hm2 rfl rfl).symm
    | y i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | sx i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | sy i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | w i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | l i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | qc i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | q0 i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | q1 i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | q2 i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
    | q3 i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
  | sl a => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq
  | u i => exact other _ (fun c h => by cases h) (fun j h => by cases h) (fun j h => by cases h) hq

end sem

end ECDLP.L81
