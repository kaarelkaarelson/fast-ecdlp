import ECDLP.L76_Lay
import ECDLP.L72_Init

/-!
# L76 / Lay2: prefix expressions, memory spec and the local checks for `Lay` (L63's `Pre`, `Mem`, `Local`, `Main`)
-/
noncomputable section
namespace ECDLP.L76
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 ECDLP.L38 Slot
open ECDLP.L63 (sgCode sgDec sgDec_code)

variable (Y : Lay) {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ}

theorem eval_pidx (i q : Ex) :
    eval σ A (pidx Y i q) = eval σ A i * (eval σ A Y.ellE + 1) + eval σ A q := rfl

theorem pf_bit {p a b X xR yR : ℕ} {π : List Bool} {ℓ : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    {k : ℕ} (hk : k < π.length) : (if A Y.aPre (k + 1) = 0 then 0 else 1) = (π[k]).toNat := by
  have := hr.hpi k hk
  cases hb : π[k]
  · rw [hb] at this; simp at this; simp [this]
  · rw [hb] at this; simp at this; simp [this]

/-- `(jj, β) ∈ xcOf ℓ π i` iff the expressions say so -/
theorem xc_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (i jj : Ex) (β : Bool) :
    (eval σ A jj, β) ∈ xcOf ℓ π (eval σ A i) ↔
      eval σ A (xcDefE Y i jj) = 1 ∧ eval σ A (xcBitE Y i jj) = β.toNat := by
  have hl := hr.hl
  have hlen := hr.hlen
  simp only [xcDefE, xcBitE, pfDef, pfBit, qOf, eval_ifLt', eval_bitRd, eval_pidx, xcOf, List.mem_filterMap,
    List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq, eval, hl, hlen]
  by_cases hj : eval σ A jj < ℓ
  · rw [if_pos hj]
    set q := ℓ - (eval σ A jj + 1) with hq
    have hq' : q < ℓ := by omega
    have hjq : ℓ - 1 - q = eval σ A jj := by omega
    constructor
    · rintro ⟨q', hq'', γ, hγ, h1, h2⟩
      have : q' = q := by omega
      subst this
      obtain ⟨hlt, hget⟩ := ECDLP.L63.getElem?_eq_some.1 hγ
      subst h2
      refine ⟨if_pos hlt, ?_⟩
      rw [pf_bit Y hr hlt, hget]
    · rintro ⟨h1, h2⟩
      have hlt : eval σ A i * (ℓ + 1) + q < π.length := by
        by_contra hc; rw [if_neg hc] at h1; omega
      rw [pf_bit Y hr hlt] at h2
      have h3 : π[eval σ A i * (ℓ + 1) + q] = β := by
        cases hx : π[eval σ A i * (ℓ + 1) + q] <;> cases β <;> simp_all
      exact ⟨q, hq', π[eval σ A i * (ℓ + 1) + q], ECDLP.L63.getElem?_eq_some.2 ⟨hlt, rfl⟩, hjq, h3⟩
  · rw [if_neg hj]
    constructor
    · rintro ⟨q', hq'', γ, -, h1, -⟩; omega
    · rintro ⟨h1, -⟩; omega

theorem eval_sgE {p a b X xR yR : ℕ} {π : List Bool} {ℓ : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (i : Ex) : eval σ A (sgE Y i) = sgCode (sgOf ℓ π (eval σ A i)) := by
  have hl := hr.hl
  have hlen := hr.hlen
  simp only [sgE, eval_ifLt', eval_pidx, sgOf, eval, hl, hlen]
  by_cases hlt : eval σ A i * (ℓ + 1) + ℓ < π.length
  · rw [if_pos hlt, List.getElem?_eq_getElem hlt]
    have := hr.hpi _ hlt
    cases hb : π[eval σ A i * (ℓ + 1) + ℓ] <;> rw [hb] at this <;> simp at this <;> simp [sgCode, this]
  · rw [if_neg hlt, List.getElem?_eq_none (by omega)]
    rfl

/-! ### local checks -/

theorem Cl_cst_iff (hY : Y.Ok) {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (hX : X = Bd p m) (hodd : p % 2 = 1) (c : Cst) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.cst c) ↔
      eval σ A j < bW ∧ eval σ A (cvBitE Y c j) = β.toNat := by
  simp only [Cl]
  rw [ECDLP.L63.mem_pinList, eval_cvBitE Y hY hr hX hodd]
  exact and_congr_right fun _ => ECDLP.L63.toNat_testBit_eq_iff.symm

theorem Cl_tg_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (i : Fin (n + 1)) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.tg i) ↔
      eval σ A (sgE Y (.lit i)) = 0 ∧ eval σ A j < bW ∧ β.toNat = 0 := by
  have h := eval_sgE Y hr (.lit (i : ℕ)) (σ := σ) (A := A)
  simp only [eval] at h
  simp only [Cl]
  cases hs : sgOf ℓ π i <;> rw [hs] at h <;> simp only [sgCode] at h <;> rw [h]
  · rw [ECDLP.L63.mem_pinList]; simp
  · simp
  · simp

theorem Cl_x_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (i : Fin (n + 1)) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.v (.x i)) ↔
      eval σ A (xcDefE Y (.lit i) j) = 1 ∧ eval σ A (xcBitE Y (.lit i) j) = β.toNat := by
  have := xc_iff Y hr (.lit (i : ℕ)) j β
  simp only [eval] at this
  exact this

theorem formF_dec {p a b X xR yR : ℕ} {π : List Bool} {ℓ : ℕ} (hr : Reads Y σ A p a b X xR yR π ℓ)
    (c : Cn n) :
    formF (fun i : Fin (n + 1) => sgDec (eval σ A (sgE Y (.lit i)))) c = formF (fun i : Fin (n + 1) => sgOf ℓ π i) c := by
  have : (fun i : Fin (n + 1) => sgDec (eval σ A (sgE Y (.lit i)))) = fun i : Fin (n + 1) => sgOf ℓ π i := by
    funext i
    rw [eval_sgE Y hr]
    simp only [eval]
    exact sgDec_code _
  rw [this]

/-! ### L72's layout `Reads72` (adopted) -/

/-- **L72's layout as a `Lay`**: arrays `0,1,2,4,5,6,7,8` = `p,a,b,xR,yR,prefix,2p²,X` (frame-relative), width `σ 0`, `2σ 0 + 1`; `|π|` and `ℓ` are the numbers
in the bit arrays 9 and 10, read by the Horner expression `valE` (binders 920, 921; bound variable 922 for `cc1`). -/
def lay72 : Lay where
  aP := 0
  aA := 1
  aB := 2
  aX := 8
  aR := 4
  aY := 5
  aPre := 6
  aOp := 7
  wE := .var 0
  w2E := .add (.mul (.lit 2) (.var 0)) (.lit 1)
  piE := valE (.var 0) 9 920 921
  ellE := valE (.var 0) 10 920 921
  vb := 922

theorem lay72_ok : lay72.Ok := by
  intro σ A i
  simp [lay72, eval, Function.update_apply]

/-- **Translation**: L72's `Reads72` gives L76's `Reads` for `lay72` -/
theorem reads_of_reads72 {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (h : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Reads lay72 σ A p a b X xR yR π ℓ where
  hp := h.hp
  ha := h.ha
  hb := h.hb
  hX := h.hX
  hxR := h.hxR
  hyR := h.hyR
  hOp := by simpa [lay72, eval] using h.hOp
  hlen := by
    show eval σ A (valE (.var 0) 9 920 921) = _
    rw [eval_valE 0 9 920 921 (by norm_num) (by norm_num) (by norm_num)]; exact h.hlen
  hl := by
    show eval σ A (valE (.var 0) 10 920 921) = _
    rw [eval_valE 0 10 920 921 (by norm_num) (by norm_num) (by norm_num)]; exact h.hl
  hpi := h.hpi

end ECDLP.L76
end
