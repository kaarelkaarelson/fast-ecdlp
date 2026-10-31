import ECDLP.L63_Pre

/-!
# L63 / Local: the local checks of the network (`Cl`, the forms) computed by the expressions

For `I = instOf p a b xR yR n`, `sg = sgOf ℓ π`, `xc = xcOf ℓ π`:
* `Cl_cst_iff`: pinned-constant constraints = `cvBitE`;
* `Cl_tg_iff`: the sign slack is pinned to `0` iff `sgE i = 0`;
* `Cl_x_iff`: the `x`-bit constraints = `xcDefE/xcBitE`;
* `Cl_other`: all other slots have no bit constraint;
* `formF_dec`: the identity forms `formF sg c` are those of `sg := decode (eval sgE)`.
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 ECDLP.L38 Slot

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {n : ℕ}

theorem mem_pinList {bW c jj : ℕ} {β : Bool} : (jj, β) ∈ pinList bW c ↔ jj < bW ∧ c.testBit jj = β := by
  simp [pinList]

theorem Cl_cst_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (hX : X = Bd p m) (hodd : p % 2 = 1) (c : Cst) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.cst c) ↔
      eval σ A j < bW ∧ eval σ A (cvBitE c j) = β.toNat := by
  simp only [Cl]
  rw [mem_pinList, eval_cvBitE hr hX hodd]
  exact and_congr_right fun _ => toNat_testBit_eq_iff.symm

theorem Cl_tg_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (i : Fin (n + 1)) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.tg i) ↔
      eval σ A (sgE (.lit i)) = 0 ∧ eval σ A j < bW ∧ β.toNat = 0 := by
  have h := eval_sgE hr (.lit (i : ℕ)) (σ := σ) (A := A)
  simp only [eval] at h
  simp only [Cl]
  cases hs : sgOf ℓ π i <;> rw [hs] at h <;> simp only [sgCode] at h <;> rw [h]
  · rw [mem_pinList]; simp
  · simp
  · simp

theorem Cl_x_iff {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW m : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (i : Fin (n + 1)) (j : Ex) (β : Bool) :
    (eval σ A j, β) ∈ Cl (instOf p a b xR yR m) bW (fun i : Fin (n + 1) => sgOf ℓ π i)
        (fun i : Fin (n + 1) => xcOf ℓ π i) (.v (.x i)) ↔
      eval σ A (xcDefE (.lit i) j) = 1 ∧ eval σ A (xcBitE (.lit i) j) = β.toNat := by
  have := xc_iff hr (.lit (i : ℕ)) j β
  simp only [eval] at this
  exact this

theorem Cl_other (I : ECDLP.L44.Inst) (bW : ℕ) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool)) (s : Slot n)
    (h : (∀ c, s ≠ .cst c) ∧ (∀ i, s ≠ .tg i) ∧ (∀ i, s ≠ .v (.x i))) : Cl I bW sg xc s = [] := by
  cases s with
  | cst c => exact absurd rfl (h.1 c)
  | tg i => exact absurd rfl (h.2.1 i)
  | v a => cases a with
    | x i => exact absurd rfl (h.2.2 i)
    | _ => rfl
  | _ => rfl

theorem formF_dec {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (hr : Reads σ A p a b X xR yR π ℓ bW)
    (c : Cn n) :
    formF (fun i : Fin (n + 1) => sgDec (eval σ A (sgE (.lit i)))) c = formF (fun i : Fin (n + 1) => sgOf ℓ π i) c := by
  have : (fun i : Fin (n + 1) => sgDec (eval σ A (sgE (.lit i)))) = fun i : Fin (n + 1) => sgOf ℓ π i := by
    funext i
    rw [eval_sgE hr]
    simp only [eval]
    exact sgDec_code _
  rw [this]

end ECDLP.L63
end
