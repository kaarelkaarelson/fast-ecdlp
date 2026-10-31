import ECDLP.L86_Pp
import ECDLP.L73_Asm
import ECDLP.L68_CarB

/-!
# L86 / Car: closed-form digits for the car gate and the car message expression without `digE`

The parents of `car c j` are `ib (j % A)` (global index `d + j % A`, `d = nι A + off c + nc A + A`) and, for `j > 0`, `car (j-1)`
(index `d + A + j - 1`).  The ring radix is `2^M + 1` (`card_msg_ib`), the carry radix is `2^(M+3)` (`card_msg_car`), `nf = 1`, so
`digit(ib) = z % (2^M+1)` and `digit(car (j-1)) = (z / (2^M+1)) % 2^(M+3)`.
`carOutXD` / `carWXD` read these from the setting code in slot `u+7` and the gate index from slot `u+16` of the decode state
(no `digE`, no node re-decode).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79

/-- digit of the ring parent: `z % (2^M + 1)` -/
def digCarR (u : ℕ) : Ex := .mod (.var (u + 7)) (.add (.var (u + 11)) (.lit 1))
/-- digit of the previous carry: `(z / (2^M + 1)) % (8 * 2^M)` -/
def digCarC (u : ℕ) : Ex := .mod (.div (.var (u + 7)) (.add (.var (u + 11)) (.lit 1))) (.mul (.lit 8) (.var (u + 11)))

theorem dp_digCarR (u : ℕ) : Ex.dp (digCarR u) = 3 := by simp [digCarR, Ex.dp]
theorem dp_digCarC (u : ℕ) : Ex.dp (digCarC u) = 4 := by simp [digCarC, Ex.dp]

/-- the car binders: carry code `vc` (0 for `j = 0`) and ring code `vr`, then `body` -/
def carInD (u vj vc vr : ℕ) (body : Ex) : Ex :=
  .lett vc (.ifLt (.lit 0) (.var vj) (digCarC u) (.lit 0)) (.lett vr (digCarR u) body)

/-- the car message expression: gate index from slot `u+16` -/
def carOutXD (u : ℕ) : Ex := carInD u (u + 16) (u + 93) (u + 94) (carOutE (u + 10) (u + 11) (u + 16) (u + 93) (u + 94))
/-- the car weight expression (`u+28` holds `A*A`) -/
def carWXD (u : ℕ) : Ex := carInD u (u + 16) (u + 93) (u + 94) (carWE (u + 10) (u + 11) (u + 16) (u + 28) (u + 93) (u + 94))

section node
variable {m B : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

theorem car_parents (c : Fin K) (j : Fin (N0.A * N0.A)) (x : Fin (L.gTot N0.A)) :
    (L.enum N0.A).symm x ∈ paC (w := w) φ (CG.gt c (Gate.car j)) ↔
      (x.val = L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A ∨
        (0 < j.val ∧ x.val + 1 = L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + N0.A + j.val)) := by
  rw [pa_iff (L := L) (w := w) φ]
  simp [PA]

theorem car_ib_idx (c : Fin K) (j : Fin (N0.A * N0.A)) :
    (L.enum N0.A (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) : ℕ) =
      L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A := by
  rw [Lay.enum_gt, Lay.gateE_ib]; simp only; omega

theorem car_prev_idx (c : Fin K) (j : Fin (N0.A * N0.A)) (h : 0 < j.val) :
    (L.enum N0.A (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) : ℕ) + 1 =
      L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + N0.A + j.val := by
  rw [Lay.enum_gt, Lay.gateE_car]; simp only; omega

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include X hu hC hσ

/-- **the ring code read by the car node is `z % (2^M+1)`** -/
theorem pm_car_ib {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j))
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hz : σ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)
      (hF := ECDLP.L64.edge_free_nonempty φ F ok m)).e a z) :
    pm (w := w) φ F ok m z (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) =
      σ (u + 2) % (2 ^ (NP N0 w c).M + 1) := by
  have := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  set k : Fin (L.gTot N0.A) := L.enum N0.A (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) with hk
  set σ' := Function.update (Function.update σ u (a : ℕ)) (u + 1) (k : ℕ) with hσ'
  have g' : Ag B σ₀ σ' := (hσ.upd (by omega) _).upd (by omega) _
  have e2 : σ' (u + 2) = σ (u + 2) := by
    rw [hσ', Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have e0 : σ' u = a := by rw [hσ', Function.update_of_ne (by omega), Function.update_self]
  have e1 : σ' (u + 1) = k := by rw [hσ', Function.update_self]
  have hmem : CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩) ∈ paC (w := w) φ ((L.enum N0.A).symm a) := by
    rw [hka]; exact car_ib_mem φ c j
  have h1 := ECDLP.L73.eval_digE_pm' X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k)
    (p := CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) e0 e1 (by rw [hk]; simp) hmem z
    (by rw [e2]; exact hz)
  have hj := j.2
  by_cases h0 : 0 < j.val
  · have h2 := eval_digE_first X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k) e0 e1
      (i1 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A)
      (i2 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + N0.A + j.val - 1)
      (Q1 := 2 ^ (NP N0 w c).M + 1)
      (by have := Nat.mod_lt j.val N0.toPar.A_pos; omega)
      (by rw [hka]; exact card_free_gt φ F ok m c _)
      (fun x hx => by
        rw [hka] at hx
        have := (car_parents (w := w) (φ := φ) L c j x).1 hx
        omega)
      (by rw [hk]; exact car_ib_idx L c j) (by rw [hk, Equiv.symm_apply_apply]; exact card_msg_ib φ F ok m c _)
    rw [e2] at h2
    rw [← h1, h2]
  · have h2 := eval_digE_first X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k) e0 e1
      (i1 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A)
      (i2 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A + 1)
      (Q1 := 2 ^ (NP N0 w c).M + 1)
      (by omega)
      (by rw [hka]; exact card_free_gt φ F ok m c _)
      (fun x hx => by
        have := (car_parents (w := w) (φ := φ) L c j x).1 (by rw [hka] at hx; exact hx)
        omega)
      (by rw [hk]; exact car_ib_idx L c j) (by rw [hk, Equiv.symm_apply_apply]; exact card_msg_ib φ F ok m c _)
    rw [e2] at h2
    rw [← h1, h2]

/-- **the previous-carry code read by the car node (`j > 0`) is `(z / (2^M+1)) % 2^(M+3)`** -/
theorem pm_car_prev {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (h0 : 0 < j.val)
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hz : σ (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) (L.enum N0.A)
      (hF := ECDLP.L64.edge_free_nonempty φ F ok m)).e a z) :
    pm (w := w) φ F ok m z (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) =
      σ (u + 2) / (2 ^ (NP N0 w c).M + 1) % (2 ^ ((NP N0 w c).M + 3)) := by
  have := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  set k : Fin (L.gTot N0.A) := L.enum N0.A (CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) with hk
  set σ' := Function.update (Function.update σ u (a : ℕ)) (u + 1) (k : ℕ) with hσ'
  have g' : Ag B σ₀ σ' := (hσ.upd (by omega) _).upd (by omega) _
  have e2 : σ' (u + 2) = σ (u + 2) := by
    rw [hσ', Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have e0 : σ' u = a := by rw [hσ', Function.update_of_ne (by omega), Function.update_self]
  have e1 : σ' (u + 1) = k := by rw [hσ', Function.update_self]
  have hmem : CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩) ∈ paC (w := w) φ ((L.enum N0.A).symm a) := by
    rw [hka]; exact car_prev_mem φ c j h0
  have h1 := ECDLP.L73.eval_digE_pm' X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k)
    (p := CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩)) e0 e1 (by rw [hk]; simp) hmem z
    (by rw [e2]; exact hz)
  have hj := j.2
  have hmod := Nat.mod_lt j.val N0.toPar.A_pos
  have h2 := eval_digE_second X hu hC g' (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k) e0 e1
    (i1 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A)
    (i2 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + N0.A + j.val - 1)
    (Q1 := 2 ^ (NP N0 w c).M + 1) (Q2 := 2 ^ ((NP N0 w c).M + 3))
    (by omega)
    (by rw [hka]; exact card_free_gt φ F ok m c _)
    (fun x hx => by
      have := (car_parents (w := w) (φ := φ) L c j x).1 (by rw [hka] at hx; exact hx)
      omega)
    (fun x hx => by
      refine ⟨?_, ?_⟩
      · rw [hka]
        have : (L.enum N0.A).symm x ∈ paC (w := w) φ (CG.gt c (Gate.car j)) :=
          (car_parents (w := w) (φ := φ) L c j x).2 (Or.inl (by omega))
        exact this
      · have hxe : (L.enum N0.A).symm x = CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩) := by
          apply (L.enum N0.A).injective
          apply Fin.ext
          rw [Equiv.apply_symm_apply, car_ib_idx]; omega
        rw [hxe]; exact card_msg_ib φ F ok m c _)
    (by have := car_prev_idx L c j h0; rw [hk]; omega)
    (by rw [hk, Equiv.symm_apply_apply]; exact card_msg_car φ F ok m c _)
  rw [e2] at h2
  rw [← h1, h2]

end node
end ECDLP.L86
end
