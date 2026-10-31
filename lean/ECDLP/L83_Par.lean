import ECDLP.L83_Lay
import ECDLP.L73_Dec
import ECDLP.L76_Lay2
import ECDLP.L72_Init

/-!
# L83 / Par: the shape parameters `A, h, 2^b, b, M` of `NParE (Nat.size p)` as expressions of the instance (`Reads72`)

`szE` = `Nat.size p` (count of `j < sigma0` with `2^j <= p`), `log2E`, and a `prelude` that binds `L = size p`, `jm1`, `k`, `D = 2^k`, `bP` in slots `u+63 ..u+67`
(loop binders `u+60, u+61`, temp `u+62`); `AE, hE, pbE, bE, MeE` of the explicit parameters of L59.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L59 ECDLP.L76 ECDLP.L73

section
variable (u : ℕ)

def pE : Ex := valE (.var 0) 0 920 921

/-- `Nat.size p` -/
def szE : Ex :=
  .lett (u + 62) pE (nsum (u + 60) (.var 0) (.ifLt (.var (u + 62)) (pow2 (u + 61) (.var (u + 60))) (.lit 0) (.lit 1)))

/-- `Nat.log 2 (value of x)` for an expression `x` not reading `u+60`, `u+61` -/
def log2E (x : Ex) : Ex :=
  nsum (u + 60) x (.ifLt x (pow2 (u + 61) (.add (.var (u + 60)) (.lit 1))) (.lit 0) (.lit 1))

def jm1E : Ex := .sub (.div (.add (log2E u (.var (u + 63))) (.lit 2)) (.lit 4)) (.lit 1)

/-- binds `u+63 = L`, `u+64 = jm1 L`, `u+65 = kP L`, `u+66 = DP L`, `u+67 = bP L` -/
def prel (body : Ex) : Ex :=
  .lett (u + 63) (szE u) <| .lett (u + 64) (jm1E u) <| .lett (u + 65) (.add (.mul (.lit 2) (.var (u + 64))) (.lit 1)) <|
  .lett (u + 66) (pow2 (u + 60) (.var (u + 65))) <|
  .lett (u + 67) (.add (.div (.add (.mul (.lit 2) (.var (u + 63))) (.lit 3)) (.var (u + 66))) (.lit 1)) body

def AEx : Ex := prel u (pow2 (u + 60) (.add (.var (u + 64)) (.lit 1)))
def hEx : Ex := prel u (pow2 (u + 60) (.var (u + 64)))
def pbEx : Ex := prel u (pow2 (u + 60) (.var (u + 67)))
def bEx : Ex := prel u (.var (u + 67))
def MEx : Ex := prel u (.mul (.var (u + 66))
  (.add (.div (.add (.add (.mul (.lit 2) (.var (u + 67))) (.var (u + 65))) (.lit 4)) (.var (u + 66))) (.lit 1)))

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem eval_pE (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) : Ex.eval σ A pE = p := by
  rw [pE, eval_valE 0 0 920 921 (by norm_num) (by norm_num) (by norm_num)]; exact hR.hp

theorem p_lt (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) : p < 2 ^ σ 0 := by
  rw [← hR.hp]; exact numCells_lt _ _ _

theorem sum_size (p N : ℕ) (hp : p < 2 ^ N) :
    ∑ j ∈ range N, (if p < 2 ^ j then 0 else 1) = Nat.size p := by
  have h1 : ∀ j, (if p < 2 ^ j then 0 else 1) = if 2 ^ j ≤ p then 1 else 0 := fun j => by
    split_ifs <;> first | rfl | omega
  simp only [h1]
  rw [Finset.sum_boole]
  have : (range N).filter (fun j => 2 ^ j ≤ p) = range (Nat.size p) := by
    ext j
    simp only [mem_filter, mem_range]
    have hs : Nat.size p ≤ N := Nat.size_le.2 hp
    constructor
    · rintro ⟨-, h⟩; exact Nat.lt_size.2 h
    · intro h; exact ⟨by omega, Nat.lt_size.1 h⟩
  rw [this]; simp

theorem sum_log (L : ℕ) : ∑ x ∈ range L, (if L < 2 ^ (x + 1) then 0 else 1) = Nat.log 2 L := by
  have h1 : ∀ x, (if L < 2 ^ (x + 1) then 0 else 1) = if 2 ^ (x + 1) ≤ L then 1 else 0 := fun x => by
    split_ifs <;> first | rfl | omega
  simp only [h1]
  rw [Finset.sum_boole]
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · have : (range L).filter (fun x => 2 ^ (x + 1) ≤ L) = range (Nat.log 2 L) := by
      ext x
      simp only [mem_filter, mem_range]
      have hl := Nat.log_le_self 2 L
      constructor
      · rintro ⟨-, h⟩; have := Nat.le_log_of_pow_le (by norm_num) h; omega
      · intro h
        exact ⟨by omega, (Nat.le_log_iff_pow_le (by norm_num) (by omega)).1 (by omega)⟩
    rw [this]; simp

theorem eval_szE (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (szE u) = Nat.size p := by
  have hv : Ex.eval σ A pE = p := eval_pE hR
  simp only [szE, Ex.eval]
  rw [hv, eval_nsum]
  simp only [Ex.eval, eval_pow2, Function.update_apply]
  simp
  exact sum_size p _ (p_lt hR)

theorem eval_log2E (x : Ex) (hx : ∀ j, Ex.eval (Function.update σ (u + 60) j) A x = Ex.eval σ A x) :
    Ex.eval σ A (log2E u x) = Nat.log 2 (Ex.eval σ A x) := by
  simp only [log2E, eval_nsum, Ex.eval, eval_pow2, hx]
  simp [Function.update_apply]
  exact sum_log _

theorem eval_jm1E (L : ℕ) (h : σ (u + 63) = L) : Ex.eval σ A (jm1E u) = jm1 L := by
  have := eval_log2E (u := u) (σ := σ) (A := A) (.var (u + 63)) (fun j => by show Function.update σ (u + 60) j (u + 63) = σ (u + 63); simp [Function.update_apply])
  simp only [jm1E, Ex.eval, h] at this ⊢
  rw [this]; rfl

/-- the values bound by `prel` -/
def st (σ : ℕ → ℕ) (L : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update σ (u + 63) L)
    (u + 64) (jm1 L)) (u + 65) (kP L)) (u + 66) (DP L)) (u + 67) (bP L)

theorem eval_prel (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (body : Ex) :
    Ex.eval σ A (prel u body) = Ex.eval (st u σ (Nat.size p)) A body := by
  simp only [prel, Ex.eval]
  rw [eval_szE u hR, eval_jm1E u (Nat.size p) (by simp)]
  simp only [st, Ex.eval, eval_pow2, Function.update_apply, kP, DP, bP, ECDLP.L59.Bits]
  simp

theorem eval_AEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (AEx u) = (NParE (Nat.size p)).A := by
  rw [AEx, eval_prel u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE, AP]

theorem eval_hEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (hEx u) = (NParE (Nat.size p)).h := by
  rw [hEx, eval_prel u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE, hP]

theorem eval_pbEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (pbEx u) = 2 ^ (NParE (Nat.size p)).b := by
  rw [pbEx, eval_prel u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE]

theorem eval_bEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (bEx u) = (NParE (Nat.size p)).b := by
  rw [bEx, eval_prel u hR]; simp [st, Function.update_apply, Ex.eval, NParE]

theorem eval_MEx (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (MEx u) = 2 ^ (NParE (Nat.size p)).k * wP (Nat.size p) := by
  rw [MEx, eval_prel u hR]; simp [st, Function.update_apply, Ex.eval, NParE, DP, wP, kP]

end
end ECDLP.L83
end
