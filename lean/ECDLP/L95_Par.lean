import ECDLP.L91_Real
import ECDLP.L90_MidReal

/-!
# L95 / Par: the L83 prelude (`szE`, `log2E`, `prel`, `AEx .. MEx`, `epsEx`) REWRITTEN so that no intermediate value exceeds `Nat.size p` (or `2^small`)

PROBLEM (L95 item 1; real barrier for the old expressions): `szE = Nat.size p` is computed through `pE` (the integer `p`, `p < 2^sigma0`) and `2^j` for `j <= sigma0`;
`log2E (size p)` computes `2^j` for `j <= size p`.  `Bdd V` of these needs `p <= V` and `2^(size p) <= V`, which is false in the regime of the theorem
(`V = 2^(19680 X^3)`, `X^4 ~ n`, `size p ~ n/(const m)`: `p ~ 2^size >> V`).
FIX: `szE2` = number of `j < sigma0` such that some bit `k >= j` of `p` is set (reads bits only; every value `<= sigma0`);
`log2E2` = number of `j < x` such that `x / 2^(j+1) > 0` (iterated halving; every value `<= x`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L59 ECDLP.L76 ECDLP.L73 ECDLP.L83

theorem exists_iff (p N j : ℕ) (hp : p < 2 ^ N) :
    (∃ k ∈ range N, ¬ k < j ∧ p.testBit k = true) ↔ j < Nat.size p := by
  constructor
  · rintro ⟨k, hk, hkj, hb⟩
    have := Nat.ge_two_pow_of_testBit hb
    have : k < Nat.size p := Nat.lt_size.2 this
    omega
  · intro hj
    have hp0 : p ≠ 0 := by
      intro h; subst h; simp at hj
    have h1 : Nat.size p ≤ Nat.log2 p + 1 := Nat.size_le.2 (Nat.lt_log2_self)
    have h2 : Nat.log2 p < Nat.size p := Nat.lt_size.2 (Nat.log2_self_le hp0)
    have hs : Nat.size p ≤ N := Nat.size_le.2 hp
    refine ⟨Nat.log2 p, by simp; omega, by omega, Nat.testBit_log2 hp0⟩

theorem sum_size2 (p N : ℕ) (hp : p < 2 ^ N) :
    ∑ j ∈ range N, (if 0 < ∑ k ∈ range N, (if k < j then 0 else (p.testBit k).toNat) then 1 else 0) = Nat.size p := by
  have h1 : ∀ j, (0 < ∑ k ∈ range N, (if k < j then 0 else (p.testBit k).toNat)) ↔ j < Nat.size p := by
    intro j
    rw [Finset.sum_pos_iff, ← exists_iff p N j hp]
    constructor
    · rintro ⟨k, hk, h⟩
      refine ⟨k, hk, ?_, ?_⟩ <;> by_cases h' : k < j <;> by_cases hb : p.testBit k = true <;> simp_all
    · rintro ⟨k, hk, h, hb⟩
      exact ⟨k, hk, by simp [h, hb]⟩
  simp only [h1]
  rw [Finset.sum_boole]
  have hs : Nat.size p ≤ N := Nat.size_le.2 hp
  have : (range N).filter (fun j => j < Nat.size p) = range (Nat.size p) := by
    ext j; simp only [mem_filter, mem_range]; constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [this]; simp

section
variable (u : ℕ)

/-- `Nat.size p`, from the bits of `p` only -/
def szE2 : Ex :=
  nsum (u + 60) (.var 0) (.ifLt (.lit 0)
    (nsum (u + 61) (.var 0) (.ifLt (.var (u + 61)) (.var (u + 60)) (.lit 0) (nbitW (.var 0) 0 (.var (u + 61)))))
    (.lit 1) (.lit 0))

/-- `Nat.log 2 x` for `x` not reading `u+60, u+61, u+62`: `#{j < x | 0 < x / 2^(j+1)}`, by iterated halving -/
def log2E2 (x : Ex) : Ex :=
  nsum (u + 60) x (.ifLt (.lit 0)
    (.iter (u + 61) (u + 62) (.add (.var (u + 60)) (.lit 1)) x (.div (.var (u + 62)) (.lit 2))) (.lit 1) (.lit 0))

def jm1E2 : Ex := .sub (.div (.add (log2E2 u (.var (u + 63))) (.lit 2)) (.lit 4)) (.lit 1)

def prel2 (body : Ex) : Ex :=
  .lett (u + 63) (szE2 u) <| .lett (u + 64) (jm1E2 u) <| .lett (u + 65) (.add (.mul (.lit 2) (.var (u + 64))) (.lit 1)) <|
  .lett (u + 66) (pow2 (u + 60) (.var (u + 65))) <|
  .lett (u + 67) (.add (.div (.add (.mul (.lit 2) (.var (u + 63))) (.lit 3)) (.var (u + 66))) (.lit 1)) body

def AEx2 : Ex := prel2 u (pow2 (u + 60) (.add (.var (u + 64)) (.lit 1)))
def hEx2 : Ex := prel2 u (pow2 (u + 60) (.var (u + 64)))
def pbEx2 : Ex := prel2 u (pow2 (u + 60) (.var (u + 67)))
def bEx2 : Ex := prel2 u (.var (u + 67))
def MEx2 : Ex := prel2 u (.mul (.var (u + 66))
  (.add (.div (.add (.add (.mul (.lit 2) (.var (u + 67))) (.var (u + 65))) (.lit 4)) (.var (u + 66))) (.lit 1)))

/-- `eps = +-1` of a term, with the repaired `MEx2` -/
def epsEx2 (n cv tv : ℕ) : Ex := .ifLt (negEx n cv tv) (.lit 1) (.lit 1) (pow2 (u + 60) (MEx2 u))

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

theorem eval_szE2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (szE2 u) = Nat.size p := by
  have hp := p_lt hR
  rw [szE2, eval_nsum]
  have h0 : ∀ j, Function.update σ (u + 60) j 0 = σ 0 := fun j => Function.update_of_ne (by omega) _ _
  have key : ∀ j, Ex.eval (Function.update σ (u + 60) j) A (.ifLt (.lit 0)
    (nsum (u + 61) (.var 0) (.ifLt (.var (u + 61)) (.var (u + 60)) (.lit 0) (nbitW (.var 0) 0 (.var (u + 61)))))
    (.lit 1) (.lit 0)) = (if 0 < ∑ k ∈ range (σ 0), (if k < j then 0 else (p.testBit k).toNat) then 1 else 0) := by
    intro j
    have e : Ex.eval (Function.update σ (u + 60) j) A (nsum (u + 61) (.var 0)
        (.ifLt (.var (u + 61)) (.var (u + 60)) (.lit 0) (nbitW (.var 0) 0 (.var (u + 61))))) =
        ∑ k ∈ range (σ 0), (if k < j then 0 else (p.testBit k).toNat) := by
      rw [eval_nsum]
      have h00 : Ex.eval (Function.update σ (u + 60) j) A (.var 0) = σ 0 := h0 j
      rw [h00]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have t0 : Function.update (Function.update σ (u + 60) j) (u + 61) k 0 = σ 0 := by
        rw [Function.update_of_ne (by omega)]; exact h0 j
      have t1 : Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 61) = k := Function.update_self ..
      have t2 : Function.update (Function.update σ (u + 60) j) (u + 61) k (u + 60) = j := by
        rw [Function.update_of_ne (by omega)]; exact Function.update_self ..
      simp only [Ex.eval, t1, t2]
      split_ifs with h
      · rfl
      · rw [eval_nbitW]
        simp only [Ex.eval, t0, t1]
        rw [show numCells (A 0) 1 (σ 0) = p from hR.hp]
    show (if Ex.eval _ A (.lit 0) < Ex.eval _ A _ then Ex.eval _ A (.lit 1) else Ex.eval _ A (.lit 0)) = _
    rw [e]; rfl
  have h00 : Ex.eval σ A (.var 0) = σ 0 := rfl
  rw [h00]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  exact sum_size2 p (σ 0) hp

theorem iterF_half (x : ℕ) (w : ℕ) : iterF (fun _ s => s / 2) x w = x / 2 ^ w := by
  induction w with
  | zero => simp [iterF]
  | succ w ih => simp only [iterF, ih]; rw [Nat.div_div_eq_div_mul, pow_succ]

theorem sum_log2 (L : ℕ) : ∑ x ∈ range L, (if 0 < L / 2 ^ (x + 1) then 1 else 0) = Nat.log 2 L := by
  rw [← sum_log L]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : L < 2 ^ (x + 1)
  · rw [if_pos h, if_neg]; simp [Nat.div_eq_of_lt h]
  · rw [if_neg h, if_pos]; exact Nat.div_pos (by omega) (Nat.two_pow_pos _)

theorem eval_log2E2' (L : ℕ) (h63 : σ (u + 63) = L) :
    Ex.eval σ A (log2E2 u (.var (u + 63))) = Nat.log 2 L := by
  rw [← sum_log2 L, log2E2, eval_nsum]
  have h00 : Ex.eval σ A (.var (u + 63)) = L := h63
  rw [h00]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have e1 : Function.update σ (u + 60) j (u + 63) = L := by rw [Function.update_of_ne (by omega)]; exact h63
  have e2 : Function.update σ (u + 60) j (u + 60) = j := Function.update_self ..
  have hit : Ex.eval (Function.update σ (u + 60) j) A
      (.iter (u + 61) (u + 62) (.add (.var (u + 60)) (.lit 1)) (.var (u + 63)) (.div (.var (u + 62)) (.lit 2))) = L / 2 ^ (j + 1) := by
    simp only [Ex.eval, e1, e2]
    rw [← iterF_half]
    congr 1
    funext j' s
    simp [Ex.eval]
  show (if Ex.eval _ A (.lit 0) < Ex.eval _ A _ then Ex.eval _ A (.lit 1) else Ex.eval _ A (.lit 0)) = _
  rw [hit]; rfl

theorem eval_jm1E2 (L : ℕ) (h : σ (u + 63) = L) : Ex.eval σ A (jm1E2 u) = jm1 L := by
  have := eval_log2E2' u (σ := σ) (A := A) L h
  simp only [jm1E2, Ex.eval, h] at this ⊢
  rw [this]; rfl

theorem eval_prel2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) (body : Ex) :
    Ex.eval σ A (prel2 u body) = Ex.eval (st u σ (Nat.size p)) A body := by
  simp only [prel2, Ex.eval]
  rw [eval_szE2 u hR, eval_jm1E2 u (Nat.size p) (by simp)]
  simp only [st, Ex.eval, eval_pow2, Function.update_apply, kP, DP, bP, ECDLP.L59.Bits]
  simp

theorem eval_AEx2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (AEx2 u) = (NParE (Nat.size p)).A := by
  rw [AEx2, eval_prel2 u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE, AP]

theorem eval_hEx2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (hEx2 u) = (NParE (Nat.size p)).h := by
  rw [hEx2, eval_prel2 u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE, hP]

theorem eval_pbEx2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (pbEx2 u) = 2 ^ (NParE (Nat.size p)).b := by
  rw [pbEx2, eval_prel2 u hR]; simp [st, Function.update_apply, eval_pow2, Ex.eval, NParE]

theorem eval_bEx2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (bEx2 u) = (NParE (Nat.size p)).b := by
  rw [bEx2, eval_prel2 u hR]; simp [st, Function.update_apply, Ex.eval, NParE]

theorem eval_MEx2 (hR : ECDLP.L72.Reads72 σ A p a b X xR yR π ℓ bW) :
    Ex.eval σ A (MEx2 u) = 2 ^ (NParE (Nat.size p)).k * wP (Nat.size p) := by
  rw [MEx2, eval_prel2 u hR]; simp [st, Function.update_apply, Ex.eval, NParE, DP, wP, kP]

end
end ECDLP.L95
end
