import ECDLP.L63_Count

/-!
# L63 / Size: L59's size lemmas for the concrete family, with `nmax = 9`, `K = 18m - 6`, `|iota| = 24m - 1`
-/
noncomputable section
namespace ECDLP.L63
open Finset ECDLP.L44 ECDLP.L54 ECDLP.L56 ECDLP.L59 ECDLP.L34 ECDLP.L38 Slot Cst

variable {n K : ℕ}

/-- **Number of gates of the concrete edge network**: `≤ A (24 m + 18 m (11 + A))`, `m = n+1`, `A⁴ ≤ 4L`. -/
theorem gates_concrete (L : ℕ) (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) :
    Fintype.card (CG (Slot n) (UC sg e) (NParE L).A) ≤
      AP L * (24 * (n + 1) + 18 * (n + 1) * (11 + AP L)) := by
  have h := gates_explicit (ι := Slot n) (ιc := UC sg e) L 9 (fun c => card_UC_le9 sg e c)
  rw [card_Slot] at h
  have hK := card_K e
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  rw [hK]
  nlinarith [Nat.zero_le (n * AP L)]

/-- **Setting length of the concrete edge network**: every gate has setting `≤ 1640 · A · D` bits. -/
theorem setting_concrete (L : ℕ) (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K)
    (φ : ∀ c, UC sg e c → Slot n) (F : ∀ c, Form (UC sg e c))
    (ok : Slot n → Fin (NParE L).A → Dg (NParE L) → Prop) (g : CG (Slot n) (UC sg e) (NParE L).A) :
    settingBits (w := fun _ : Fin K => wP L) φ F ok g ≤ 1640 * (AP L * DP L) := by
  have h := settingBits_explicit (ιc := UC sg e) φ F L 9 (fun c => card_UC_le9 sg e c) ok g
  simpa using h

theorem setting_concrete_L (L : ℕ) (hL : 4 ≤ L) :
    (1640 * (AP L * DP L)) ^ 4 ≤ 1640 ^ 4 * 4 * L ^ 3 := by
  simpa using settingBits_explicit_L L 9 hL

end ECDLP.L63
end
