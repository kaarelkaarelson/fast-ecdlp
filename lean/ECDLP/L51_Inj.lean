import Mathlib
import ECDLP.L44_Str

/-!
# L51 / Inj: `strOf` is injective on points of the curve with `x.val < 2^ℓ`
(x-bits and the sign bit determine the point).
-/
namespace ECDLP.L51
open ECDLP.L44

theorem zmod2 : ∀ y y' : ZMod 2, y = -y' → y = y' := by decide

theorem sign_inj (p : ℕ) [hp : Fact p.Prime] (y y' : ZMod p) (h2 : y * y = y' * y')
    (hs : decide ((p - 1) / 2 < y.val) = decide ((p - 1) / 2 < y'.val)) : y = y' := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rcases mul_self_eq_mul_self_iff.1 h2 with h | h
  · exact h
  · by_cases hy : y' = 0
    · rw [h, hy]; simp
    · rcases hp.out.eq_two_or_odd' with h2p | hodd
      · subst h2p
        exact zmod2 y y' h
      · have hv : y.val = p - y'.val := by haveI : NeZero y' := ⟨hy⟩; rw [h]; exact ZMod.val_neg_of_ne_zero y'
        have hlt := ZMod.val_lt y'
        have hpos : 0 < y'.val := by
          rcases Nat.eq_zero_or_pos y'.val with h0 | h0
          · exact absurd ((ZMod.val_eq_zero y').1 h0) hy
          · exact h0
        obtain ⟨k, hk⟩ := hodd
        exfalso
        rw [hv] at hs
        subst hk
        have : (2 * k + 1 - 1) / 2 = k := by omega
        rw [this] at hs
        by_cases h1 : k < y'.val
        · have h3 : ¬ k < 2 * k + 1 - y'.val := by omega
          simp [h1, h3] at hs
        · have h3 : k < 2 * k + 1 - y'.val := by omega
          simp [h1, h3] at hs

theorem x_inj (p ℓ : ℕ) [NeZero p] (x x' : ZMod p) (hx : x.val < 2 ^ ℓ) (hx' : x'.val < 2 ^ ℓ)
    (h : ∀ q < ℓ, x.val.testBit (ℓ - 1 - q) = x'.val.testBit (ℓ - 1 - q)) : x = x' := by
  have : x.val = x'.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < ℓ
    · have := h (ℓ - 1 - j) (by omega)
      rwa [show ℓ - 1 - (ℓ - 1 - j) = j by omega] at this
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  exact (ZMod.val_injective p) this

theorem chunk_at {n : ℕ} (p ℓ : ℕ) (P : Fin (n + 1) → ZMod p × ZMod p) (i : Fin (n + 1)) (q : ℕ)
    (hq : q ≤ ℓ) : (strOf p ℓ P)[i * (ℓ + 1) + q]? = (chunk p ℓ (P i))[q]? := by
  have hlt' : i * (ℓ + 1) + q < (n + 1) * (ℓ + 1) := by
    have := i.2
    nlinarith
  have hget := flat_get (fun i => chunk p ℓ (P i)) (fun i => chunk_length p ℓ _) _ hlt'
  show (List.ofFn fun i => chunk p ℓ (P i)).flatten[i * (ℓ + 1) + q]? = _
  rw [hget]
  obtain ⟨d1, d2⟩ := divmod i q (ℓ + 1) (by omega)
  simp only [d2]
  congr 3
  exact Fin.ext d1

/-- **Injectivity.** On tuples of curve points (`y² = x³ + a x + b`) with `x.val < 2^ℓ`. -/
theorem strOf_inj {n : ℕ} (p : ℕ) [Fact p.Prime] (a b : ZMod p) (ℓ : ℕ)
    (P Q : Fin (n + 1) → ZMod p × ZMod p)
    (hP : ∀ i, (P i).2 * (P i).2 = (P i).1 ^ 3 + a * (P i).1 + b)
    (hQ : ∀ i, (Q i).2 * (Q i).2 = (Q i).1 ^ 3 + a * (Q i).1 + b)
    (hxP : ∀ i, (P i).1.val < 2 ^ ℓ) (hxQ : ∀ i, (Q i).1.val < 2 ^ ℓ)
    (h : strOf p ℓ P = strOf p ℓ Q) : P = Q := by
  funext i
  have key : ∀ q ≤ ℓ, (chunk p ℓ (P i))[q]? = (chunk p ℓ (Q i))[q]? := by
    intro q hq
    rw [← chunk_at p ℓ P i q hq, ← chunk_at p ℓ Q i q hq, h]
  have hx : (P i).1 = (Q i).1 := by
    apply x_inj p ℓ _ _ (hxP i) (hxQ i)
    intro q hq
    have := key q hq.le
    rw [chunk_get_x p ℓ _ hq, chunk_get_x p ℓ _ hq] at this
    exact Option.some.inj this
  have hs := key ℓ le_rfl
  rw [chunk_get_s, chunk_get_s] at hs
  have hs' := Option.some.inj hs
  have hy : (P i).2 = (Q i).2 := by
    apply sign_inj p _ _ _ hs'
    rw [hP i, hQ i, hx]
  exact Prod.ext hx hy

end ECDLP.L51

#print axioms ECDLP.L51.strOf_inj
