import Mathlib
import ECDLPv2.L116_Main

/-!
# L118: crude totient bound `n ≤ (1 + log₂ n) φ(n)` and its use with `gen_two_explicit`.
-/
namespace ECDLP.L118
open Finset

/-- distinct integers ≥ 2: `∏ p/(p-1) ≤ card + 1`. -/
theorem prod_ratio_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, ((p : ℚ) / ((p : ℚ) - 1)) ≤ (S.card : ℚ) + 1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have haS : a ∉ S := fun h => lt_irrefl _ (hlt a h)
    have hS' : ∀ p ∈ S, 2 ≤ p := fun p hp => hS p (mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (mem_insert_self _ _)
    have hsub : S ⊆ Finset.Icc 2 (a - 1) := by
      intro p hp
      simp only [mem_Icc]
      exact ⟨hS' p hp, by have := hlt p hp; omega⟩
    have hc : S.card + 2 ≤ a := by
      have := Finset.card_le_card hsub
      simp at this; omega
    have ih' := ih hS'
    rw [prod_insert haS, card_insert_of_notMem haS]
    have hcq : (S.card : ℚ) + 2 ≤ (a : ℚ) := by exact_mod_cast hc
    have hpos : (0 : ℚ) < (a : ℚ) - 1 := by linarith [(by positivity : (0:ℚ) ≤ S.card)]
    have hnn : 0 ≤ ∏ p ∈ S, ((p : ℚ) / ((p : ℚ) - 1)) := by
      apply prod_nonneg
      intro p hp
      have : (2 : ℚ) ≤ p := by exact_mod_cast hS' p hp
      apply div_nonneg <;> linarith
    have h1 : (a : ℚ) / ((a : ℚ) - 1) * ∏ p ∈ S, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        (a : ℚ) / ((a : ℚ) - 1) * ((S.card : ℚ) + 1) :=
      mul_le_mul_of_nonneg_left ih' (by positivity)
    refine h1.trans ?_
    push_cast
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith

theorem card_primeFactors_le_log (n : ℕ) (hn : n ≠ 0) : n.primeFactors.card ≤ Nat.log 2 n := by
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    (Nat.prod_primeFactors_dvd n)
  exact Nat.le_log_of_pow_le (by norm_num) (h1.trans h2)

/-- **Crude Mertens replacement.**  `n ≤ (1 + log₂ n) · φ(n)`. -/
theorem totient_ge (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ) ≤ (1 + Nat.log 2 n : ℕ) * (Nat.totient n : ℚ) := by
  have key := Nat.totient_mul_prod_primeFactors n
  have hpf : ∀ p ∈ n.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hr := prod_ratio_le _ hpf
  have hk := card_primeFactors_le_log n hn
  have hφ : (0 : ℚ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)
  -- ∏ p/(p-1) = n/φ(n)
  have hprodp : (0:ℚ) < ∏ p ∈ n.primeFactors, (p : ℚ) := prod_pos (fun p hp => by
    have : (2:ℚ) ≤ p := by exact_mod_cast hpf p hp
    linarith)
  have hprodm : (0:ℚ) < ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := prod_pos (fun p hp => by
    have : (2:ℚ) ≤ p := by exact_mod_cast hpf p hp
    linarith)
  have keyq : (Nat.totient n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) =
      (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
    have := congrArg (Nat.cast : ℕ → ℚ) key
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    have : 1 ≤ p := (hpf p hp).trans' (by norm_num)
    push_cast [Nat.cast_sub this]; ring
  have hdiv : ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) =
      (∏ p ∈ n.primeFactors, (p : ℚ)) / ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := prod_div_distrib _ _
  rw [hdiv, div_le_iff₀ hprodm] at hr
  have hkq : (n.primeFactors.card : ℚ) ≤ Nat.log 2 n := by exact_mod_cast hk
  -- φ·P ≤ (k+1)·(∏(p-1))·φ ... derive n ≤ (k+1) φ
  have h3 : (Nat.totient n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) ≤
      (Nat.totient n : ℚ) * (((n.primeFactors.card : ℚ) + 1) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1)) :=
    mul_le_mul_of_nonneg_left hr hφ.le
  rw [keyq] at h3
  have h4 : (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) ≤
      ((Nat.totient n : ℚ) * ((n.primeFactors.card : ℚ) + 1)) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
    linarith
  have h5 := le_of_mul_le_mul_right h4 hprodm
  push_cast
  nlinarith

/-- **Lemma gen, rank ≤ 2, polylog form.** -/
theorem gen_two_log {A : Type*} [AddCommGroup A] [Fintype A] (hA : ECDLP.L116.HasGen A 2) :
    (5 / 16 : ℚ) / (1 + Nat.log 2 (Fintype.card A) : ℕ) ≤
      (ECDLP.L116.genCount A 2 : ℚ) / (Fintype.card A : ℚ) ^ 2 := by
  have hN : Fintype.card A ≠ 0 := Fintype.card_ne_zero
  have h := ECDLP.L116.gen_two_explicit hA
  have ht := totient_ge _ hN
  have hNq : (0:ℚ) < Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hL : (0:ℚ) < (1 + Nat.log 2 (Fintype.card A) : ℕ) := by positivity
  refine le_trans ?_ h
  rw [div_le_iff₀ hL]
  have : (1:ℚ) ≤ (Nat.totient (Fintype.card A) : ℚ) / (Fintype.card A) * (1 + Nat.log 2 (Fintype.card A) : ℕ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hNq]; linarith
  nlinarith

/-- expected trials until two uniform samples generate `A` is at most `(16/5)(1 + log₂|A|)`. -/
theorem gen_two_trials {A : Type*} [AddCommGroup A] [Fintype A] (hA : ECDLP.L116.HasGen A 2) :
    (1 : ℚ) / ((ECDLP.L116.genCount A 2 : ℚ) / (Fintype.card A : ℚ) ^ 2) ≤
      (16 / 5 : ℚ) * (1 + Nat.log 2 (Fintype.card A) : ℕ) := by
  have h := gen_two_log hA
  have hL : (0:ℚ) < (1 + Nat.log 2 (Fintype.card A) : ℕ) := by positivity
  have hp : (0:ℚ) < (5 / 16 : ℚ) / (1 + Nat.log 2 (Fintype.card A) : ℕ) := by positivity
  calc (1:ℚ) / ((ECDLP.L116.genCount A 2 : ℚ) / (Fintype.card A : ℚ) ^ 2)
      ≤ 1 / ((5 / 16 : ℚ) / (1 + Nat.log 2 (Fintype.card A) : ℕ)) := one_div_le_one_div_of_le hp h
    _ = _ := by field_simp

end ECDLP.L118
