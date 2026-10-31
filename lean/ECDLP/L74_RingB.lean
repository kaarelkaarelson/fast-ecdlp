import ECDLP.L68_Ring
import ECDLP.L74_Fv
import FactoringAux.EngineBddBase
import FactoringAux.EngineMulBdd

/-!
# L74 / RingB: value bounds (`Bdd V`) of the `ZMod q` combinators of L68 (`mulE`, `pwE`, `sumE`, `faE`, `hatE`)

All of them hold as soon as `q*q <= V` and the exponents (products of the small numbers `w, A, i, k`) are `<= V`.
Every ring expression evaluates to a value `< q` (`lt_*`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Factoring.Aux Factoring.Aux.SB Ex ECDLP.L68

section
variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vq x : ℕ}

theorem bdd_mulE {a b : Ex} (ha : Bdd V σ A a) (hb : Bdd V σ A b) (hq : σ vq ≤ V)
    (hab : Ex.eval σ A a * Ex.eval σ A b ≤ V) : Bdd V σ A (mulE vq a b) := B_zmul ha hb hq hab

theorem lt_mulE {a b : Ex} (hq : 0 < σ vq) : Ex.eval σ A (mulE vq a b) < σ vq := lt_zmul hq

theorem bdd_pwE {n : Ex} (hq0 : 0 < σ vq) (hqV : σ vq ≤ V) (h2 : 2 ≤ V) (hn : Bdd V σ A n) :
    Bdd V σ A (pwE vq x n) := B_zprod hq0 hqV (by omega) hn (fun j _ => B_lit h2)

theorem lt_pwE {n : Ex} (hq : 1 < σ vq) : Ex.eval σ A (pwE vq x n) < σ vq := lt_zprod hq

theorem bdd_sumE {n b : Ex} (hq0 : 0 < σ vq) (hqV : σ vq ≤ V) (hn : Bdd V σ A n)
    (hb : ∀ j < Ex.eval σ A n, Bdd V (Function.update σ x j) A b) : Bdd V σ A (sumE vq x n b) :=
  B_zsum hq0 hqV hn hb

theorem lt_sumE {n b : Ex} (hq : 0 < σ vq) : Ex.eval σ A (sumE vq x n b) < σ vq := lt_zsum hq

/-- the product of two ring values is `<= V` once `q * q <= V` -/
theorem mul_lt_le {a b q : ℕ} (ha : a < q) (hb : b < q) (hqq : q * q ≤ V) : a * b ≤ V :=
  le_trans (Nat.mul_le_mul ha.le hb.le) hqq

/-- `faOut`: root exponent `v0`, `r`, `k` variables; the digit body `u` is bounded and `< q` for every loop value. -/
theorem bdd_faE {vA x1 v0 vr vk : ℕ} {u : Ex} (hq2 : 2 < σ vq) (hqq : σ vq * σ vq ≤ V) (hqV : σ vq ≤ V)
    (h2 : 2 ≤ V) (hx : x1 ≠ vq ∧ x1 ≠ vA ∧ x1 ≠ v0 ∧ x1 ≠ vr ∧ x1 ≠ vk)
    (hA : σ vA ≤ V) (h0 : σ v0 ≤ V) (hr : σ vr ≤ V) (hk : σ vk ≤ V)
    (hexp1 : σ vr * σ vk ≤ V) (hexp2 : σ v0 * (σ vr * σ vk) ≤ V)
    (hexp3 : ∀ i < σ vA, σ vA * i ≤ V ∧ σ vA * i * σ vk ≤ V ∧ σ v0 * (σ vA * i * σ vk) ≤ V)
    (hu : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A u ∧ Ex.eval (Function.update σ x1 i) A u < σ vq) :
    Bdd V σ A (faE vq vA x1 (.var v0) (.var vr) (.var vk) u) := by
  obtain ⟨h1, h2', h3, h4, h5⟩ := hx
  have hq0 : 0 < σ vq := by omega
  refine bdd_mulE (bdd_pwE hq0 hqV h2 ?_) (bdd_sumE hq0 hqV (B_var hA) fun i hi => ?_) hqV ?_
  · exact B_mul (B_var h0) (B_mul (B_var hr) (B_var hk) hexp1) hexp2
  · have hi' : (Function.update σ x1 i) vq = σ vq := Function.update_of_ne (Ne.symm h1) _ _
    have hA' : (Function.update σ x1 i) vA = σ vA := Function.update_of_ne (Ne.symm h2') _ _
    have h0' : (Function.update σ x1 i) v0 = σ v0 := Function.update_of_ne (Ne.symm h3) _ _
    have hk' : (Function.update σ x1 i) vk = σ vk := Function.update_of_ne (Ne.symm h5) _ _
    have hx1 : (Function.update σ x1 i) x1 = i := Function.update_self _ _ _
    have hiA : i < σ vA := by simpa [Ex.eval] using hi
    obtain ⟨e1, e2, e3⟩ := hexp3 i hiA
    have hpw : Bdd V (Function.update σ x1 i) A
        (pwE vq x1 (.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk)))) := by
      refine bdd_pwE (by rw [hi']; exact hq0) (by rw [hi']; exact hqV) h2 ?_
      refine B_mul (B_var (by rw [h0']; exact h0)) (B_mul (B_mul (B_var (by rw [hA']; exact hA))
        (B_var (by rw [hx1]; omega)) ?_) (B_var (by rw [hk']; exact hk)) ?_) ?_
      · simp only [Ex.eval, hA', hx1]; exact e1
      · simp only [Ex.eval, hA', hx1, hk']; exact e2
      · simp only [Ex.eval, hA', hx1, hk', h0']; exact e3
    refine bdd_mulE (hu i hiA).1 hpw (by rw [hi']; exact hqV) ?_
    have hlt : Ex.eval (Function.update σ x1 i) A
        (pwE vq x1 (.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk)))) < σ vq := by
      have := lt_pwE (σ := Function.update σ x1 i) (A := A) (vq := vq) (x := x1)
        (n := Ex.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk))) (by rw [hi']; omega)
      rwa [hi'] at this
    exact mul_lt_le (hu i hiA).2 hlt hqq
  · have hlt1 : Ex.eval σ A (pwE vq x1 (.mul (.var v0) (.mul (.var vr) (.var vk)))) < σ vq := lt_pwE (by omega)
    have hlt2 : Ex.eval σ A (sumE vq x1 (.var vA) (mulE vq u (pwE vq x1 (.mul (.var v0)
        (.mul (.mul (.var vA) (.var x1)) (.var vk)))))) < σ vq := lt_sumE hq0
    exact mul_lt_le hlt1 hlt2 hqq

theorem lt_faE {vA x1 v0 vr vk : ℕ} {u : Ex} (hq : 0 < σ vq) :
    Ex.eval σ A (faE vq vA x1 (.var v0) (.var vr) (.var vk) u) < σ vq := lt_mulE hq

/-- `hatOut`: root exponent `v0`, `k` variable -/
theorem bdd_hatE {vA x1 v0 vk : ℕ} {u : Ex} (hq2 : 2 < σ vq) (hqq : σ vq * σ vq ≤ V) (hqV : σ vq ≤ V)
    (h2 : 2 ≤ V) (hx : x1 ≠ vq ∧ x1 ≠ vA ∧ x1 ≠ v0 ∧ x1 ≠ vk)
    (hA : σ vA ≤ V) (h0 : σ v0 ≤ V) (hk : σ vk ≤ V)
    (hexp3 : ∀ i < σ vA, σ vA * i ≤ V ∧ σ vA * i * σ vk ≤ V ∧ σ v0 * (σ vA * i * σ vk) ≤ V)
    (hu : ∀ i < σ vA, Bdd V (Function.update σ x1 i) A u ∧ Ex.eval (Function.update σ x1 i) A u < σ vq) :
    Bdd V σ A (hatE vq vA x1 (.var v0) (.var vk) u) := by
  obtain ⟨h1, h2', h3, h5⟩ := hx
  have hq0 : 0 < σ vq := by omega
  refine bdd_sumE hq0 hqV (B_var hA) fun i hi => ?_
  have hi' : (Function.update σ x1 i) vq = σ vq := Function.update_of_ne (Ne.symm h1) _ _
  have hA' : (Function.update σ x1 i) vA = σ vA := Function.update_of_ne (Ne.symm h2') _ _
  have h0' : (Function.update σ x1 i) v0 = σ v0 := Function.update_of_ne (Ne.symm h3) _ _
  have hk' : (Function.update σ x1 i) vk = σ vk := Function.update_of_ne (Ne.symm h5) _ _
  have hx1 : (Function.update σ x1 i) x1 = i := Function.update_self _ _ _
  have hiA : i < σ vA := by simpa [Ex.eval] using hi
  obtain ⟨e1, e2, e3⟩ := hexp3 i hiA
  have hpw : Bdd V (Function.update σ x1 i) A
      (pwE vq x1 (.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk)))) := by
    refine bdd_pwE (by rw [hi']; exact hq0) (by rw [hi']; exact hqV) h2 ?_
    refine B_mul (B_var (by rw [h0']; exact h0)) (B_mul (B_mul (B_var (by rw [hA']; exact hA))
      (B_var (by rw [hx1]; omega)) ?_) (B_var (by rw [hk']; exact hk)) ?_) ?_
    · simp only [Ex.eval, hA', hx1]; exact e1
    · simp only [Ex.eval, hA', hx1, hk']; exact e2
    · simp only [Ex.eval, hA', hx1, hk', h0']; exact e3
  refine bdd_mulE (hu i hiA).1 hpw (by rw [hi']; exact hqV) ?_
  have hlt : Ex.eval (Function.update σ x1 i) A
      (pwE vq x1 (.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk)))) < σ vq := by
    have := lt_pwE (σ := Function.update σ x1 i) (A := A) (vq := vq) (x := x1)
      (n := Ex.mul (.var v0) (.mul (.mul (.var vA) (.var x1)) (.var vk))) (by rw [hi']; omega)
    rwa [hi'] at this
  exact mul_lt_le (hu i hiA).2 hlt hqq

theorem lt_hatE {vA x1 v0 vk : ℕ} {u : Ex} (hq : 0 < σ vq) :
    Ex.eval σ A (hatE vq vA x1 (.var v0) (.var vk) u) < σ vq := lt_sumE hq

end
end ECDLP.L74
end
