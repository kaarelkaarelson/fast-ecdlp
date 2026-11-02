import Mathlib
import ECDLPv2.L114_Trans
import ECDLPv2.L116_Row
import ECDLPv2.L116_Alg

/-!
# L116 / Chernoff: the acceptance/cap term (H1, probabilistic part) in the finite counting model

Model: tags `a : Fin n → A` uniform (counted), `ev : A →+ G` onto, the presented point of draw `t` is
`ev a_t + cc(history)` and the oracle `Orc` (arbitrary, stateful) answers; a draw is *accepted* if `acc (answer)`.
Hypothesis (paper: "`R` is uniform on `G` and each sample is accepted with probability at least `c_m(4)`"):
for **every** history `h`, at least a `c` fraction of the points of `G` are accepted by `Orc h`.

* `expmom` : exponential moment `∑_a θ^{#accepted(a)} ≤ ((1 - c(1-θ)) |A|)^n`  (adaptive; by induction on `n`).
* `few_accepted` : if `c·n ≥ 2k` then `#{a : #accepted(a) < k} · e^{k/4} ≤ |A|^n`  (Chernoff for the lower tail,
  the paper's "the cap is not hit, which fails with probability at most `e^{-N_r/4}`").
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L116

open ECDLP.L114 Finset

section chern
variable {A G O : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup G]

open Classical in
/-- **Exponential moment bound** (adaptive oracle). -/
theorem expmom (ev : A →+ G) (Orc : List O → G → O) (cc : List O → G) (acc : O → Prop)
    (c θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc : ∀ h, c * Fintype.card A ≤ ((univ.filter (fun a : A => acc (Orc h (ev a + cc h)))).card : ℝ)) :
    ∀ (n : ℕ) (h : List O),
      ∑ a : Fin n → A, θ ^ ((ECDLP.L114.trans ev Orc cc h n a).countP (fun o => decide (acc o))) ≤
        ((1 - c * (1 - θ)) * Fintype.card A) ^ n := by
  intro n
  induction n with
  | zero => intro h; simp [ECDLP.L114.trans]
  | succ n ih =>
    intro h
    set B : ℝ := (1 - c * (1 - θ)) * Fintype.card A with hB
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => A), Fintype.sum_prod_type]
    have hstep : ∀ a0 : A, ∑ r : Fin n → A,
        θ ^ ((ECDLP.L114.trans ev Orc cc h (n + 1) (Fin.consEquiv (fun _ : Fin (n + 1) => A) (a0, r))).countP
          (fun o => decide (acc o))) ≤
        (if acc (Orc h (ev a0 + cc h)) then θ else 1) * B ^ n := by
      intro a0
      have hcons : ∀ r : Fin n → A,
          (ECDLP.L114.trans ev Orc cc h (n + 1) (Fin.consEquiv (fun _ : Fin (n + 1) => A) (a0, r))) =
            Orc h (ev a0 + cc h) :: trans ev Orc cc (h ++ [Orc h (ev a0 + cc h)]) n r := by
        intro r
        simp [ECDLP.L114.trans, Fin.consEquiv, Fin.tail_cons, Fin.cons_zero]
      simp_rw [hcons, List.countP_cons]
      by_cases hacc : acc (Orc h (ev a0 + cc h))
      · simp only [hacc, decide_true, if_true]
        have := ih (h ++ [Orc h (ev a0 + cc h)])
        calc ∑ r : Fin n → A, θ ^ ((ECDLP.L114.trans ev Orc cc (h ++ [Orc h (ev a0 + cc h)]) n r).countP
                (fun o => decide (acc o)) + 1)
            = θ * ∑ r : Fin n → A, θ ^ ((ECDLP.L114.trans ev Orc cc (h ++ [Orc h (ev a0 + cc h)]) n r).countP
                (fun o => decide (acc o))) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
          _ ≤ θ * B ^ n := mul_le_mul_of_nonneg_left this hθ0
      · simp only [hacc, decide_false, if_false, Bool.false_eq_true, add_zero, one_mul]
        exact ih _
    have hsum_ite : ∑ a0 : A, (if acc (Orc h (ev a0 + cc h)) then θ else 1) ≤ B := by
      have h1 : ∀ a0 : A, (if acc (Orc h (ev a0 + cc h)) then θ else 1) =
          1 - (1 - θ) * (if acc (Orc h (ev a0 + cc h)) then 1 else 0) := by
        intro a0; split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have := hc h
      have h1θ : 0 ≤ 1 - θ := by linarith
      rw [hB]
      nlinarith
    have hBn : 0 ≤ B ^ n := le_trans (Finset.sum_nonneg fun a _ => pow_nonneg hθ0 _) (ih h)
    calc _ ≤ ∑ a0 : A, (if acc (Orc h (ev a0 + cc h)) then θ else 1) * B ^ n :=
          Finset.sum_le_sum fun a0 _ => hstep a0
      _ = (∑ a0 : A, (if acc (Orc h (ev a0 + cc h)) then θ else 1)) * B ^ n := by rw [Finset.sum_mul]
      _ ≤ B * B ^ n := mul_le_mul_of_nonneg_right hsum_ite hBn
      _ = B ^ (n + 1) := by ring

open Classical in
/-- **Chernoff, lower tail.**  If every history leaves a `c` fraction of points accepted and `2k ≤ c n`,
then the number of tag sequences with fewer than `k` accepted draws is at most `e^{-k/4} |A|^n`. -/
theorem few_accepted (ev : A →+ G) (Orc : List O → G → O) (cc : List O → G) (acc : O → Prop)
    (c : ℝ) (hc0' : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : ∀ h, c * Fintype.card A ≤ ((univ.filter (fun a : A => acc (Orc h (ev a + cc h)))).card : ℝ))
    (n k : ℕ) (hnk : 2 * (k : ℝ) ≤ c * n) (h : List O) :
    ((univ.filter (fun a : Fin n → A =>
        (ECDLP.L114.trans ev Orc cc h n a).countP (fun o => decide (acc o)) < k)).card : ℝ) * Real.exp (k / 4) ≤
      (Fintype.card A : ℝ) ^ n := by
  have hmom := expmom ev Orc cc acc c (1 / 2) (by norm_num) (by norm_num) hc n h
  set F := univ.filter (fun a : Fin n → A =>
        (ECDLP.L114.trans ev Orc cc h n a).countP (fun o => decide (acc o)) < k) with hF
  have hMarkov : (F.card : ℝ) * (1 / 2) ^ k ≤ ∑ a : Fin n → A,
      (1 / 2 : ℝ) ^ ((ECDLP.L114.trans ev Orc cc h n a).countP (fun o => decide (acc o))) := by
    calc (F.card : ℝ) * (1 / 2) ^ k = ∑ a ∈ F, (1 / 2 : ℝ) ^ k := by simp [mul_comm]
      _ ≤ ∑ a ∈ F, (1 / 2 : ℝ) ^ ((ECDLP.L114.trans ev Orc cc h n a).countP (fun o => decide (acc o))) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hlt := (Finset.mem_filter.1 ha).2
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun a _ _ => by positivity)
  have hcard : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
  have hB : (1 - c * (1 - 1 / 2)) * (Fintype.card A : ℝ) = (1 - c / 2) * Fintype.card A := by ring
  rw [hB] at hmom
  have h1 : (1 - c / 2 : ℝ) ≤ Real.exp (-(c / 2)) := by
    have := Real.add_one_le_exp (-(c / 2)); linarith
  have h2 : (1 - c / 2 : ℝ) ^ n ≤ Real.exp (-(c * n / 2)) := by
    calc (1 - c / 2 : ℝ) ^ n ≤ (Real.exp (-(c / 2))) ^ n :=
          pow_le_pow_left₀ (by linarith) h1 n
      _ = Real.exp (-(c * n / 2)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.exp (-(c * n / 2)) ≤ Real.exp (-(k : ℝ)) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : (F.card : ℝ) * (1 / 2) ^ k ≤ Real.exp (-(k : ℝ)) * (Fintype.card A : ℝ) ^ n := by
    refine hMarkov.trans (hmom.trans ?_)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (h2.trans h3) (pow_nonneg hcard _)
  have h5 : (2 : ℝ) ≤ Real.exp (3 / 4) := by
    have := Real.log_two_lt_d9
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (3 / 4) := Real.exp_le_exp.2 (by linarith)
  -- F.card ≤ 2^k e^{-k} |A|^n, and 2^k e^{-3k/4} ≤ 1
  have h6 : (F.card : ℝ) ≤ 2 ^ k * Real.exp (-(k : ℝ)) * (Fintype.card A : ℝ) ^ n := by
    have : (F.card : ℝ) = (F.card : ℝ) * (1 / 2) ^ k * 2 ^ k := by
      rw [mul_assoc, ← mul_pow]; norm_num
    rw [this]
    calc _ ≤ Real.exp (-(k : ℝ)) * (Fintype.card A : ℝ) ^ n * 2 ^ k :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by ring
  have h7 : (2 : ℝ) ^ k ≤ Real.exp (3 / 4 * k) := by
    calc (2 : ℝ) ^ k ≤ (Real.exp (3 / 4)) ^ k := pow_le_pow_left₀ (by norm_num) h5 k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc (F.card : ℝ) * Real.exp (k / 4) ≤ 2 ^ k * Real.exp (-(k : ℝ)) * (Fintype.card A : ℝ) ^ n * Real.exp (k / 4) :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ ≤ Real.exp (3 / 4 * k) * Real.exp (-(k : ℝ)) * (Fintype.card A : ℝ) ^ n * Real.exp (k / 4) := by
        gcongr
    _ = (Fintype.card A : ℝ) ^ n := by
        have : Real.exp (3 / 4 * k) * Real.exp (-(k : ℝ)) * Real.exp (k / 4) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; convert Real.exp_zero using 2; ring
        calc _ = (Real.exp (3 / 4 * k) * Real.exp (-(k : ℝ)) * Real.exp (k / 4)) * (Fintype.card A : ℝ) ^ n := by ring
          _ = _ := by rw [this, one_mul]

open Classical in
/-- the accepted fraction of tags is the accepted fraction of points (uniform `R`). -/
theorem accept_frac [Fintype G] (ev : A →+ G) (hsurj : Function.Surjective ev) (P : G → Prop)
    (s0 : G) (c : ℝ) (hc : c * Fintype.card G ≤ ((univ.filter P).card : ℝ)) :
    c * Fintype.card A ≤ ((univ.filter (fun a : A => P (ev a + s0))).card : ℝ) := by
  set φ : A → G := fun a => ev a + s0 with hφ
  have hfib : ∀ R R' : G, (univ.filter (fun a : A => φ a = R)).card =
      (univ.filter (fun a : A => φ a = R')).card := by
    intro R R'
    have h := shift_count ev hsurj (fun x => x = R) s0 (s0 + R - R')
    have himg : (univ.filter (fun a : A => ev a + (s0 + R - R') = R)) = (univ.filter (fun a : A => φ a = R')) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, hφ]
      constructor
      · intro h1
        have : ev a + s0 - R' = ev a + (s0 + R - R') - R := by abel
        rw [← sub_eq_zero, this]; exact sub_eq_zero.2 h1
      · intro h1
        have : ev a + (s0 + R - R') - R = ev a + s0 - R' := by abel
        rw [← sub_eq_zero, this]; exact sub_eq_zero.2 h1
    rw [himg] at h
    exact h
  obtain ⟨R0⟩ : Nonempty G := ⟨0⟩
  set k := (univ.filter (fun a : A => φ a = R0)).card with hk
  have hA : Fintype.card A = Fintype.card G * k := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := (univ : Finset G)) (fun _ _ => mem_univ _)]
    rw [Finset.sum_congr rfl (fun R (_ : R ∈ (univ : Finset G)) => hfib R R0)]
    simp [hk, mul_comm]
  have hP : (univ.filter (fun a : A => P (φ a))).card = (univ.filter P).card * k := by
    have h1 : ∀ R ∈ univ.filter P,
        ((univ.filter (fun a : A => P (φ a))).filter (fun a => φ a = R)).card = k := by
      intro R hR
      rw [hk, ← hfib R R0]
      congr 1; ext a
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; simpa using hR, h⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := univ.filter P)
      (fun a ha => by simpa using ha), Finset.sum_congr rfl h1]
    simp
  rw [hP, hA]
  push_cast
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith

end chern

section cap
variable {A G O : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup G] [Fintype G] {f s Nd m : ℕ} [NeZero Nd]

open Classical in
/-- **The cap/acceptance term (H1, probabilistic part), for the concrete algorithm.**
If at every history the oracle accepts at least a `c` fraction of the points of `G` (`hcG`), and the number of draws
satisfies `2 (f + s) ≤ c · Nd`, then the number of tag sequences for which fewer than `f + s` draws are accepted
(`¬ AccAlg`) is at most `e^{-(f+s)/4} |A|^Nd` -- for any (stateful) oracle and any history-dependent shift `cc`
(in particular the planted shift, whose presented points are still uniform). -/
theorem cap_bound (ev : A →+ G) (hsurj : Function.Surjective ev) (Orc : List O → G → O)
    (cc : List O → G) (dec : O → Option (Fin m → Fin f)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcG : ∀ h, c * Fintype.card G ≤ ((univ.filter (fun R : G => (dec (Orc h R)).isSome = true)).card : ℝ))
    (hn : 2 * ((f + s : ℕ) : ℝ) ≤ c * Nd) :
    ((univ.filter (fun a : Fin Nd → A =>
        ¬ AccAlg (f := f) (s := s) (Nd := Nd) dec (ECDLP.L114.trans ev Orc cc [] Nd a))).card : ℝ) *
        Real.exp (((f + s : ℕ) : ℝ) / 4) ≤ (Fintype.card A : ℝ) ^ Nd := by
  have hfew := few_accepted ev Orc cc (fun o => (dec o).isSome = true) c hc0 hc1
    (fun h => accept_frac ev hsurj (fun R => (dec (Orc h R)).isSome = true) (cc h) c (by convert hcG h))
    Nd (f + s) hn []
  refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card ?_)) (Real.exp_pos _).le) hfew
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  set w := ECDLP.L114.trans ev Orc cc [] Nd a with hw
  have hlen : w.length = Nd := trans_length ev Orc cc Nd [] a
  have hcount : Nat.count (accD dec w) Nd = nColl dec w := by
    rw [← nColl_take dec w Nd hlen.ge, List.take_of_length_le hlen.le]
  have hlt : ¬ (f + s ≤ Nat.count (accD dec w) Nd) := fun h => ha ⟨hlen, h⟩
  rw [hcount] at hlt
  have h2 : nColl dec w < f + s := by omega
  refine lt_of_eq_of_lt ?_ h2
  unfold nColl
  exact List.countP_congr (fun o _ => by simp)

end cap
end ECDLP.L116
