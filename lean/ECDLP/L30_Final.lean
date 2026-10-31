import ECDLP.L30_Count
import ECDLP.L30_Int

/-!
# L30 / Final: the network's integer constraint system counts exactly the generic decompositions

Integer-level statement over `ZMod p` (`p` prime) for the short Weierstrass curve
`y² = x³ + a x + b`.  The integer system is the one of the network (`scripts/network/netlib.py`, `Spec`): integer variables
`x_i < X`, `y_i < p`, `u_i = x_i²`, curve quotients `qc_i`, partial sums `S_k`, inverses `w_k`,
slopes `l_k`, and quotients `q0..q3` of the four addition gadgets, each integer identity being
`E + O·p = q·p` with `q ∈ [0, N)`.
-/

set_option linter.unusedSectionVars false

namespace ECDLP.L30

open WeierstrassCurve WeierstrassCurve.Affine

/-- The short Weierstrass curve `y² = x³ + a x + b` over `ZMod p`. -/
def shortW (p : ℕ) (a b : ℤ) : WeierstrassCurve.Affine (ZMod p) := ⟨0, 0, 0, (a : ZMod p), (b : ZMod p)⟩

/-- The quotient-form of one integer identity: `0 ≤ q < N` and `E + O p = q p`. -/
def QEq (p : ℕ) (O N E q : ℤ) : Prop := 0 ≤ q ∧ q < N ∧ E + O * p = q * p

/-- All integer variables of the network (with `m = n + 1` points). -/
@[ext] structure IntAssign (n : ℕ) where
  P : Fin (n + 1) → ℤ × ℤ
  u : Fin (n + 1) → ℤ
  qc : Fin (n + 1) → ℤ
  S : Fin (n + 1) → ℤ × ℤ
  w : Fin n → ℤ
  l : Fin n → ℤ
  q0 : Fin n → ℤ
  q1 : Fin n → ℤ
  q2 : Fin n → ℤ
  q3 : Fin n → ℤ

/-- The network's constraint system: ranges, `u = x²`, the curve identity, `S 0 = P 0`, `S n = R`, and for
each addition the four gadget identities (inverse, slope, x-sum, y-sum). -/
def IntOK (p : ℕ) (a b : ℤ) (X : ℕ) (O N : ℤ) (R : ℤ × ℤ) {n : ℕ} (t : IntAssign n) : Prop :=
  (∀ i, 0 ≤ (t.P i).1 ∧ (t.P i).1 < X ∧ 0 ≤ (t.P i).2 ∧ (t.P i).2 < p) ∧
  (∀ i, t.u i = (t.P i).1 * (t.P i).1) ∧
  (∀ i, QEq p O N ((t.P i).2 * (t.P i).2 - t.u i * (t.P i).1 - a * (t.P i).1 - b) (t.qc i)) ∧
  (∀ i, 0 ≤ (t.S i).1 ∧ (t.S i).1 < p ∧ 0 ≤ (t.S i).2 ∧ (t.S i).2 < p) ∧
  t.S 0 = t.P 0 ∧ t.S (Fin.last n) = R ∧
  ∀ k : Fin n, (0 ≤ t.w k ∧ t.w k < p) ∧ (0 ≤ t.l k ∧ t.l k < p) ∧
    QEq p O N (t.w k * ((t.P k.succ).1 - (t.S k.castSucc).1) - 1) (t.q0 k) ∧
    QEq p O N (t.l k * ((t.P k.succ).1 - (t.S k.castSucc).1)
      - ((t.P k.succ).2 - (t.S k.castSucc).2)) (t.q1 k) ∧
    QEq p O N (t.l k * t.l k - (t.S k.castSucc).1 - (t.P k.succ).1 - (t.S k.succ).1) (t.q2 k) ∧
    QEq p O N (t.l k * (t.S k.castSucc).1 - t.l k * (t.S k.succ).1 - (t.S k.succ).2
      - (t.S k.castSucc).2) (t.q3 k)

section
variable {p : ℕ} [NeZero p]

/-- Canonical integer lift of a residue. -/
def lift (x : ZMod p) : ℤ := (x.val : ℤ)

theorem lift_cast (x : ZMod p) : ((lift x : ℤ) : ZMod p) = x := by simp [lift]
theorem lift_nonneg (x : ZMod p) : 0 ≤ lift x := by unfold lift; positivity
theorem lift_lt (x : ZMod p) : lift x < p := by
  simp only [lift]; exact_mod_cast ZMod.val_lt x

theorem lift_of_range {z : ℤ} (h0 : 0 ≤ z) (h : z < p) : lift (z : ZMod p) = z := by
  simp only [lift, ZMod.val_intCast]
  exact Int.emod_eq_of_lt h0 h

theorem cast_inj_range {z z' : ℤ} (h0 : 0 ≤ z) (h : z < p) (h0' : 0 ≤ z') (h' : z' < p)
    (e : (z : ZMod p) = z') : z = z' := by
  rw [← lift_of_range h0 h, ← lift_of_range h0' h', e]

theorem cast_zero_of_QEq {O N E q : ℤ} (h : QEq p O N E q) : (E : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨q - O, by linear_combination h.2.2⟩

theorem qeq_unique {O N E q q' : ℤ} (hp : 0 < p) (h : QEq p O N E q) (h' : QEq p O N E q') :
    q = q' := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have : (q - q') * p = 0 := by linear_combination h'.2.2 - h.2.2
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hp'.ne'

end

section main
variable {p : ℕ} [hpp : Fact p.Prime] [NeZero p]

theorem equation_short_iff (a b : ℤ) (x y : ZMod p) :
    (shortW p a b).Equation x y ↔ y * y - x * x * x - (a : ZMod p) * x - (b : ZMod p) = 0 := by
  rw [Affine.equation_iff]
  simp only [shortW]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- Integer-level assignment to the field-level tuple of witnesses. -/
def toSol {n : ℕ} (t : IntAssign n) :
    (Fin (n + 1) → ZMod p × ZMod p) × (Fin (n + 1) → ZMod p × ZMod p) ×
      (Fin n → ZMod p) × (Fin n → ZMod p) :=
  (fun i => (((t.P i).1 : ZMod p), ((t.P i).2 : ZMod p)),
   fun i => (((t.S i).1 : ZMod p), ((t.S i).2 : ZMod p)),
   fun k => (t.w k : ZMod p), fun k => (t.l k : ZMod p))

theorem exists_q {O N E K : ℤ} (hp : 0 < p) (hE : |E| ≤ K * p) (hKO : K ≤ O) (hN : O + K < N)
    (h0 : (E : ZMod p) = 0) : ∃ q, QEq p O N E q := by
  obtain ⟨q, ⟨h1, h2, h3⟩, -⟩ := (zero_iff_window hp E K O N hE hKO hN).1 h0
  exact ⟨q, h1, h2, h3⟩

variable {a b : ℤ} {X : ℕ} {O N : ℤ} {R : ℤ × ℤ} {n : ℕ}

theorem toSol_mem [(shortW p a b).IsElliptic] (hXp : X ≤ p) (t : IntAssign n)
    (ht : IntOK p a b X O N R t) :
    toSol t ∈ SolSet (shortW p a b) (fun x : ZMod p => x.val < X)
      ((R.1 : ZMod p), (R.2 : ZMod p)) n := by
  obtain ⟨hr, hu, hc, hS, h0, hl, hk⟩ := ht
  simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Constraints
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h := cast_zero_of_QEq (hc i)
    rw [hu i] at h
    push_cast at h
    exact Affine.equation_iff_nonsingular.1 ((equation_short_iff a b _ _).2 h)
  · obtain ⟨h1, h2, -, -⟩ := hr i
    have := lift_of_range (p := p) h1 (lt_of_lt_of_le h2 (by exact_mod_cast hXp))
    simp only [lift] at this
    simp only [toSol]
    exact_mod_cast this ▸ h2
  · simp only [toSol]
    rw [h0]
  · intro k
    simp only [toSol]
    rw [← stepL27_iff_stepC _ ⟨rfl, rfl, rfl⟩]
    obtain ⟨-, -, e1, e2, e3, e4⟩ := hk k
    have f1 := cast_zero_of_QEq e1
    have f2 := cast_zero_of_QEq e2
    have f3 := cast_zero_of_QEq e3
    have f4 := cast_zero_of_QEq e4
    push_cast at f1 f2 f3 f4
    exact ⟨f1, f2, f3, f4⟩
  · simp only [toSol]
    rw [hl]

theorem toSol_inj (hp : 0 < p) (hXp : X ≤ p) {t t' : IntAssign n} (ht : IntOK p a b X O N R t)
    (ht' : IntOK p a b X O N R t') (h : toSol (p := p) t = toSol (p := p) t') : t = t' := by
  obtain ⟨hr, hu, hc, hS, h0, hlast, hk⟩ := ht
  obtain ⟨hr', hu', hc', hS', h0', hlast', hk'⟩ := ht'
  simp only [toSol, Prod.mk.injEq] at h
  obtain ⟨hP, hSS, hw, hll⟩ := h
  have hPe : ∀ i, t.P i = t'.P i := fun i => by
    have := congrFun hP i
    simp only [Prod.mk.injEq] at this
    obtain ⟨a1, a2, -, -⟩ := hr i
    obtain ⟨b1, b2, -, -⟩ := hr' i
    exact Prod.ext (cast_inj_range a1 (lt_of_lt_of_le a2 (by omega)) b1
      (lt_of_lt_of_le b2 (by omega)) this.1) (cast_inj_range (hr i).2.2.1 (hr i).2.2.2
      (hr' i).2.2.1 (hr' i).2.2.2 this.2)
  have hSe : ∀ i, t.S i = t'.S i := fun i => by
    have := congrFun hSS i
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (cast_inj_range (hS i).1 (hS i).2.1 (hS' i).1 (hS' i).2.1 this.1)
      (cast_inj_range (hS i).2.2.1 (hS i).2.2.2 (hS' i).2.2.1 (hS' i).2.2.2 this.2)
  have hwe : ∀ k, t.w k = t'.w k := fun k =>
    cast_inj_range (hk k).1.1 (hk k).1.2 (hk' k).1.1 (hk' k).1.2 (congrFun hw k)
  have hle : ∀ k, t.l k = t'.l k := fun k =>
    cast_inj_range (hk k).2.1.1 (hk k).2.1.2 (hk' k).2.1.1 (hk' k).2.1.2 (congrFun hll k)
  have hue : ∀ i, t.u i = t'.u i := fun i => by rw [hu i, hu' i, hPe i]
  refine IntAssign.ext (funext hPe) (funext hue) ?_ (funext hSe) (funext hwe) (funext hle)
    ?_ ?_ ?_ ?_
  · funext i
    have key := hc' i
    simp only [← hPe, ← hue] at key
    exact qeq_unique hp (hc i) key
  · funext k
    have key := (hk' k).2.2.1
    simp only [← hPe, ← hSe, ← hwe, ← hle] at key
    exact qeq_unique hp (hk k).2.2.1 key
  · funext k
    have key := (hk' k).2.2.2.1
    simp only [← hPe, ← hSe, ← hwe, ← hle] at key
    exact qeq_unique hp (hk k).2.2.2.1 key
  · funext k
    have key := (hk' k).2.2.2.2.1
    simp only [← hPe, ← hSe, ← hwe, ← hle] at key
    exact qeq_unique hp (hk k).2.2.2.2.1 key
  · funext k
    have key := (hk' k).2.2.2.2.2
    simp only [← hPe, ← hSe, ← hwe, ← hle] at key
    exact qeq_unique hp (hk k).2.2.2.2.2 key

theorem toSol_surj [(shortW p a b).IsElliptic] (ha0 : 0 ≤ a) (ha : a < p) (hb0 : 0 ≤ b)
    (hb : b < p) (hXX : ∀ x : ℤ, 0 ≤ x → x < X → x * x ≤ p)
    (hO : 2 * (p : ℤ) ≤ O) (hN : O + 2 * (p : ℤ) < N)
    (hR : 0 ≤ R.1 ∧ R.1 < p ∧ 0 ≤ R.2 ∧ R.2 < p)
    (s : (Fin (n + 1) → ZMod p × ZMod p) × (Fin (n + 1) → ZMod p × ZMod p) ×
      (Fin n → ZMod p) × (Fin n → ZMod p))
    (hs : s ∈ SolSet (shortW p a b) (fun x : ZMod p => x.val < X)
      ((R.1 : ZMod p), (R.2 : ZMod p)) n) :
    ∃ t : IntAssign n, IntOK p a b X O N R t ∧ toSol (p := p) t = s := by
  have hp0 : 0 < p := hpp.out.pos
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hpp.out.two_le
  obtain ⟨P, S, w, l⟩ := s
  simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  obtain ⟨hns, h0, hstep, hlast⟩ := hs
  have hcurve : ∀ i, ((lift (P i).2 * lift (P i).2 - (lift (P i).1 * lift (P i).1) * lift (P i).1
      - a * lift (P i).1 - b : ℤ) : ZMod p) = 0 := by
    intro i
    have := (equation_short_iff a b _ _).1 (Affine.equation_iff_nonsingular.2 (hns i).1)
    push_cast
    simp only [lift_cast]
    exact this
  have hxX : ∀ i, lift (P i).1 < X := fun i => by
    have := (hns i).2
    simp only [lift]
    exact_mod_cast this
  have hxx : ∀ i, lift (P i).1 * lift (P i).1 ≤ p := fun i =>
    hXX _ (lift_nonneg _) (hxX i)
  have hqc : ∀ i, ∃ q, QEq p O N (lift (P i).2 * lift (P i).2 - (lift (P i).1 * lift (P i).1)
      * lift (P i).1 - a * lift (P i).1 - b) q := fun i =>
    exists_q hp0 (K := 2 * p)
      (bound_curve hp2 (lift_nonneg _) (hxx i) (lift_nonneg _) (lift_lt _) ha0 ha hb0 hb)
      hO hN (hcurve i)
  choose qc hqc using hqc
  have hst : ∀ k : Fin n, StepL27 (S k.castSucc).1 (S k.castSucc).2 (P k.succ).1 (P k.succ).2
      (w k) (l k) (S k.succ).1 (S k.succ).2 := fun k =>
    (stepL27_iff_stepC _ ⟨rfl, rfl, rfl⟩ _ _ _ _ _ _ _ _).2 (hstep k)
  have hq0 : ∀ k : Fin n, ∃ q, QEq p O N (lift (w k) * (lift (P k.succ).1
      - lift (S k.castSucc).1) - 1) q := fun k => by
    refine exists_q hp0 (K := p) (bound_inv hp2 (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _) (lift_nonneg _) (lift_lt _)) (by omega) (by omega) ?_
    push_cast; simp only [lift_cast]; exact (hst k).1
  have hq1 : ∀ k : Fin n, ∃ q, QEq p O N (lift (l k) * (lift (P k.succ).1
      - lift (S k.castSucc).1) - (lift (P k.succ).2 - lift (S k.castSucc).2)) q := fun k => by
    refine exists_q hp0 (K := p) (bound_slope hp2 (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _) (lift_nonneg _) (lift_lt _) (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _)) (by omega) (by omega) ?_
    push_cast; simp only [lift_cast]; exact (hst k).2.1
  have hq2 : ∀ k : Fin n, ∃ q, QEq p O N (lift (l k) * lift (l k) - lift (S k.castSucc).1
      - lift (P k.succ).1 - lift (S k.succ).1) q := fun k => by
    refine exists_q hp0 (K := p) (bound_xsum hp2 (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _) (lift_nonneg _) (lift_lt _) (lift_nonneg _) (lift_lt _)) (by omega) (by omega) ?_
    push_cast; simp only [lift_cast]; exact (hst k).2.2.1
  have hq3 : ∀ k : Fin n, ∃ q, QEq p O N (lift (l k) * lift (S k.castSucc).1
      - lift (l k) * lift (S k.succ).1 - lift (S k.succ).2 - lift (S k.castSucc).2) q :=
    fun k => by
    refine exists_q hp0 (K := p) (bound_ysum hp2 (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _) (lift_nonneg _) (lift_lt _) (lift_nonneg _) (lift_lt _) (lift_nonneg _)
      (lift_lt _)) (by omega) (by omega) ?_
    push_cast; simp only [lift_cast]; exact (hst k).2.2.2
  choose q0 hq0 using hq0
  choose q1 hq1 using hq1
  choose q2 hq2 using hq2
  choose q3 hq3 using hq3
  refine ⟨⟨fun i => (lift (P i).1, lift (P i).2), fun i => lift (P i).1 * lift (P i).1, qc,
    fun i => (lift (S i).1, lift (S i).2), fun k => lift (w k), fun k => lift (l k),
    q0, q1, q2, q3⟩, ?_, ?_⟩
  · refine ⟨fun i => ⟨lift_nonneg _, hxX i, lift_nonneg _, lift_lt _⟩, fun i => rfl, hqc,
      fun i => ⟨lift_nonneg _, lift_lt _, lift_nonneg _, lift_lt _⟩, ?_, ?_, fun k => ?_⟩
    · show (lift (S 0).1, lift (S 0).2) = (lift (P 0).1, lift (P 0).2)
      rw [h0]
    · show (lift (S (Fin.last n)).1, lift (S (Fin.last n)).2) = R
      rw [hlast]
      exact Prod.ext (lift_of_range hR.1 hR.2.1) (lift_of_range hR.2.2.1 hR.2.2.2)
    · exact ⟨⟨lift_nonneg _, lift_lt _⟩, ⟨lift_nonneg _, lift_lt _⟩, hq0 k, hq1 k, hq2 k, hq3 k⟩
  · simp [toSol, lift_cast]

/-- **integer level**.**  Over `ZMod p` (`p` prime) for the elliptic short Weierstrass
curve `y² = x³ + a x + b`, the number of integer assignments satisfying the network's constraint system
with `0 ≤ x_i < X` equals the number of ordered generic factor-base `(n+1)`-tuples
(`x_i.val < X`) of nonsingular points with sum `R`. -/
theorem card_int_eq_card_generic [(shortW p a b).IsElliptic] (ha0 : 0 ≤ a) (ha : a < p)
    (hb0 : 0 ≤ b) (hb : b < p) (hXp : X ≤ p) (hXX : ∀ x : ℤ, 0 ≤ x → x < X → x * x ≤ p)
    (hO : 2 * (p : ℤ) ≤ O) (hN : O + 2 * (p : ℤ) < N)
    (hR : 0 ≤ R.1 ∧ R.1 < p ∧ 0 ≤ R.2 ∧ R.2 < p)
    (hRns : (shortW p a b).Nonsingular (R.1 : ZMod p) (R.2 : ZMod p)) :
    {t : IntAssign n | IntOK p a b X O N R t}.ncard =
      (GenSet (shortW p a b) (fun x : ZMod p => x.val < X)
        ((R.1 : ZMod p), (R.2 : ZMod p)) n).card := by
  rw [← card_sol_eq_card_gen (shortW p a b) (fun x : ZMod p => x.val < X) hRns n,
    ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun t _ => toSol (p := p) t)
  · intro t ht
    exact toSol_mem hXp t ht
  · intro t t' ht ht' h
    exact toSol_inj hpp.out.pos hXp ht ht' h
  · intro s hs
    obtain ⟨t, ht, e⟩ := toSol_surj ha0 ha hb0 hb hXX hO hN hR s hs
    exact ⟨t, ht, e⟩

end main

end ECDLP.L30
