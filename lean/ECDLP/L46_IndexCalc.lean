import Mathlib
import ECDLP.L40_LasVegas

/-!
# L46 (3): the Las Vegas index-calculus step, abstractly

`G` an additive abelian group, a module over a field `K` (in the application `K = ZMod ℓ`, `G` the
prime-order subgroup of `W.Point`, `Q = d • P`).  `FB : Fin s → G` the factor base, `D : G → Option (Fin m → G)`
a deterministic decomposition oracle.

* `OracleSound D FB` : every answer `D R = some t` has `∑ t_j = R` and every `t_j ∈ range FB`.
* `countRow` : the relation row (multiplicities of the factor-base points in a decomposition).
* `recover_correct` : rows `R_i = a_i P + b_i Q`, a vector `λ` supported on the successful rows
  with `λᵀE = 0`; if `∑ λ_i b_i ≠ 0` then `d = -(∑ λ_i a_i)/(∑ λ_i b_i)`.
* `bad_count` / `bad_prob` : if `λ` is any (nonzero-valued) function of the residues `c_i = a_i + d b_i`
  (which is all the oracle sees), the pairs `(a,b)` with `∑ λ_i b_i = 0` are exactly a `1/q` fraction.
-/
namespace ECDLP.L46

open Finset

section algebra
variable {K : Type*} [Field K] {G : Type*} [AddCommGroup G] [Module K G]

/-- A deterministic oracle returns valid decompositions into factor-base points. -/
def OracleSound {m s : ℕ} (D : G → Option (Fin m → G)) (FB : Fin s → G) : Prop :=
  ∀ R t, D R = some t → (∑ j, t j = R) ∧ ∀ j, ∃ k, t j = FB k

open Classical in
/-- multiplicities of the factor-base points in a decomposition (the relation row) -/
noncomputable def countRow {m s : ℕ} (FB : Fin s → G) (t : Fin m → G) : Fin s → K :=
  fun k => (((univ : Finset (Fin m)).filter (fun j => t j = FB k)).card : K)

/-- `∑ t_j = ∑_k (mult_k) • FB k` when all `t_j` lie in the (injectively indexed) factor base. -/
theorem sum_eq_countRow {m s : ℕ} (FB : Fin s → G) (hFB : Function.Injective FB)
    (t : Fin m → G) (ht : ∀ j, ∃ k, t j = FB k) :
    ∑ j, t j = ∑ k, countRow (K := K) FB t k • FB k := by
  classical
  choose idx hidx using ht
  have h1 : ∑ j, t j = ∑ j, FB (idx j) := sum_congr rfl (fun j _ => hidx j)
  have h2 : ∀ j, (idx j) ∈ (univ : Finset (Fin s)) := fun _ => mem_univ _
  rw [h1, ← sum_fiberwise_of_maps_to (g := idx) (t := univ) (fun j _ => h2 j)]
  refine sum_congr rfl (fun k _ => ?_)
  have e : ∀ j ∈ (univ : Finset (Fin m)).filter (fun j => idx j = k), FB (idx j) = FB k :=
    fun j hj => by rw [(mem_filter.1 hj).2]
  rw [sum_congr rfl e, sum_const, countRow]
  have : (univ.filter (fun j : Fin m => t j = FB k)) = univ.filter (fun j => idx j = k) := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    rw [hidx j]
    exact ⟨fun h => hFB h, fun h => by rw [h]⟩
  rw [this, ← Nat.cast_smul_eq_nsmul K]

/-- **Correctness of the relation-solving step.**  Rows `R_i = a_i • P + b_i • Q`, `Q = d • P`,
`P` of order exactly `|K|` (`c • P = 0 → c = 0`); `E i` the relation row of `R_i`
(`R_i = ∑_k E i k • FB k` whenever the oracle succeeded); `lam` supported on successful rows with
`lamᵀ E = 0`.  Then `(∑ lam_i b_i) * d = -(∑ lam_i a_i)`; hence if `∑ lam_i b_i ≠ 0`, `d` is recovered. -/
theorem recover_correct {s N : ℕ} (FB : Fin s → G) (P Q : G) (d : K)
    (hP : ∀ c : K, c • P = 0 → c = 0) (hQ : Q = d • P) (a b : Fin N → K)
    (E : Fin N → Fin s → K) (lam : Fin N → K)
    (hrow : ∀ i, lam i ≠ 0 → a i • P + b i • Q = ∑ k, E i k • FB k)
    (hker : ∀ k, ∑ i, lam i * E i k = 0) (hb : ∑ i, lam i * b i ≠ 0) :
    d = -(∑ i, lam i * a i) / (∑ i, lam i * b i) := by
  have h1 : ∑ i, lam i • (a i • P + b i • Q) = ∑ i, lam i • ∑ k, E i k • FB k := by
    refine sum_congr rfl (fun i _ => ?_)
    by_cases h : lam i = 0
    · simp [h]
    · rw [hrow i h]
  have h2 : ∑ i, lam i • ∑ k, E i k • FB k = 0 := by
    simp only [smul_sum, smul_smul]
    rw [sum_comm]
    simp only [← sum_smul, hker, zero_smul, sum_const_zero]
  have h5 : ∑ i, lam i • (a i • P + b i • Q) = (∑ i, lam i * a i + d * ∑ i, lam i * b i) • P := by
    rw [hQ, mul_sum, ← sum_add_distrib, sum_smul]
    refine sum_congr rfl (fun i _ => ?_)
    rw [smul_add, smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1; ring
  have h3 : (∑ i, lam i * a i + d * ∑ i, lam i * b i) • P = 0 := by
    rw [← h5, h1, h2]
  have h4 := hP _ h3
  field_simp
  linear_combination h4

/-- **Correctness with the oracle.**  `D` sound, `FB` injective; rows `R_i = a_i P + b_i Q`;
`E i` = multiplicities of the decomposition `D R_i`; `lam` supported on successful rows, `lamᵀ E = 0`,
`∑ lam_i b_i ≠ 0`.  Then the recovered value is `d`. -/
theorem recover_from_oracle {m s N : ℕ} (D : G → Option (Fin m → G)) (FB : Fin s → G)
    (hD : OracleSound D FB) (hFB : Function.Injective FB) (P Q : G) (d : K)
    (hP : ∀ c : K, c • P = 0 → c = 0) (hQ : Q = d • P) (a b : Fin N → K) (lam : Fin N → K)
    (hsupp : ∀ i, lam i ≠ 0 → (D (a i • P + b i • Q)).isSome)
    (hker : ∀ k, ∑ i, lam i * countRow (K := K) FB ((D (a i • P + b i • Q)).getD (fun _ => 0)) k = 0)
    (hb : ∑ i, lam i * b i ≠ 0) :
    d = -(∑ i, lam i * a i) / (∑ i, lam i * b i) := by
  refine recover_correct FB P Q d hP hQ a b
    (fun i => countRow (K := K) FB ((D (a i • P + b i • Q)).getD (fun _ => 0))) lam ?_ hker hb
  intro i hi
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hsupp i hi)
  obtain ⟨hsum, hmem⟩ := hD _ t ht
  simp only [ht, Option.getD_some]
  rw [← hsum]
  exact sum_eq_countRow FB hFB t hmem

end algebra

section prob
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

/-- The residue vector `c = a + d b` is all the oracle sees; `λ = Λ c` is any function of it. -/
theorem bad_count (d : K) (Λ : (Fin N → K) → Fin N → K) (hΛ : ∀ c, Λ c ≠ 0) :
    (univ.filter (fun ab : (Fin N → K) × (Fin N → K) =>
      ∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i = 0)).card
      = Fintype.card K ^ N * Fintype.card K ^ (N - 1) := by
  classical
  have h := ECDLP.L40.las_vegas_indep (Ω := Fin N → K) Λ hΛ
  have hc : Fintype.card (Fin N → K) = Fintype.card K ^ N := by simp
  rw [hc] at h
  rw [← h]
  refine card_bij (fun ab _ => (fun j => ab.1 j + d * ab.2 j, ab.2)) ?_ ?_ ?_
  · intro ab hab
    simpa using hab
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    refine Prod.ext (funext fun j => ?_) h2
    have := congrFun h1 j
    have h2j := congrFun h2 j
    rw [h2j] at this
    exact add_right_cancel this
  · intro x hx
    refine ⟨(fun j => x.1 j - d * x.2 j, x.2), ?_, ?_⟩
    · simpa using hx
    · simp

/-- probability form: the bad event has probability exactly `1/q` over uniform `(a,b)`. -/
theorem bad_prob (hN : 1 ≤ N) (d : K) (Λ : (Fin N → K) → Fin N → K) (hΛ : ∀ c, Λ c ≠ 0) :
    ((univ.filter (fun ab : (Fin N → K) × (Fin N → K) =>
      ∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i = 0)).card : ℚ)
      / (Fintype.card K : ℚ) ^ (2 * N) = 1 / Fintype.card K := by
  rw [bad_count d Λ hΛ]
  have hq : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_pow]
  rw [show 2 * (k + 1) = (k + 1) + (k + 1) by ring, pow_add]
  field_simp
  ring

/-- **Las Vegas success count.**  If for every residue vector `c` the algorithm's `Λ c` is a
nonzero left-kernel vector of the relation matrix of the rows `c_i • P` supported on successful
rows, then over uniform `(a,b)` the recovered value equals `d` for at least `q^{2N} - q^{2N-1}`
pairs (failure probability exactly `1/q`). -/
theorem las_vegas_success {G : Type*} [AddCommGroup G] [Module K G] {m s : ℕ}
    (D : G → Option (Fin m → G)) (FB : Fin s → G) (hD : OracleSound D FB)
    (hFB : Function.Injective FB) (P Q : G) (d : K)
    (hP : ∀ c : K, c • P = 0 → c = 0) (hQ : Q = d • P)
    (Λ : (Fin N → K) → Fin N → K) (hΛ : ∀ c, Λ c ≠ 0)
    (hsupp : ∀ c i, Λ c i ≠ 0 → (D (c i • P)).isSome)
    (hker : ∀ c k, ∑ i, Λ c i * countRow (K := K) FB ((D (c i • P)).getD (fun _ => 0)) k = 0) :
    Fintype.card K ^ (2 * N) - Fintype.card K ^ N * Fintype.card K ^ (N - 1) ≤
      (univ.filter (fun ab : (Fin N → K) × (Fin N → K) =>
        d = -(∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.1 i)
          / (∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i))).card := by
  classical
  have hres : ∀ (ab : (Fin N → K) × (Fin N → K)) i,
      ab.1 i • P + ab.2 i • Q = (ab.1 i + d * ab.2 i) • P := by
    intro ab i; rw [hQ, smul_smul, add_smul, mul_comm]
  have hsub : (univ.filter (fun ab : (Fin N → K) × (Fin N → K) =>
      ¬ ∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i = 0)) ⊆
      (univ.filter (fun ab : (Fin N → K) × (Fin N → K) =>
        d = -(∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.1 i)
          / (∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i))) := by
    intro ab hab
    simp only [mem_filter, mem_univ, true_and] at hab ⊢
    refine recover_from_oracle D FB hD hFB P Q d hP hQ ab.1 ab.2
      (Λ (fun j => ab.1 j + d * ab.2 j)) ?_ ?_ hab
    · intro i hi
      rw [hres ab i]; exact hsupp _ i hi
    · intro k
      have := hker (fun j => ab.1 j + d * ab.2 j) k
      simpa only [hres ab] using this
  refine le_trans ?_ (card_le_card hsub)
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset ((Fin N → K) × (Fin N → K))))
    (fun ab => ∑ i, Λ (fun j => ab.1 j + d * ab.2 j) i * ab.2 i = 0)
  rw [bad_count d Λ hΛ] at h1
  have h2 : (univ : Finset ((Fin N → K) × (Fin N → K))).card = Fintype.card K ^ (2 * N) := by
    simp [card_univ, Fintype.card_prod, pow_mul, two_mul, pow_add]
  omega

end prob

end ECDLP.L46
