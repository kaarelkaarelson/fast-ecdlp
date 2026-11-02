import Mathlib

/-!
# L114 / Plant: (b) planted-diagonal invertibility

`T'` an integer `f × f` matrix (the answers of the oracle on the planted rows; by P1 its law does not
depend on the planted multiplier `ν`).  The top block of the relation matrix is `B = T' - ν I`.
* `det_sub_scalar` : `det (T' - ν I) = (-1)^f * charpoly(T')(ν)`;  the charpoly is monic of degree `f`.
* `bad_nu_le` : for a prime `ℓ ≥ ν₀`, at most `f` values `ν ∈ [0, ν₀)` have `ℓ ∣ det (T' - ν I)`.
* `bad_nu_union` : for a set `Ls` of primes `≥ ν₀`, at most `|Ls| * f` values of `ν` are bad for some `ℓ ∈ Ls`.
* `isUnit_of_not_dvd` : if `ℓ ∤ det` then the block is invertible over `Z/ℓ^v`.
* `planted_kernel` : with `B` invertible, `Λ = (-R B⁻¹ | I)` satisfies `Λ · [B; R] = 0` and `Λ · [0; I] = I`.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
namespace ECDLP.L114

open Finset Polynomial

section charpoly
variable {f : ℕ}

theorem det_sub_scalar (T : Matrix (Fin f) (Fin f) ℤ) (ν : ℤ) :
    (T - Matrix.scalar (Fin f) ν).det = (-1) ^ f * T.charpoly.eval ν := by
  rw [Matrix.eval_charpoly, ← neg_sub, Matrix.det_neg]
  simp

theorem charpoly_dvd_iff (T : Matrix (Fin f) (Fin f) ℤ) (ℓ : ℕ) (ν : ℤ) :
    (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) ν).det ↔ (ℓ : ℤ) ∣ T.charpoly.eval ν := by
  rw [det_sub_scalar]
  constructor
  · intro h
    have := (Dvd.dvd.mul_left h ((-1) ^ f))
    have e : ((-1 : ℤ) ^ f) * ((-1) ^ f * T.charpoly.eval ν) = T.charpoly.eval ν := by
      rw [← mul_assoc, ← mul_pow]; simp
    rwa [e] at this
  · intro h; exact Dvd.dvd.mul_left h _

/-- for a prime `ℓ ≥ ν₀`, at most `f` values `ν < ν₀` make `ℓ ∣ det (T' - ν I)`. -/
theorem bad_nu_le (T : Matrix (Fin f) (Fin f) ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (ν0 : ℕ) (hle : ν0 ≤ ℓ) :
    ((range ν0).filter (fun ν : ℕ => (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)).card ≤ f := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set χ : (ZMod ℓ)[X] := T.charpoly.map (Int.castRingHom (ZMod ℓ)) with hχ
  have hmon : χ.Monic := (Matrix.charpoly_monic T).map _
  have hdeg : χ.natDegree = f := by
    rw [hχ, (Matrix.charpoly_monic T).natDegree_map, Matrix.charpoly_natDegree_eq_dim]; simp
  have hne : χ ≠ 0 := hmon.ne_zero
  have hsub : ((range ν0).filter (fun ν : ℕ => (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)).card
      ≤ χ.roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun ν : ℕ => ((ν : ℤ) : ZMod ℓ)) ?_ ?_
    · intro ν hν
      simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hν
      simp only [coe_filter, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      rw [hχ, Polynomial.eval_intCast_map]
      simp only [eq_intCast, Int.cast_natCast] at *
      have := (charpoly_dvd_iff T ℓ ν).1 hν.2
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_setOf_eq, mem_range] at ha hb
      simp only [Int.cast_natCast] at hab
      exact (ZMod.natCast_eq_natCast_iff' a b ℓ).1 hab |> fun h =>
        by rw [Nat.mod_eq_of_lt (lt_of_lt_of_le ha.1 hle), Nat.mod_eq_of_lt (lt_of_lt_of_le hb.1 hle)] at h; exact h
  refine hsub.trans ?_
  exact (Multiset.toFinset_card_le _).trans ((card_roots' χ).trans hdeg.le)

theorem bad_nu_union (T : Matrix (Fin f) (Fin f) ℤ) (Ls : Finset ℕ) (hp : ∀ ℓ ∈ Ls, ℓ.Prime)
    (ν0 : ℕ) (hbig : ∀ ℓ ∈ Ls, ν0 ≤ ℓ) :
    ((range ν0).filter (fun ν : ℕ => ∃ ℓ ∈ Ls,
      (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)).card ≤ Ls.card * f := by
  classical
  have : (range ν0).filter (fun ν : ℕ => ∃ ℓ ∈ Ls, (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)
      = Ls.biUnion (fun ℓ => (range ν0).filter
          (fun ν : ℕ => (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)) := by
    ext ν; simp only [mem_filter, mem_biUnion]; constructor
    · rintro ⟨h1, ℓ, h2, h3⟩; exact ⟨ℓ, h2, h1, h3⟩
    · rintro ⟨ℓ, h2, h1, h3⟩; exact ⟨h1, ℓ, h2, h3⟩
  rw [this]
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ ℓ ∈ Ls, ((range ν0).filter (fun ν : ℕ => (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) (ν : ℤ)).det)).card
      ≤ ∑ _ℓ ∈ Ls, f := Finset.sum_le_sum fun ℓ hℓ => bad_nu_le T ℓ (hp ℓ hℓ) ν0 (hbig ℓ hℓ)
    _ = Ls.card * f := by simp

end charpoly

section unit
/-- if the prime `ℓ` does not divide `D`, then `D` is a unit modulo `ℓ^v`. -/
theorem isUnit_of_not_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (v : ℕ) (D : ℤ) (h : ¬ (ℓ : ℤ) ∣ D) :
    IsUnit ((D : ℤ) : ZMod (ℓ ^ v)) := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
  have hc : IsCoprime (ℓ : ℤ) D := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 h
  obtain ⟨a, b, hab⟩ := (hc.pow_left (m := v))
  have : ((a * (ℓ : ℤ) ^ v + b * D : ℤ) : ZMod (ℓ ^ v)) = 1 := by rw [hab]; simp
  push_cast at this
  have h0 : ((ℓ : ZMod (ℓ ^ v)) ^ v) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [h0, mul_zero, zero_add] at this
  exact IsUnit.of_mul_eq_one (b : ZMod (ℓ ^ v)) (by rw [mul_comm]; exact this)

/-- the planted block `T' - ν I` reduced mod `ℓ^v` is invertible when `ℓ ∤ det`. -/
theorem block_isUnit {f : ℕ} (T : Matrix (Fin f) (Fin f) ℤ) (ν : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (v : ℕ)
    (h : ¬ (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) ν).det) :
    IsUnit (((T - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod (ℓ ^ v)))).det) := by
  have := isUnit_of_not_dvd ℓ hℓ v _ h
  have e : (((T - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod (ℓ ^ v)))).det) =
      (((T - Matrix.scalar (Fin f) ν).det : ℤ) : ZMod (ℓ ^ v)) := by
    rw [← eq_intCast (Int.castRingHom (ZMod (ℓ ^ v))), RingHom.map_det]; rfl
  rw [e]; exact this
end unit

section kernel
variable {S : Type*} [CommRing S] {f s : ℕ}

/-- **kernel vectors from an invertible planted block.**  Rows `[B; R]` (planted block on top,
ordinary rows below).  `Λ = (-R B⁻¹ | I)` annihilates the matrix and has the right inverse `[0; I]`. -/
theorem planted_kernel (B : Matrix (Fin f) (Fin f) S) (hB : IsUnit B.det) (Rr : Matrix (Fin s) (Fin f) S) :
    Matrix.fromCols (-(Rr * B⁻¹)) (1 : Matrix (Fin s) (Fin s) S) * Matrix.fromRows B Rr = 0 ∧
    Matrix.fromCols (-(Rr * B⁻¹)) (1 : Matrix (Fin s) (Fin s) S) *
      Matrix.fromRows (0 : Matrix (Fin f) (Fin s) S) (1 : Matrix (Fin s) (Fin s) S) = 1 := by
  constructor
  · rw [Matrix.fromCols_mul_fromRows, Matrix.neg_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB]
    simp
  · rw [Matrix.fromCols_mul_fromRows]; simp
end kernel

section dbl
variable {Ω W : Type*} [Fintype Ω] [DecidableEq W]

/-- **Double counting for the "bad `ν`" event.**  If the law of the transcript `τ ν a` does not depend
on `ν` (P1) and for every transcript `w` at most `Bd` values of `ν < ν₀` are bad, then the number of
pairs `(ν, a)` that are bad is at most `Bd * |Ω|`; i.e. the bad probability is `≤ Bd / ν₀`. -/
theorem double_count (ν0 : ℕ) (τ : ℕ → Ω → W)
    (hτ : ∀ ν ν' w, (univ.filter fun a => τ ν a = w).card = (univ.filter fun a => τ ν' a = w).card)
    (bad : W → ℕ → Prop) [∀ w ν, Decidable (bad w ν)] (Bd : ℕ)
    (hbad : ∀ w, ((range ν0).filter (bad w)).card ≤ Bd) :
    ((range ν0 ×ˢ (univ : Finset Ω)).filter (fun p => bad (τ p.1 p.2) p.1)).card ≤ Bd * Fintype.card Ω := by
  classical
  set Wset : Finset W := univ.image (τ 0) with hW
  set c : W → ℕ := fun w => (univ.filter fun a => τ 0 a = w).card with hc
  have hmem : ∀ ν a, τ ν a ∈ Wset := by
    intro ν a
    have h1 : 0 < (univ.filter fun a' => τ ν a' = τ ν a).card :=
      Finset.card_pos.2 ⟨a, by simp⟩
    rw [hτ ν 0] at h1
    obtain ⟨a', ha'⟩ := Finset.card_pos.1 h1
    simp only [mem_filter, mem_univ, true_and] at ha'
    exact Finset.mem_image.2 ⟨a', mem_univ _, ha'⟩
  have hfib : ∀ ν, (univ.filter fun a => bad (τ ν a) ν).card =
      ∑ w ∈ Wset, if bad w ν then c w else 0 := by
    intro ν
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a => τ ν a) (t := Wset)
      (fun a _ => hmem ν a)]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hb : bad w ν
    · rw [if_pos hb]
      have : (univ.filter fun a => bad (τ ν a) ν).filter (fun a => τ ν a = w) =
          univ.filter fun a => τ ν a = w := by
        ext a; simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨h ▸ hb, h⟩
      rw [this, hτ ν 0]
    · rw [if_neg hb]
      refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a ha => ?_)
      simp only [mem_filter, mem_univ, true_and] at ha
      exact hb (ha.2 ▸ ha.1)
  have hsum : ∑ w ∈ Wset, c w = Fintype.card Ω := by
    rw [← Finset.card_univ]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a => τ 0 a) (t := Wset) (fun a _ => hmem 0 a)]
  rw [Finset.card_filter, Finset.sum_product]
  have : ∀ ν, (∑ a : Ω, if bad (τ ν a) ν then 1 else 0) = ∑ w ∈ Wset, if bad w ν then c w else 0 := by
    intro ν; rw [← hfib ν, Finset.card_filter]
  simp only [this]
  rw [Finset.sum_comm]
  calc ∑ w ∈ Wset, ∑ ν ∈ range ν0, (if bad w ν then c w else 0)
      = ∑ w ∈ Wset, c w * ((range ν0).filter (bad w)).card := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ w ∈ Wset, c w * Bd := Finset.sum_le_sum fun w _ => Nat.mul_le_mul_left _ (hbad w)
    _ = Bd * Fintype.card Ω := by rw [← Finset.sum_mul, hsum, mul_comm]
end dbl

end ECDLP.L114
