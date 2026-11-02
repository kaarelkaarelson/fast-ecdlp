import Mathlib
import ECDLPv2.L114_Round

/-!
# L114 / Main: the round-failure budget and the correctness of a successful round

* `howell_localSol` : at a prime power whose lattice vectors generate `Rel_ℓ`, any Howell decision
  procedure returns a local discrete log (completeness) and only local discrete logs (soundness).
* `round_failure_le` : in the finite space `[0,ν₀) × (tags)`,
  `#fail ≤ #¬Acc + |I|·f·|Ω| + (∑_{i∈I} 1/D_i)·ν₀·|Ω|`
  where the three terms are the acceptance/cap event (hypothesis H1), the planted-block singularity
  (Schwartz–Zippel on the monic charpoly + P1) and the generation failure of the lattices (S1 + `GenBound`).
* `round_output` : outside the failure event, the final CRT value satisfies `o • P = Q`.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

section main
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the specification of the Howell procedure (paper Lemma `howell`, an elementary polynomial-time
algorithm): it decides whether some `(0,0,z,-1)` lies in the span of the vectors and returns such a `z`. -/
def HowellSpec {q : ℕ} (μ : Fin s → Fin 4 → ZMod q) (r : Option ℤ) : Prop :=
  (∀ z, r = some z → (![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) ∈ AddSubgroup.closure (Set.range μ)) ∧
  (r = none → ¬ ∃ z : ℤ, (![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) ∈ AddSubgroup.closure (Set.range μ))

theorem howell_localSol (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (q : ι → ℕ) (i : ι)
    [NeZero (q i)] (hq : q i * cofac q i = N) (μ : Fin s → Fin 4 → ZMod (q i))
    (hgood : AddSubgroup.closure (Set.range μ) = (evL ![H1, H2, P, Q] hN hq).ker)
    (d : ℤ) (hQ : Q = d • P) (r : Option ℤ) (hr : HowellSpec μ r) :
    ∃ z, r = some z ∧ LocalSol (q := q) P Q i z := by
  have htrue := true_relation_mem H1 H2 P Q hN hq d hQ
  rw [← hgood] at htrue
  cases hr' : r with
  | none => exact absurd ⟨d, htrue⟩ (hr.2 hr')
  | some z =>
    refine ⟨z, rfl, ?_⟩
    have hz := hr.1 z hr'
    rw [hgood, AddMonoidHom.mem_ker, evL_four] at hz
    exact hz

theorem block_isUnit' {f : ℕ} (T : Matrix (Fin f) (Fin f) ℤ) (ν : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (v q : ℕ)
    (hq : q = ℓ ^ v) (h : ¬ (ℓ : ℤ) ∣ (T - Matrix.scalar (Fin f) ν).det) :
    IsUnit (((T - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det) := by
  subst hq; exact block_isUnit T ν ℓ hℓ v h

open Classical in
theorem pairs_card {Ω : Type*} [Fintype Ω] (ν0 : ℕ) (S : ℕ → Ω → Prop)
    [DecidablePred (fun p : ℕ × Ω => S p.1 p.2)] :
    ((range ν0 ×ˢ (univ : Finset Ω)).filter (fun p => S p.1 p.2)).card =
      ∑ ν ∈ range ν0, (univ.filter (fun a => S ν a)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : S ν y <;> simp [h]

open Classical in
/-- **The round-failure budget.**  Failure = not accepted, or the planted block is singular modulo some
large prime, or some lattice phase fails to generate `Rel_ℓ`.  Counting over `ν < ν₀` and all tags. -/
theorem round_failure_le (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0)
    (R : RoundSpec ![H1, H2, P, Q] hN f s Nd O)
    (hsurj : Function.Surjective (evG ![H1, H2, P, Q] hN))
    (q ℓ v : ι → ℕ) (hq0 : ∀ i, q i ≠ 0) (hpow : ∀ i, q i = ℓ i ^ v i)
    (hprime : ∀ i, (ℓ i).Prime) (hqM : ∀ i, q i * cofac q i = N)
    (hcop : ∀ i, Nat.Coprime (cofac q i) (q i))
    (I : Finset ι) (ν0 : ℕ) (hbig : ∀ i ∈ I, ν0 ≤ ℓ i) (D : ι → ℕ) (hD : ∀ i ∈ I, 0 < D i)
    (hGen : ∀ i ∈ I, haveI : NeZero (q i) := ⟨hq0 i⟩;
      GenBound (q i) (evL ![H1, H2, P, Q] hN (hqM i)).ker s (D i)) :
    (((range ν0 ×ˢ (univ : Finset (Fin Nd → (Fin 4 → ZMod N)))).filter (fun p =>
        ¬ R.Acc (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift p.1) [] Nd p.2) ∨
        (∃ l ∈ I.image ℓ, (l : ℤ) ∣ (R.Ttop (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift p.1) [] Nd p.2) -
          Matrix.scalar (Fin f) (p.1 : ℤ)).det) ∨
        ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) ≤
      ((range ν0 ×ˢ (univ : Finset (Fin Nd → (Fin 4 → ZMod N)))).filter (fun p =>
        ¬ R.Acc (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift p.1) [] Nd p.2))).card +
      (I.card * f : ℕ) * Fintype.card (Fin Nd → (Fin 4 → ZMod N)) +
      (∑ i ∈ I, (1 : ℚ) / D i) * (ν0 * Fintype.card (Fin Nd → (Fin 4 → ZMod N))) := by
  set Ω := Fin Nd → (Fin 4 → ZMod N) with hΩ
  set ev := evG ![H1, H2, P, Q] hN with hev
  let tr : ℕ → Ω → List O := fun ν a => trans ev R.Orc (R.shift (ν : ℤ)) [] Nd a
  let Bad : ℕ → Ω → Prop := fun ν a => ∃ l ∈ I.image ℓ,
    (l : ℤ) ∣ (R.Ttop (tr ν a) - Matrix.scalar (Fin f) (ν : ℤ)).det
  let Pairs : Finset (ℕ × Ω) := range ν0 ×ˢ (univ : Finset Ω)
  -- A1 : not accepted
  -- A2 : bad
  have hA2 : (Pairs.filter (fun p => Bad p.1 p.2)).card ≤ I.card * f * Fintype.card Ω := by
    have := double_count ν0 (fun ν a => tr ν a)
      (fun ν ν' w => by
        have := trans_count_indep ev hsurj R.Orc (R.shift (ν : ℤ)) (R.shift (ν' : ℤ)) Nd [] w
        exact this)
      (fun w ν => ∃ l ∈ I.image ℓ, (l : ℤ) ∣ (R.Ttop w - Matrix.scalar (Fin f) (ν : ℤ)).det)
      (I.card * f)
      (fun w => by
        refine (bad_nu_union (R.Ttop w) (I.image ℓ) ?_ ν0 ?_).trans ?_
        · intro l hl; obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hl; exact hprime i
        · intro l hl; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hl; exact hbig i hi
        · exact Nat.mul_le_mul_right _ Finset.card_image_le)
    convert this using 1
  -- A3 : lattice failure
  have hA3 : ((Pairs.filter (fun p => (R.Acc (tr p.1 p.2) ∧ ¬ Bad p.1 p.2) ∧
        ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) ≤
      (∑ i ∈ I, (1 : ℚ) / D i) * (ν0 * Fintype.card Ω) := by
    simp only [Pairs]
    rw [pairs_card ν0 (fun ν a => (R.Acc (tr ν a) ∧ ¬ Bad ν a) ∧
      ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (ν : ℤ) a)]
    push_cast
    have hν : ∀ ν ∈ range ν0, ((univ.filter (fun a : Ω => (R.Acc (tr ν a) ∧ ¬ Bad ν a) ∧
        ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (ν : ℤ) a)).card : ℚ) ≤
        (∑ i ∈ I, (1 : ℚ) / D i) * Fintype.card Ω := by
      intro ν _
      have key := lf_bound (fun a : Ω => fun t => ev (a t)) (fun a => R.Acc (tr ν a) ∧ ¬ Bad ν a) I
        (fun i a => GoodAt H1 H2 P Q hN R q i (hqM i) (ν : ℤ) a) D hD
        (fun a a' haa => by
          have : tr ν a = tr ν a' :=
            trans_eq_of_ev_eq ev R.Orc _ Nd [] a a' (fun t => congrFun haa t)
          simp only [Bad, this])
        (fun i hi => by
          haveI : NeZero (q i) := ⟨hq0 i⟩
          refine good_fibre_bound H1 H2 P Q hN R hsurj q i (hqM i) (hcop i) (D i) (hGen i hi) (ν : ℤ)
            (fun a => R.Acc (tr ν a) ∧ ¬ Bad ν a) ?_
          intro a ha
          refine ⟨ha.1, block_isUnit' _ _ (ℓ i) (hprime i) (v i) (q i) (hpow i) ?_⟩
          intro hdvd
          exact ha.2 ⟨ℓ i, Finset.mem_image_of_mem _ hi, hdvd⟩)
      refine key.trans ?_
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_univ _)
        (Finset.sum_nonneg fun i _ => by positivity)
    have hs := Finset.sum_le_sum hν
    have hs2 : ∑ ν ∈ range ν0, (∑ i ∈ I, (1 : ℚ) / D i) * Fintype.card Ω =
        (∑ i ∈ I, (1 : ℚ) / D i) * (ν0 * Fintype.card Ω) := by simp; ring
    rw [hs2] at hs
    convert hs using 2
    congr!
  have hsub : (Pairs.filter (fun p =>
        ¬ R.Acc (tr p.1 p.2) ∨ Bad p.1 p.2 ∨ ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)) ⊆
      (Pairs.filter (fun p => ¬ R.Acc (tr p.1 p.2))) ∪ (Pairs.filter (fun p => Bad p.1 p.2)) ∪
      (Pairs.filter (fun p => (R.Acc (tr p.1 p.2) ∧ ¬ Bad p.1 p.2) ∧
        ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)) := by
    intro p hp
    simp only [mem_filter, mem_union] at hp ⊢
    obtain ⟨hpP, h⟩ := hp
    by_cases h1 : R.Acc (tr p.1 p.2)
    · by_cases h2 : Bad p.1 p.2
      · exact Or.inl (Or.inr ⟨hpP, h2⟩)
      · rcases h with h | h | h
        · exact absurd h1 h
        · exact absurd h h2
        · exact Or.inr ⟨hpP, ⟨h1, h2⟩, h⟩
    · exact Or.inl (Or.inl ⟨hpP, h1⟩)
  have c1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have c2 : (((Pairs.filter (fun p =>
        ¬ R.Acc (tr p.1 p.2) ∨ Bad p.1 p.2 ∨ ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℕ) : ℚ) ≤
      ((Pairs.filter (fun p => ¬ R.Acc (tr p.1 p.2))).card : ℚ) +
      ((Pairs.filter (fun p => Bad p.1 p.2)).card : ℚ) +
      ((Pairs.filter (fun p => (R.Acc (tr p.1 p.2) ∧ ¬ Bad p.1 p.2) ∧
        ∃ i ∈ I, ¬ GoodAt H1 H2 P Q hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) := by
    exact_mod_cast c1
  have hA2' : ((Pairs.filter (fun p => Bad p.1 p.2)).card : ℚ) ≤
      ((I.card * f : ℕ) : ℚ) * Fintype.card Ω := by exact_mod_cast hA2
  show ((Pairs.filter _).card : ℚ) ≤ _
  linarith

/-- **Correctness of a successful round.**  If at every large prime the lattice vectors generate `Rel_ℓ`
(`GoodAt`), the Howell procedure is run on them, and the small primes are handled by Pohlig–Hellman,
then the algorithm's end-to-end output exists and is a discrete logarithm: `o • P = Q`. -/
theorem round_output (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0)
    (R : RoundSpec ![H1, H2, P, Q] hN f s Nd O)
    (q : ι → ℕ) (hq0 : ∀ i, q i ≠ 0) (hpair : Pairwise (Function.onFun Nat.Coprime q))
    (hNprod : N = ∏ j, q j) (hqM : ∀ i, q i * cofac q i = N)
    (d : ℤ) (hQ : Q = d • P) (ν : ℤ) (a : Fin Nd → (Fin 4 → ZMod N)) (I : Finset ι)
    (hGood : ∀ i ∈ I, GoodAt H1 H2 P Q hN R q i (hqM i) ν a)
    (res : ι → Option ℤ)
    (hHow : ∀ i ∈ I, HowellSpec (combHom (rho (Dvd.intro _ (hqM i)))
      (kerMat (q i) (R.Ttop (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a))
        (R.Rint (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a)) ν)
      (fun r => a (R.pos (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a) r))) (res i))
    (hPH : ∀ i, i ∉ I → ∃ z, res i = some z ∧ (addOrderOf (cofac q i • P) : ℤ) ∣ z - d) :
    ∃ o, runFinal q P Q res = some o ∧ o • P = Q := by
  have hN' : ∀ g : G, (∏ j, q j) • g = 0 := by rw [← hNprod]; exact hN
  refine runFinal_complete hq0 hpair hN' P Q res (fun i => ?_)
  by_cases hi : i ∈ I
  · haveI : NeZero (q i) := ⟨hq0 i⟩
    exact howell_localSol H1 H2 P Q hN q i (hqM i) _ (hGood i hi) d hQ (res i) (hHow i hi)
  · obtain ⟨z, hz, hdvd⟩ := hPH i hi
    exact ⟨z, hz, localSol_of_ph P Q i d z hQ hdvd⟩

end main
end ECDLP.L114
