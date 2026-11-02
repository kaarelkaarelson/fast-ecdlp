import Mathlib
import ECDLPv2.L114_Main
import ECDLPv2.L119_WRound

set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L119

open ECDLP.L114 Finset

section main
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **The round-failure budget.**  Failure = not accepted, or the planted block is singular modulo some
large prime, or some lattice phase fails to generate `Rel_ℓ`.  Counting over `ν < ν₀` and all tags. -/
theorem round_failure_leW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0)
    (R : RoundSpecW V hN f s Nd O)
    (hsurj : Function.Surjective (evG V hN))
    (q ℓ v : ι → ℕ) (hq0 : ∀ i, q i ≠ 0) (hpow : ∀ i, q i = ℓ i ^ v i)
    (hprime : ∀ i, (ℓ i).Prime) (hqM : ∀ i, q i * cofac q i = N)
    (hcop : ∀ i, Nat.Coprime (cofac q i) (q i))
    (I : Finset ι) (ν0 : ℕ) (hbig : ∀ i ∈ I, ν0 ≤ ℓ i) (D : ι → ℕ) (hD : ∀ i ∈ I, 0 < D i)
    (hGen : ∀ i ∈ I, haveI : NeZero (q i) := ⟨hq0 i⟩;
      GenBoundW (q i) (evL V hN (hqM i)).ker s (D i)) :
    (((range ν0 ×ˢ (univ : Finset (Fin Nd → (Fin k → ZMod N)))).filter (fun p =>
        ¬ R.Acc (trans (evG V hN) R.Orc (R.shift p.1) [] Nd p.2) ∨
        (∃ l ∈ I.image ℓ, (l : ℤ) ∣ (R.Ttop (trans (evG V hN) R.Orc (R.shift p.1) [] Nd p.2) -
          Matrix.scalar (Fin f) (p.1 : ℤ)).det) ∨
        ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) ≤
      ((range ν0 ×ˢ (univ : Finset (Fin Nd → (Fin k → ZMod N)))).filter (fun p =>
        ¬ R.Acc (trans (evG V hN) R.Orc (R.shift p.1) [] Nd p.2))).card +
      (I.card * f : ℕ) * Fintype.card (Fin Nd → (Fin k → ZMod N)) +
      (∑ i ∈ I, (1 : ℚ) / D i) * (ν0 * Fintype.card (Fin Nd → (Fin k → ZMod N))) := by
  set Ω := Fin Nd → (Fin k → ZMod N) with hΩ
  set ev := evG V hN with hev
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
        ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) ≤
      (∑ i ∈ I, (1 : ℚ) / D i) * (ν0 * Fintype.card Ω) := by
    simp only [Pairs]
    rw [pairs_card ν0 (fun ν a => (R.Acc (tr ν a) ∧ ¬ Bad ν a) ∧
      ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (ν : ℤ) a)]
    push_cast
    have hν : ∀ ν ∈ range ν0, ((univ.filter (fun a : Ω => (R.Acc (tr ν a) ∧ ¬ Bad ν a) ∧
        ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (ν : ℤ) a)).card : ℚ) ≤
        (∑ i ∈ I, (1 : ℚ) / D i) * Fintype.card Ω := by
      intro ν _
      have key := lf_bound (fun a : Ω => fun t => ev (a t)) (fun a => R.Acc (tr ν a) ∧ ¬ Bad ν a) I
        (fun i a => GoodAtW V hN R q i (hqM i) (ν : ℤ) a) D hD
        (fun a a' haa => by
          have : tr ν a = tr ν a' :=
            trans_eq_of_ev_eq ev R.Orc _ Nd [] a a' (fun t => congrFun haa t)
          simp only [Bad, this])
        (fun i hi => by
          haveI : NeZero (q i) := ⟨hq0 i⟩
          refine good_fibre_boundW V hN R hsurj q i (hqM i) (hcop i) (D i) (hGen i hi) (ν : ℤ)
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
        ¬ R.Acc (tr p.1 p.2) ∨ Bad p.1 p.2 ∨ ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)) ⊆
      (Pairs.filter (fun p => ¬ R.Acc (tr p.1 p.2))) ∪ (Pairs.filter (fun p => Bad p.1 p.2)) ∪
      (Pairs.filter (fun p => (R.Acc (tr p.1 p.2) ∧ ¬ Bad p.1 p.2) ∧
        ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)) := by
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
        ¬ R.Acc (tr p.1 p.2) ∨ Bad p.1 p.2 ∨ ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℕ) : ℚ) ≤
      ((Pairs.filter (fun p => ¬ R.Acc (tr p.1 p.2))).card : ℚ) +
      ((Pairs.filter (fun p => Bad p.1 p.2)).card : ℚ) +
      ((Pairs.filter (fun p => (R.Acc (tr p.1 p.2) ∧ ¬ Bad p.1 p.2) ∧
        ∃ i ∈ I, ¬ GoodAtW V hN R q i (hqM i) (p.1 : ℤ) p.2)).card : ℚ) := by
    exact_mod_cast c1
  have hA2' : ((Pairs.filter (fun p => Bad p.1 p.2)).card : ℚ) ≤
      ((I.card * f : ℕ) : ℚ) * Fintype.card Ω := by exact_mod_cast hA2
  show ((Pairs.filter _).card : ℚ) ≤ _
  linarith


end main
end ECDLP.L119
