import Mathlib
import ECDLPv2.L114_Phase

/-!
# L114 / Gen: exact conditional success probability of the lattice phase

From the uniformity `phase_unif` (S1): conditionally on the draw points `T`, the event that the `s`
lattice vectors satisfy any property `Gd` (e.g. "they generate `Rel_ℓ`") has *exactly* the probability
`#{m ∈ Rel_ℓ^s | Gd m} / |Rel_ℓ|^s`, independent of `T`, of the transcript and of `ν`.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

theorem fiber_split {X Y : Type*} [DecidableEq Y] (Xs : Finset X) (Φ : X → Y) (S : Finset Y)
    (hmaps : ∀ x ∈ Xs, Φ x ∈ S) (c : ℕ)
    (hc : ∀ m ∈ S, (Xs.filter (fun x => Φ x = m)).card = c) (Gd : Y → Prop) [DecidablePred Gd] :
    Xs.card = c * S.card ∧ (Xs.filter (fun x => Gd (Φ x))).card = c * (S.filter Gd).card := by
  constructor
  · rw [Finset.card_eq_sum_card_fiberwise (f := Φ) (t := S) hmaps, Finset.sum_congr rfl hc]
    simp [mul_comm]
  · have h1 : ∀ x ∈ Xs.filter (fun x => Gd (Φ x)), Φ x ∈ S.filter Gd := by
      intro x hx
      rw [mem_filter] at hx
      exact mem_filter.2 ⟨hmaps x hx.1, hx.2⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := Φ) (t := S.filter Gd) h1]
    have : ∀ m ∈ S.filter Gd, ((Xs.filter (fun x => Gd (Φ x))).filter (fun x => Φ x = m)).card = c := by
      intro m hm
      rw [mem_filter] at hm
      rw [← hc m hm.1]
      congr 1
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hm.2⟩, h3⟩
    rw [Finset.sum_congr rfl this]
    simp [mul_comm]

section gen
variable {G : Type*} [AddCommGroup G] {N q M f s : ℕ} [NeZero N] [NeZero q]
  {κd : Type*} [Fintype κd]

open Classical in
/-- **Exact success probability of the lattice phase.**  With `K = Rel_ℓ`, `Fibre = {a : ev a_t = T t ∀t}`:
`#Fibre = c * |K|^s` and `#{a ∈ Fibre | Gd (μ(a))} = c * #{m ∈ K^s | Gd m}`. -/
theorem phase_gen (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (hcop : Nat.Coprime M q)
    (hsurj : Function.Surjective (evG ![H1, H2, P, Q] hN))
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (hpos : Function.Injective pos) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (Gd : (Fin s → (Fin 4 → ZMod q)) → Prop) [DecidablePred Gd] :
    ∃ c : ℕ,
      (univ.filter (fun a : κd → (Fin 4 → ZMod N) =>
        ∀ t, evG ![H1, H2, P, Q] hN (a t) = T t)).card =
        c * (Fintype.card ((evL ![H1, H2, P, Q] hN hqM).ker)) ^ s ∧
      (univ.filter (fun a : κd → (Fin 4 → ZMod N) =>
        (∀ t, evG ![H1, H2, P, Q] hN (a t) = T t) ∧
        Gd (combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i))))).card =
        c * ((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin 4 → ZMod q => x ∈ (evL ![H1, H2, P, Q] hN hqM).ker)))).filter Gd).card := by
  set K := (evL ![H1, H2, P, Q] hN hqM).ker with hK
  set Kfin : Finset (Fin 4 → ZMod q) := univ.filter (fun x => x ∈ K) with hKfin
  set S := Fintype.piFinset (fun _ : Fin s => Kfin) with hS
  set Xs := (univ.filter (fun a : κd → (Fin 4 → ZMod N) => ∀ t, evG ![H1, H2, P, Q] hN (a t) = T t)) with hXs
  set Φ : (κd → (Fin 4 → ZMod N)) → (Fin s → (Fin 4 → ZMod q)) :=
    fun a => combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) with hΦ
  have hmaps : ∀ a ∈ Xs, Φ a ∈ S := by
    intro a ha
    rw [hXs, mem_filter] at ha
    rw [hS, Fintype.mem_piFinset]
    intro j
    rw [hKfin, mem_filter]
    exact ⟨mem_univ _, phase_mem H1 H2 P Q hN hqM FB Ttop Rint ν hB pos T hrow a ha.2 j⟩
  have hmem : ∀ m ∈ S, ∀ j, m j ∈ K := by
    intro m hm j
    rw [hS, Fintype.mem_piFinset] at hm
    have := hm j
    rw [hKfin, mem_filter] at this
    exact this.2
  have h0 : (0 : Fin s → (Fin 4 → ZMod q)) ∈ S := by
    rw [hS, Fintype.mem_piFinset]; intro j
    rw [hKfin, mem_filter]; exact ⟨mem_univ _, K.zero_mem⟩
  refine ⟨(Xs.filter (fun a => Φ a = 0)).card, ?_⟩
  have hc : ∀ m ∈ S, (Xs.filter (fun a => Φ a = m)).card = (Xs.filter (fun a => Φ a = 0)).card := by
    intro m hm
    have := phase_unif H1 H2 P Q hN hqM hcop hsurj FB Ttop Rint ν hB pos hpos T hrow m 0
      (hmem m hm) (hmem 0 h0)
    simpa [hXs, Finset.filter_filter] using this
  obtain ⟨e1, e2⟩ := fiber_split Xs Φ S hmaps _ hc Gd
  have hcard : S.card = (Fintype.card K) ^ s := by
    rw [hS, Fintype.card_piFinset]
    simp [hKfin, Fintype.card_subtype]
  refine ⟨?_, ?_⟩
  · rw [e1, hcard]
  · rw [← e2]
    congr 1
    ext a
    simp [hXs, Finset.filter_filter]
    exact fun _ => Iff.rfl

end gen
end ECDLP.L114
