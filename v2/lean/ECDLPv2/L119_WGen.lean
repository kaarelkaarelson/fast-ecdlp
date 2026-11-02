import Mathlib
import ECDLPv2.L114_Gen
import ECDLPv2.L119_WPhase

set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L119

open ECDLP.L114 Finset

section gen
variable {G : Type*} [AddCommGroup G] {N q M f s : ℕ} [NeZero N] [NeZero q]
  {κd : Type*} [Fintype κd]

open Classical in
/-- **Exact success probability of the lattice phase.**  With `K = Rel_ℓ`, `Fibre = {a : ev a_t = T t ∀t}`:
`#Fibre = c * |K|^s` and `#{a ∈ Fibre | Gd (μ(a))} = c * #{m ∈ K^s | Gd m}`. -/
theorem phase_genW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (hcop : Nat.Coprime M q)
    (hsurj : Function.Surjective (evG V hN))
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (hpos : Function.Injective pos) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (Gd : (Fin s → (Fin k → ZMod q)) → Prop) [DecidablePred Gd] :
    ∃ c : ℕ,
      (univ.filter (fun a : κd → (Fin k → ZMod N) =>
        ∀ t, evG V hN (a t) = T t)).card =
        c * (Fintype.card ((evL V hN hqM).ker)) ^ s ∧
      (univ.filter (fun a : κd → (Fin k → ZMod N) =>
        (∀ t, evG V hN (a t) = T t) ∧
        Gd (combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i))))).card =
        c * ((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin k → ZMod q => x ∈ (evL V hN hqM).ker)))).filter Gd).card := by
  set K := (evL V hN hqM).ker with hK
  set Kfin : Finset (Fin k → ZMod q) := univ.filter (fun x => x ∈ K) with hKfin
  set S := Fintype.piFinset (fun _ : Fin s => Kfin) with hS
  set Xs := (univ.filter (fun a : κd → (Fin k → ZMod N) => ∀ t, evG V hN (a t) = T t)) with hXs
  set Φ : (κd → (Fin k → ZMod N)) → (Fin s → (Fin k → ZMod q)) :=
    fun a => combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) with hΦ
  have hmaps : ∀ a ∈ Xs, Φ a ∈ S := by
    intro a ha
    rw [hXs, mem_filter] at ha
    rw [hS, Fintype.mem_piFinset]
    intro j
    rw [hKfin, mem_filter]
    exact ⟨mem_univ _, phase_memW V hN hqM FB Ttop Rint ν hB pos T hrow a ha.2 j⟩
  have hmem : ∀ m ∈ S, ∀ j, m j ∈ K := by
    intro m hm j
    rw [hS, Fintype.mem_piFinset] at hm
    have := hm j
    rw [hKfin, mem_filter] at this
    exact this.2
  have h0 : (0 : Fin s → (Fin k → ZMod q)) ∈ S := by
    rw [hS, Fintype.mem_piFinset]; intro j
    rw [hKfin, mem_filter]; exact ⟨mem_univ _, K.zero_mem⟩
  refine ⟨(Xs.filter (fun a => Φ a = 0)).card, ?_⟩
  have hc : ∀ m ∈ S, (Xs.filter (fun a => Φ a = m)).card = (Xs.filter (fun a => Φ a = 0)).card := by
    intro m hm
    have := phase_unifW V hN hqM hcop hsurj FB Ttop Rint ν hB pos hpos T hrow m 0
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
end ECDLP.L119
