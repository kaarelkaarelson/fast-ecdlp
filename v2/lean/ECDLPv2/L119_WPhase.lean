import Mathlib
import ECDLPv2.L114_Phase

set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L119

open ECDLP.L114 Finset

section phase
variable {G : Type*} [AddCommGroup G] {N q M f s : ℕ} [NeZero N] [NeZero q]
  {κd : Type*} [Fintype κd]

/-- every lattice vector lies in `Rel_ℓ`. -/
theorem phase_memW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (a : κd → (Fin k → ZMod N)) (ha : ∀ t, evG V hN (a t) = T t) (j : Fin s) :
    combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) j ∈
      (evL V hN hqM).ker := by
  rw [combHom_apply, AddMonoidHom.mem_ker]
  exact relation_lattice V hN hqM FB (relMat Ttop Rint ν) (fun i => a (pos i))
    (fun i => by rw [hrow i, ha]) (kerMat q Ttop Rint ν j) (kerMat_mul Ttop Rint ν hB j)

open Classical in
/-- **S1 for the planted lattice phase**: conditionally on the draw points `T`, the `s` lattice vectors
are independent and uniform on `Rel_ℓ` (all tuples in `Rel_ℓ^s` have the same number of tag-tuples). -/
theorem phase_unifW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (hcop : Nat.Coprime M q)
    (hsurj : Function.Surjective (evG V hN))
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (hpos : Function.Injective pos) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (m m' : Fin s → (Fin k → ZMod q))
    (hm : ∀ j, m j ∈ (evL V hN hqM).ker)
    (hm' : ∀ j, m' j ∈ (evL V hN hqM).ker) :
    (univ.filter (fun a : κd → (Fin k → ZMod N) =>
        (∀ t, evG V hN (a t) = T t) ∧
        combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) = m)).card =
    (univ.filter (fun a : κd → (Fin k → ZMod N) =>
        (∀ t, evG V hN (a t) = T t) ∧
        combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) = m')).card := by
  classical
  have := unif_fibres_sel (evG V hN) (rho (Dvd.intro _ hqM))
    (evL V hN hqM).ker (fun μ hμ =>
      ker_reduces V hN hqM hcop μ (AddMonoidHom.mem_ker.1 hμ)) (kerMat q Ttop Rint ν)
    (Matrix.fromRows (0 : Matrix (Fin f) (Fin s) (ZMod q)) (1 : Matrix (Fin s) (Fin s) (ZMod q)))
    (kerMat_rightInv Ttop Rint ν hB) (fun z => ZMod.intCast_surjective z) pos hpos T
    (fun t => hsurj (T t)) (fun a ha j => phase_memW V hN hqM FB Ttop Rint ν hB pos T hrow a ha j)
    m m' hm hm'
  convert this


end phase
end ECDLP.L119
