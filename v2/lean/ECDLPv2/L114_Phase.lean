import Mathlib
import ECDLPv2.L114_Ev
import ECDLPv2.L114_Rel
import ECDLPv2.L114_Unif
import ECDLPv2.L114_Plant

/-!
# L114 / Phase: the lattice phase at one prime `ℓ` (planted version), assembled

Data: `G` finite abelian, `N • G = 0`, `V = (H₁,H₂,P,Q)`, `q = ℓ^v`, `M = N / q` coprime to `q`.
Draws `t ∈ κd` with points `T t` (`= ev (a t)`); the accepted draws `pos : Fin f ⊕ Fin s ↪ κd`
(`f` planted rows then `s` ordinary rows) carry the relation matrix `[T' - νI ; R]` over `ℤ`.
When the planted block is invertible modulo `q`, `Λ = (-R B⁻¹ | I)` gives `s` kernel vectors and
* every `μ_j = ∑ Λ_ji ρ(a_{pos i})` lies in `Rel_ℓ = ker evL`            (`phase_mem`)
* `(μ_j)_j` is uniform on `Rel_ℓ^s`, conditionally on the points `T`      (`phase_unif`).
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

section phase
variable {G : Type*} [AddCommGroup G] {N q M f s : ℕ} [NeZero N] [NeZero q]
  {κd : Type*} [Fintype κd]

/-- the integer relation matrix: planted rows `T' - ν I` on top, ordinary rows below. -/
def relMat (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ) :
    Matrix (Fin f ⊕ Fin s) (Fin f) ℤ :=
  Matrix.fromRows (Ttop - Matrix.scalar (Fin f) ν) Rint

/-- the kernel-vector matrix over `ZMod q`. -/
noncomputable def kerMat (q : ℕ) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ)
    (ν : ℤ) : Matrix (Fin s) (Fin f ⊕ Fin s) (ZMod q) :=
  Matrix.fromCols (-((Rint.map (Int.castRingHom (ZMod q))) *
    ((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q)))⁻¹)) 1

theorem kerMat_mul (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det)) (j : Fin s) (F : Fin f) :
    ∑ i, kerMat q Ttop Rint ν j i * ((relMat Ttop Rint ν i F : ℤ) : ZMod q) = 0 := by
  have h := (planted_kernel ((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))) hB
    (Rint.map (Int.castRingHom (ZMod q)))).1
  have := congrFun (congrFun h j) F
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with i | i <;> rfl

theorem kerMat_rightInv (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det)) :
    kerMat q Ttop Rint ν * Matrix.fromRows (0 : Matrix (Fin f) (Fin s) (ZMod q)) (1 : Matrix (Fin s) (Fin s) (ZMod q)) = 1 :=
  (planted_kernel ((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))) hB
    (Rint.map (Int.castRingHom (ZMod q)))).2

/-- every lattice vector lies in `Rel_ℓ`. -/
theorem phase_mem (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (a : κd → (Fin 4 → ZMod N)) (ha : ∀ t, evG ![H1, H2, P, Q] hN (a t) = T t) (j : Fin s) :
    combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) j ∈
      (evL ![H1, H2, P, Q] hN hqM).ker := by
  rw [combHom_apply, AddMonoidHom.mem_ker]
  exact relation_lattice ![H1, H2, P, Q] hN hqM FB (relMat Ttop Rint ν) (fun i => a (pos i))
    (fun i => by rw [hrow i, ha]) (kerMat q Ttop Rint ν j) (kerMat_mul Ttop Rint ν hB j)

open Classical in
/-- **S1 for the planted lattice phase**: conditionally on the draw points `T`, the `s` lattice vectors
are independent and uniform on `Rel_ℓ` (all tuples in `Rel_ℓ^s` have the same number of tag-tuples). -/
theorem phase_unif (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (hcop : Nat.Coprime M q)
    (hsurj : Function.Surjective (evG ![H1, H2, P, Q] hN))
    (FB : Fin f → G) (Ttop : Matrix (Fin f) (Fin f) ℤ) (Rint : Matrix (Fin s) (Fin f) ℤ) (ν : ℤ)
    (hB : IsUnit (((Ttop - Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod q))).det))
    (pos : Fin f ⊕ Fin s → κd) (hpos : Function.Injective pos) (T : κd → G)
    (hrow : ∀ i, ∑ F, relMat Ttop Rint ν i F • FB F = T (pos i))
    (m m' : Fin s → (Fin 4 → ZMod q))
    (hm : ∀ j, m j ∈ (evL ![H1, H2, P, Q] hN hqM).ker)
    (hm' : ∀ j, m' j ∈ (evL ![H1, H2, P, Q] hN hqM).ker) :
    (univ.filter (fun a : κd → (Fin 4 → ZMod N) =>
        (∀ t, evG ![H1, H2, P, Q] hN (a t) = T t) ∧
        combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) = m)).card =
    (univ.filter (fun a : κd → (Fin 4 → ZMod N) =>
        (∀ t, evG ![H1, H2, P, Q] hN (a t) = T t) ∧
        combHom (rho (Dvd.intro _ hqM)) (kerMat q Ttop Rint ν) (fun i => a (pos i)) = m')).card := by
  classical
  have := unif_fibres_sel (evG ![H1, H2, P, Q] hN) (rho (Dvd.intro _ hqM))
    (evL ![H1, H2, P, Q] hN hqM).ker (fun μ hμ =>
      ker_reduces ![H1, H2, P, Q] hN hqM hcop μ (AddMonoidHom.mem_ker.1 hμ)) (kerMat q Ttop Rint ν)
    (Matrix.fromRows (0 : Matrix (Fin f) (Fin s) (ZMod q)) (1 : Matrix (Fin s) (Fin s) (ZMod q)))
    (kerMat_rightInv Ttop Rint ν hB) (fun z => ZMod.intCast_surjective z) pos hpos T
    (fun t => hsurj (T t)) (fun a ha j => phase_mem H1 H2 P Q hN hqM FB Ttop Rint ν hB pos T hrow a ha j)
    m m' hm hm'
  convert this

end phase
end ECDLP.L114
