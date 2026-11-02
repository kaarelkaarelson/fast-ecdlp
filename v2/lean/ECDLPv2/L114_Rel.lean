import Mathlib
import ECDLPv2.L114_Ev

/-!
# L114 / Rel: (a) the relation-lattice lemma and recovery of `d`

* `row_of_decomp` : a decomposition `R = ∑_j FB (t j)` gives the multiplicity row `r` with
  `∑_F r_F • FB F = R`.
* `relation_lattice` (paper Lemma "relations are relations"): rows `r_i` with `∑_F r_iF • FB F = ev(a_i)`,
  `λ ∈ (ZMod q)^n` with `λᵀ r = 0` over `ZMod q`  ⟹  `∑_i λ_i ρ(a_i) ∈ ker evL = Rel_ℓ`.
* `lattice_span_le` : the subgroup spanned by such vectors is inside `Rel_ℓ`.
* `recover_from_span` : if `(0,0,d',-1)` lies in that span, then `M • (d'•P - Q) = 0`.
* `true_relation_mem` : if `Q = d • P` then `(0,0,d,-1) ∈ Rel_ℓ`.
-/
namespace ECDLP.L114

open Finset

variable {G : Type*} [AddCommGroup G]

/-- multiplicity row of a decomposition given by factor-base labels -/
def multRow {m f : ℕ} (t : Fin m → Fin f) : Fin f → ℤ := fun F => (univ.filter (fun j => t j = F)).card

theorem row_of_decomp {m f : ℕ} (FB : Fin f → G) (t : Fin m → Fin f) :
    ∑ F, multRow t F • FB F = ∑ j, FB (t j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := t) (t := univ) (fun j _ => mem_univ _)]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_congr rfl (fun j hj => by rw [(mem_filter.1 hj).2] : ∀ j ∈ univ.filter (fun j => t j = F), FB (t j) = FB F)]
  simp [multRow]

section rel
variable {N q M k f : ℕ} {ι : Type*} [Fintype ι]

/-- **(a) Relation-lattice lemma.** -/
theorem relation_lattice (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (FB : Fin f → G) (r : Matrix ι (Fin f) ℤ) (a : ι → (Fin k → ZMod N))
    (hrow : ∀ i, ∑ F, r i F • FB F = evG V hN (a i))
    (lam : ι → ZMod q) (hlam : ∀ F, ∑ i, lam i * ((r i F : ℤ) : ZMod q) = 0) :
    evL V hN hqM (∑ i, lam i • rho (Dvd.intro _ hqM) (a i)) = 0 := by
  classical
  choose l hl using fun i => exists_lift q (fun _ : Fin 1 => lam i)
  have hl' : ∀ i, ((l i 0 : ℤ) : ZMod q) = lam i := fun i => congrFun (hl i) 0
  have hsmul : ∀ i, lam i • rho (Dvd.intro _ hqM) (a i) = (l i 0) • rho (Dvd.intro _ hqM) (a i) := by
    intro i; rw [← hl' i, Int.cast_smul_eq_zsmul]
  simp only [hsmul, map_sum, map_zsmul, ev_local_compat]
  have hdiv : ∀ F, ((q : ℤ) ∣ ∑ i, l i 0 * r i F) := by
    intro F
    have := hlam F
    simp only [← hl'] at this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact this
  choose c hc using hdiv
  have : ∑ i, l i 0 • M • evG V hN (a i) = M • ∑ F, (∑ i, l i 0 * r i F) • FB F := by
    simp only [← hrow, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun F _ => sum_congr rfl fun i _ => ?_
    rw [smul_comm (l i 0) M]
  rw [this, Finset.smul_sum]
  refine Finset.sum_eq_zero fun F _ => ?_
  have hM : ∀ x : G, M • x = (M : ℤ) • x := fun x => (natCast_zsmul x M).symm
  rw [hc F, hM, ← mul_smul]
  have h2 : ((M : ℤ) * (↑q * c F)) = c F * (N : ℤ) := by rw [← hqM]; push_cast; ring
  rw [h2, mul_smul, natCast_zsmul, hN, smul_zero]

/-- the subgroup spanned by relation-lattice vectors produced from kernel vectors stays in `Rel_ℓ`. -/
theorem lattice_span_le (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (FB : Fin f → G) (r : Matrix ι (Fin f) ℤ) (a : ι → (Fin k → ZMod N))
    (hrow : ∀ i, ∑ F, r i F • FB F = evG V hN (a i)) {s : ℕ}
    (Lam : Fin s → ι → ZMod q) (hLam : ∀ j F, ∑ i, Lam j i * ((r i F : ℤ) : ZMod q) = 0) :
    AddSubgroup.closure (Set.range fun j => ∑ i, Lam j i • rho (Dvd.intro _ hqM) (a i))
      ≤ (evL V hN hqM).ker := by
  rw [AddSubgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact relation_lattice V hN hqM FB r a hrow (Lam j) (hLam j)

theorem evL_four (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N) (z : ℤ) :
    evL ![H1, H2, P, Q] hN hqM ![0, 0, (z : ZMod q), -1] = M • (z • P - Q) := by
  have e0 : liftW q (M • (![H1, H2, P, Q] : Fin 4 → G) 0) (local_torsion _ hN hqM 0)
      ((![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) 0) = 0 := by
    show liftW q _ _ 0 = 0; exact map_zero _
  have e1 : liftW q (M • (![H1, H2, P, Q] : Fin 4 → G) 1) (local_torsion _ hN hqM 1)
      ((![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) 1) = 0 := by
    show liftW q _ _ 0 = 0; exact map_zero _
  have e2 : liftW q (M • (![H1, H2, P, Q] : Fin 4 → G) 2) (local_torsion _ hN hqM 2)
      ((![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) 2) = z • (M • P) :=
    liftW_intCast q (M • P) _ z
  have e3 : liftW q (M • (![H1, H2, P, Q] : Fin 4 → G) 3) (local_torsion _ hN hqM 3)
      ((![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) 3) = (-1 : ℤ) • (M • Q) := by
    have := liftW_intCast q (M • Q) (local_torsion ![H1, H2, P, Q] hN hqM 3) (-1)
    rw [← this]; congr 1; push_cast; rfl
  change ∑ j : Fin 4, liftW q (M • (![H1, H2, P, Q] : Fin 4 → G) j) (local_torsion _ hN hqM j)
    ((![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) j) = _
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  simp [smul_sub, smul_comm M, sub_eq_add_neg]

/-- **(a, recovery)**: if `(0,0,z,-1)` lies in the span of the lattice vectors, then `z` is a valid
local discrete log: `M • (z • P - Q) = 0`, i.e. `z ≡ d` on the `ℓ`-part. -/
theorem recover_from_span (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (FB : Fin f → G) (r : Matrix ι (Fin f) ℤ) (a : ι → (Fin 4 → ZMod N))
    (hrow : ∀ i, ∑ F, r i F • FB F = evG ![H1, H2, P, Q] hN (a i)) {s : ℕ}
    (Lam : Fin s → ι → ZMod q) (hLam : ∀ j F, ∑ i, Lam j i * ((r i F : ℤ) : ZMod q) = 0)
    (z : ℤ)
    (hmem : (![0, 0, (z : ZMod q), -1] : Fin 4 → ZMod q) ∈
      AddSubgroup.closure (Set.range fun j => ∑ i, Lam j i • rho (Dvd.intro _ hqM) (a i))) :
    M • (z • P - Q) = 0 := by
  have := lattice_span_le ![H1, H2, P, Q] hN hqM FB r a hrow Lam hLam hmem
  rw [AddMonoidHom.mem_ker, evL_four] at this
  exact this

/-- the true relation `(0,0,d,-1)` lies in `Rel_ℓ`. -/
theorem true_relation_mem (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (d : ℤ) (hQ : Q = d • P) :
    (![0, 0, (d : ZMod q), -1] : Fin 4 → ZMod q) ∈ (evL ![H1, H2, P, Q] hN hqM).ker := by
  rw [AddMonoidHom.mem_ker, evL_four, hQ, sub_self, smul_zero]

end rel
end ECDLP.L114
