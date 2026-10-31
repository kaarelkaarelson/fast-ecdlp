import ECDLP.L57_Cluster
import ECDLP.L56_PForced

/-!
# L57 / Width: shared bits of a `PForced` network, exactly

For `P : PForced R ι`, an enumeration `e : ι ≃ Fin g`, and the pair width `ew i j` of `P.toGNet`:
* `cc_eq`: `(P.toGNet.toNet e).cc a b = ew (e.symm a) (e.symm b)` (symmetric, `0` on the diagonal);
* `rowsum_eq`: the shared bits of gate `i` are `inW i + chd i * (w i + 1)`
  (`inW i = Σ_{j ∈ pa i} (w j + 1)`, `chd i` = number of children);
* `total_eq`: the total `U = 2 Σ_i inW i`.
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux ECDLP.L56

namespace PForcedW
variable {R : Type*} [CommRing R] {ι : Type} (P : PForced R ι) [Fintype ι] [DecidableEq ι]

/-- sum of incoming edge widths -/
def inW (i : ι) : ℕ := ∑ j ∈ P.pa i, (P.w j + 1)
/-- number of children -/
def chd (i : ι) : ℕ := (univ.filter fun j => i ∈ P.pa j).card

theorem not_mem_self (i : ι) : i ∉ P.pa i := fun h => lt_irrefl _ (P.hrk i i h)

theorem c_eq (i j : ι) : (P.toGNet).c i j =
    (if j ∈ P.pa i then P.w j + 1 else 0) + (if i ∈ P.pa j then P.w i + 1 else 0) := by
  classical
  show (if j ∈ P.pa i then P.w j + 1 else if i ∈ P.pa j then P.w i + 1 else 0) = _
  by_cases h1 : j ∈ P.pa i
  · simp [h1, P.pa_asymm h1]
  · by_cases h2 : i ∈ P.pa j <;> simp [h1, h2]

theorem c_symm (i j : ι) : (P.toGNet).c i j = (P.toGNet).c j i := by
  rw [c_eq, c_eq, add_comm]

theorem cc_eq {g : ℕ} (e : ι ≃ Fin g) (a b : Fin g) :
    ((P.toGNet).toNet e).cc a b = (P.toGNet).c (e.symm a) (e.symm b) := by
  unfold Net.cc
  rcases lt_trichotomy a b with h | h | h
  · simp [h]; rfl
  · subst h
    simp only [lt_self_iff_false, if_false]
    have : (P.toGNet).c (e.symm a) (e.symm a) = 0 := by
      rw [c_eq]; simp [not_mem_self]
    exact this.symm
  · simp [h, not_lt.2 h.le]
    exact c_symm P _ _

theorem rowsum_eq {g : ℕ} (e : ι ≃ Fin g) (a : Fin g) :
    ∑ b, ((P.toGNet).toNet e).cc a b = inW P (e.symm a) + chd P (e.symm a) * (P.w (e.symm a) + 1) := by
  classical
  simp_rw [cc_eq]
  rw [Fintype.sum_equiv e.symm (fun b => (P.toGNet).c (e.symm a) (e.symm b)) (fun j => (P.toGNet).c (e.symm a) j)
    (fun _ => rfl)]
  simp_rw [c_eq]
  rw [sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter]; unfold inW
    congr 1; ext j; simp
  · rw [← Finset.sum_filter]; unfold chd
    rw [sum_const, smul_eq_mul]

theorem total_eq {g : ℕ} (e : ι ≃ Fin g) :
    ((P.toGNet).toNet e).total = 2 * ∑ i, inW P i := by
  classical
  unfold Net.total
  have h1 : ∑ a, ∑ b, ((P.toGNet).toNet e).cc a b = ∑ i : ι, ∑ j : ι, (P.toGNet).c i j := by
    simp_rw [cc_eq]
    rw [← Fintype.sum_equiv e.symm (fun a => ∑ b, (P.toGNet).c (e.symm a) (e.symm b)) (fun i => ∑ j, (P.toGNet).c i j)
      (fun a => Fintype.sum_equiv e.symm _ _ (fun _ => rfl))]
  rw [h1]
  simp_rw [c_eq]
  simp_rw [sum_add_distrib]
  have h2 : ∑ i : ι, ∑ j : ι, (if j ∈ P.pa i then P.w j + 1 else 0) = ∑ i, inW P i := by
    refine sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]; unfold inW; congr 1; ext j; simp
  have h3 : ∑ i : ι, ∑ j : ι, (if i ∈ P.pa j then P.w i + 1 else 0) = ∑ i, inW P i := by
    rw [sum_comm]; exact h2
  rw [h2, h3]; ring

end PForcedW
end ECDLP.L57
end
