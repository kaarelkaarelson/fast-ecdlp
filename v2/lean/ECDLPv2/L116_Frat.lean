import Mathlib
import ECDLPv2.L116_Union

/-!
# L116 / Frat: a proper subgroup of a finite abelian `ℓ`-group lies in the kernel of a nonzero hom to `ZMod ℓ`
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L116

open Finset

theorem exists_hom_of_ne_top {A : Type*} [AddCommGroup A] [Finite A] {ℓ a : ℕ} [Fact ℓ.Prime]
    (hcard : Nat.card A = ℓ ^ a) (H : AddSubgroup A) (hH : H ≠ ⊤) :
    ∃ φ : A →+ ZMod ℓ, φ ≠ 0 ∧ ∀ x ∈ H, φ x = 0 := by
  obtain ⟨M, hM, hHM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH
  have hprime : M.index.Prime := (AddSubgroup.isCoatom_iff_index_prime M).1 hM
  have hdvd : M.index ∣ ℓ ^ a := hcard ▸ AddSubgroup.index_dvd_card M
  have hidx : M.index = ℓ :=
    (Nat.prime_dvd_prime_iff_eq hprime (Fact.out : ℓ.Prime)).1 (hprime.dvd_of_dvd_pow hdvd)
  have hQ : Nat.card (A ⧸ M) = ℓ := by rw [← hidx]; exact (AddSubgroup.index_eq_card M).symm
  have hcyc : IsAddCyclic (A ⧸ M) := isAddCyclic_of_prime_card hQ
  let e : (A ⧸ M) ≃+ ZMod ℓ := addEquivOfAddCyclicCardEq (hQ.trans (Nat.card_zmod ℓ).symm)
  let φ : A →+ ZMod ℓ := e.toAddMonoidHom.comp (QuotientAddGroup.mk' M)
  refine ⟨φ, ?_, ?_⟩
  · intro h0
    obtain ⟨x, hx⟩ : ∃ x, x ∉ M := by
      by_contra hc; push Not at hc
      exact hM.1 (AddSubgroup.eq_top_iff' M |>.2 hc)
    have : φ x = 0 := by rw [h0]; rfl
    have h1 : e (QuotientAddGroup.mk' M x) = 0 := this
    have h3 : QuotientAddGroup.mk' M x = 0 := by simpa using h1
    exact hx ((QuotientAddGroup.eq_zero_iff x).1 h3)
  · intro x hx
    have : (QuotientAddGroup.mk' M x) = 0 := (QuotientAddGroup.eq_zero_iff x).2 (hHM hx)
    show e (QuotientAddGroup.mk' M x) = 0
    rw [this]; simp

end ECDLP.L116
