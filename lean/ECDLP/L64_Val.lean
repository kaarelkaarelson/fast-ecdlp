import ECDLP.L64_Code

/-!
# L64 / Val: the value of `toGNetE` (explicit message coding) equals the value of `toGNet`

`PForced.toGNet` codes messages with the non-canonical `Fintype.equivFin`.  For an explicit coding `E` the
network `toGNetE P E` has the same good settings (`good_iffE`), hence the same value (`value_toGNetE`).
-/
noncomputable section
namespace ECDLP.L64
open Factoring.Aux Finset ECDLP.L56

variable {R : Type*} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (P : PForced R ι)
  (E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i)))

omit [Fintype ι] in
theorem good_iffE (z : ∀ i, P.S i) : (toGNetE P E).Good z ↔ P.Chk z ∧ P.Cons z := by
  classical
  unfold GNet.Good PForced.Chk PForced.Cons
  show ((∀ i, P.W i (z i) = 1) ∧ ∀ i j, i ≠ j → _ = _) ↔ _
  refine and_congr Iff.rfl ⟨fun h i j => ?_, fun h i j hij => ?_⟩
  · have hne : i ≠ j.1 := fun e => by
      have := P.hrk i j.1 j.2; rw [← e] at this; exact lt_irrefl _ this
    have := h i j.1 hne
    simp only [toGNetE, dif_pos j.2, dif_neg (P.pa_asymm j.2), if_pos j.2] at this
    exact (E j.1).injective (Fin.ext (by simpa using this))
  · by_cases h1 : j ∈ P.pa i
    · have h2 := P.pa_asymm h1
      simp only [toGNetE, dif_pos h1, dif_neg h2, if_pos h1]
      rw [h i ⟨j, h1⟩]
    · by_cases h2 : i ∈ P.pa j
      · simp only [toGNetE, dif_neg h1, if_pos h2, dif_pos h2]
        rw [h j ⟨i, h2⟩]
      · simp [toGNetE, h1, h2]

omit [Fintype ι] in
theorem v_ltE (i j : ι) (z : P.S i) : (toGNetE P E).v i j z < 2 ^ (toGNetE P E).c i j := by
  classical
  show (if h : j ∈ P.pa i then (E j (z.2 ⟨j, h⟩) : ℕ) + 1
    else if i ∈ P.pa j then (E i (P.out i z j) : ℕ) + 1 else 0) <
    2 ^ (if j ∈ P.pa i then P.w j + 1 else if i ∈ P.pa j then P.w i + 1 else 0)
  have hlt : ∀ i (m : P.Msg i), (E i m : ℕ) < 2 ^ P.w i := fun i m =>
    lt_of_lt_of_le (E i m).isLt (Nat.le_pow_clog one_lt_two _)
  by_cases h1 : j ∈ P.pa i
  · simp only [dif_pos h1, if_pos h1]
    have := hlt j (z.2 ⟨j, h1⟩)
    rw [pow_succ]; omega
  · by_cases h2 : i ∈ P.pa j
    · simp only [dif_neg h1, if_neg h1, if_pos h2]
      have := hlt i (P.out i z j)
      rw [pow_succ]; omega
    · simp [h1, h2]

open Classical in
/-- **The value of the network with the explicit message coding is the value of `toGNet`.** -/
theorem value_toGNetE {g : ℕ} (e : ι ≃ Fin g) (hW : ∀ i s, P.W i s = 0 ∨ P.W i s = 1) :
    ((toGNetE P E).toNet e).value = ((P.toGNet).toNet e).value := by
  classical
  rw [GNet.value_toNet (toGNetE P E) e hW (fun i j z => v_ltE P E i j z),
    GNet.value_toNet P.toGNet e hW (fun i j z => P.v_lt i j z)]
  have hG : (toGNetE P E).Good = P.toGNet.Good :=
    funext fun z => propext ((good_iffE P E z).trans (P.good_iff z).symm)
  rw [hG]
  congr 2

end ECDLP.L64
end
