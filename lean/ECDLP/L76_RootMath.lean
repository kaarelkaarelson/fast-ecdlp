import Mathlib

/-!
# L76 / RootMath: the bit-by-bit integer `m`-th root (pure arithmetic)

`cseq pv m nb j` is the candidate after `j` greedy bit decisions from the top (`nb` bits): try to add `2^(nb-1-j)`, keep it iff `c^m < pv`.
`cseq_final`: for `1 ≤ m`, `0 < pv ≤ (2^nb)^m`, `cseq nb + 1 = sInf {B | pv ≤ B^m}` (`= ⌈pv^(1/m)⌉`, L51's `Bd pv (m-1)`).
-/
namespace ECDLP.L76

def cseq (pv m nb : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if (cseq pv m nb j + 2 ^ (nb - 1 - j)) ^ m < pv then cseq pv m nb j + 2 ^ (nb - 1 - j) else cseq pv m nb j

theorem cseq_inv (pv m nb : ℕ) (hm : 1 ≤ m) (hpv : 0 < pv) (hb : pv ≤ (2 ^ nb) ^ m) :
    ∀ j, j ≤ nb → (cseq pv m nb j) ^ m < pv ∧ 2 ^ (nb - j) ∣ cseq pv m nb j ∧
      ¬ ((cseq pv m nb j + 2 ^ (nb - j)) ^ m < pv) ∧ cseq pv m nb j + 2 ^ (nb - j) ≤ 2 ^ nb := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, by simp [cseq], ?_, by simp [cseq]⟩
    · rw [cseq, zero_pow (by omega)]; exact hpv
    · rw [cseq]; simpa using hb
  | succ j ih =>
    intro hj
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have e : nb - j = (nb - (j + 1)) + 1 := by omega
    have e2 : nb - 1 - j = nb - (j + 1) := by omega
    set d := 2 ^ (nb - (j + 1)) with hd
    have h2d : 2 ^ (nb - j) = 2 * d := by rw [e, pow_succ, hd]; ring
    rw [h2d] at i2 i3 i4
    have hdd : d ∣ cseq pv m nb j := (Dvd.intro_left 2 rfl : d ∣ 2 * d).trans i2
    simp only [cseq, e2]
    by_cases ht : (cseq pv m nb j + d) ^ m < pv
    · rw [if_pos ht]
      refine ⟨ht, ?_, ?_, ?_⟩
      · exact dvd_add hdd dvd_rfl
      · rw [h2d] at *; intro h; apply i3; convert h using 2; rw [h2d]; ring
      · rw [h2d] at *; omega
    · rw [if_neg ht]
      exact ⟨i1, hdd, ht, by omega⟩

theorem cseq_final (pv m nb : ℕ) (hm : 1 ≤ m) (hpv : 0 < pv) (hb : pv ≤ (2 ^ nb) ^ m) :
    cseq pv m nb nb + 1 = sInf {B | pv ≤ B ^ m} := by
  obtain ⟨i1, i2, i3, i4⟩ := cseq_inv pv m nb hm hpv hb nb le_rfl
  simp only [Nat.sub_self, pow_zero] at i3
  set c := cseq pv m nb nb
  symm
  apply le_antisymm
  · apply Nat.sInf_le; show pv ≤ (c + 1) ^ m; omega
  · have hne : ({B | pv ≤ B ^ m} : Set ℕ).Nonempty := ⟨c + 1, by show pv ≤ (c + 1) ^ m; omega⟩
    have hmem := Nat.sInf_mem hne
    by_contra hlt
    have hlt : c + 1 > sInf {B | pv ≤ B ^ m} := not_le.mp hlt
    have : sInf {B | pv ≤ B ^ m} ≤ c := by omega
    have h2 : (sInf {B | pv ≤ B ^ m}) ^ m ≤ c ^ m := Nat.pow_le_pow_left this m
    have h3 : pv ≤ (sInf {B | pv ≤ B ^ m}) ^ m := hmem
    omega

end ECDLP.L76
