import ECDLP.L104_Final
import ECDLPv2.L109_CountChallenge

/-!
# L109 / Residue: what the real engine computes, and why it determines the count

* `count_eq_Zc` : the audited count `ECDLP109.count m x` is L61's `Zc m x (pre x)` (and `ECDLP109.strings = ECDLP.strings`).
* `engine_value_mod_real` : for EVERY `r ≥ 1`, the real engine (L104 `edgeCoreFL_real2`) computes, at every `Good` frame state of length `≥ T1 r`
  and for every modulus `j > 1`, a network whose value in `ZMod j` is `Zc` (this is the link `EdgeNetValueF` that L104 feeds to `uniCF_val'`).
  The engine command `uniC` only keeps the divisibility flags `[j ∣ D·Zc]`; `countMF_spec'` (L104B) shows scalar 308 is `(D·Zc : ZMod j).val`
  after each `countM` (`D = deepMult`).
* `crt_unique` : `Zc` is determined by the residues `D·Zc mod j` for `1 ≤ j ≤ 2(n+ML+4)` among the numbers `< 2^n` (`D ≤ 2^ML`): the
  information the engine already holds suffices for counting; only the (bignum) reconstruction of `Zc` is missing.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace ECDLP.L109
open ECDLP ECDLP.L61 ECDLP.L65 ECDLP.L70 ECDLP.L104 ECDLP.L104R ECDLP.L96 ECDLP.L92 Factoring.Aux Finset

theorem strings_eq (m : ℕ) (x : ECDLP.Inst) : ECDLP109.strings m x = ECDLP.strings m x := rfl

theorem count_eq_Zc (m : ℕ) (x : ECDLP.Inst) : ECDLP109.count m x = Zc m x (pre x) := rfl

/-- **The real engine's network value is `Zc` modulo every `j > 1`** (at `Good` frame states with `len ≥ T1 r`), unconditionally. -/
theorem engine_value_mod_real (r : ℕ) (hr : 1 ≤ r) : EdgeNetValueF r (edgeCoreFL_real2 r) :=
  edgeNetValueF_of_core r hr (edgeCoreFL_real2 r) (ECDLP.L96.realRep_real2 r)
    (fun x τ hG hT s hF => pl_of_frame r x τ hG hT s hF)

/-- ... and `Zc < 2^len` (L92 `zc_lt_len`), the size bound for the reconstruction. -/
theorem zc_lt_len_real (r : ℕ) (x : ECDLP.Inst) (τ : List Bool) (hg : Good (r + 1) x τ) (hT : T1 r ≤ (redInp x τ).len) :
    Zc (r + 1) x τ < 2 ^ (redInp x τ).len :=
  zc_lt_len r x τ hg (le_trans (le_max_left _ _) hT)

/-- **The residues `D·c mod j`, `1 ≤ j ≤ 2(n+ML+4)`, determine `c < 2^n`** (`0 < D ≤ 2^ML`).  This is the CRT bound of Rudich's
`bit_of_flags` (central binomial coefficient), used with the difference of two candidates. -/
theorem crt_unique {n D ML c c' : ℕ} (hD0 : 0 < D) (hDl : D ≤ 2 ^ ML) (hc : c < 2 ^ n) (hc' : c' < 2 ^ n)
    (h : ∀ j, 1 ≤ j → j ≤ 2 * (n + ML + 4) → (D * c) % j = (D * c') % j) : c = c' := by
  wlog hle : c ≤ c' generalizing c c'
  · exact (this hc' hc (fun j h1 h2 => (h j h1 h2).symm) (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdn : d < 2 ^ n := by omega
  have hfl : flagCount D d (2 * (n + ML + 4) + 1) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_neg]
    rintro ⟨h2, hnd⟩
    apply hnd
    have := h j (by omega) (by omega)
    rw [mul_add] at this
    have h4 := Nat.sub_mod_eq_zero_of_mod_eq this.symm
    rw [show D * c + D * d - D * c = D * d by omega] at h4
    exact Nat.dvd_of_mod_eq_zero h4
  have := bit_of_flags (n := n) (ML := ML) (c := d) hD0 hDl hdn
  rw [hfl] at this
  simp at this
  omega

end ECDLP.L109
#print axioms ECDLP.L109.crt_unique
#print axioms ECDLP.L109.engine_value_mod_real
#print axioms ECDLP.L109.zc_lt_len_real
#print axioms ECDLP.L109.count_eq_Zc
