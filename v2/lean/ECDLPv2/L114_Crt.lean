import Mathlib

/-!
# L114 / Crt: combining local discrete logs; (d) correctness of the output

Moduli `q : ι → ℕ` (the prime powers `ℓ^{v_ℓ}` of `N`) pairwise coprime, `N = ∏ q`, `M i = N / q i`.
`LocalSol i z : M i • (z • P - Q) = 0` is the statement "`z` is a discrete log on the `ℓ_i`-part"
(`π_ℓ = M •`).  Both the lattice route (`recover_from_span`) and Pohlig–Hellman produce such `z`.
* `localSol_shift` : `LocalSol` depends only on `z mod q i`.
* `localSol_of_ph` : Pohlig–Hellman residues (`z ≡ d` modulo the order of `M i • P`) are local solutions.
* `eq_zero_of_all_local` : `M i • y = 0` for all `i` ⟹ `y = 0`  (`N • G = 0` splits).
* `crt_correct` : CRT value `x` of local solutions satisfies `x • P = Q`.
* `finalStep` / `finalStep_sound` : the algorithm's final test; **any output satisfies `x • P = Q`**.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

variable {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]

section crt
variable (q : ι → ℕ)

/-- complementary modulus -/
def cofac (i : ι) : ℕ := ∏ j ∈ univ.erase i, q j

theorem mul_cofac (i : ι) : q i * cofac q i = ∏ j, q j := by
  simp [cofac, Finset.mul_prod_erase univ q (mem_univ i)]

theorem coprime_cofac (hq : Pairwise (Function.onFun Nat.Coprime q)) (i : ι) : Nat.Coprime (q i) (cofac q i) := by
  unfold cofac
  refine Nat.Coprime.prod_right fun j hj => hq (Finset.ne_of_mem_erase hj).symm

variable {q}

/-- `z` is a discrete log for `Q` w.r.t. `P` on the `i`-th prime-power part. -/
def LocalSol (P Q : G) (i : ι) (z : ℤ) : Prop := cofac q i • (z • P - Q) = 0

theorem localSol_shift (hN : ∀ g : G, (∏ j, q j) • g = 0) (P Q : G) (i : ι) (z : ℤ) (c : ℤ)
    (h : LocalSol (q := q) P Q i z) : LocalSol (q := q) P Q i (z + q i * c) := by
  unfold LocalSol at *
  have : (z + (q i : ℤ) * c) • P - Q = (z • P - Q) + c • ((q i) • P) := by
    rw [add_smul, mul_smul, natCast_zsmul, smul_comm (q i) c P]; abel
  rw [this, smul_add, h, zero_add, smul_comm, ← mul_nsmul', mul_comm, mul_cofac, hN, smul_zero]

/-- Pohlig–Hellman residues are local solutions: if `Q = d • P` and the order of `M • P`
divides `z - d`. -/
theorem localSol_of_ph (P Q : G) (i : ι) (d z : ℤ) (hQ : Q = d • P)
    (h : (addOrderOf (cofac q i • P) : ℤ) ∣ z - d) : LocalSol (q := q) P Q i z := by
  unfold LocalSol
  obtain ⟨c, hc⟩ := h
  have hz : z • P - Q = ((addOrderOf (cofac q i • P) : ℤ) * c) • P := by
    rw [hQ, ← sub_smul]; congr 1
  rw [hz, mul_smul, natCast_zsmul, smul_comm (cofac q i) (addOrderOf (cofac q i • P)),
    smul_comm (cofac q i) c P, smul_comm (addOrderOf (cofac q i • P)) c, addOrderOf_nsmul_eq_zero,
    smul_zero]

theorem eq_zero_of_all_local (hq : Pairwise (Function.onFun Nat.Coprime q))
    (y : G) (hN : (∏ j, q j) • y = 0) (h : ∀ i, cofac q i • y = 0) : y = 0 := by
  have h1 : ∀ i, addOrderOf y ∣ cofac q i := fun i => addOrderOf_dvd_of_nsmul_eq_zero (h i)
  have h2 : Nat.Coprime (addOrderOf y) (∏ j, q j) := by
    refine Nat.Coprime.prod_right fun i _ => ?_
    exact Nat.Coprime.coprime_dvd_left (h1 i) (coprime_cofac q hq i).symm
  have h3 : addOrderOf y ∣ ∏ j, q j := addOrderOf_dvd_of_nsmul_eq_zero hN
  have := Nat.Coprime.eq_one_of_dvd h2 h3
  exact AddMonoid.addOrderOf_eq_one_iff.1 this

theorem exists_crt (hq0 : ∀ i, q i ≠ 0) (hq : Pairwise (Function.onFun Nat.Coprime q)) (z : ι → ℤ) :
    ∃ x : ℤ, ∀ i, x ≡ z i [ZMOD q i] := by
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset (fun i => (z i % q i).toNat) q univ
    (fun i _ => hq0 i) (fun i _ j _ hij => hq hij)
  refine ⟨k, fun i => ?_⟩
  have := (Int.natCast_modEq_iff (a := k) (b := (z i % q i).toNat) (n := q i)).2 (hk i (mem_univ i))
  have hpos : 0 ≤ z i % q i := Int.emod_nonneg _ (by exact_mod_cast hq0 i)
  rw [Int.toNat_of_nonneg hpos] at this
  exact this.trans (Int.mod_modEq _ _)

/-- **CRT correctness**: an integer `x` that agrees with local solutions modulo every `q i`
satisfies `x • P = Q`. -/
theorem crt_correct (hq : Pairwise (Function.onFun Nat.Coprime q)) (hN : ∀ g : G, (∏ j, q j) • g = 0)
    (P Q : G) (z : ι → ℤ) (hz : ∀ i, LocalSol (q := q) P Q i (z i)) (x : ℤ)
    (hx : ∀ i, x ≡ z i [ZMOD q i]) : x • P = Q := by
  have : x • P - Q = 0 := by
    refine eq_zero_of_all_local hq _ (hN _) fun i => ?_
    obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.1 (hx i).symm)
    have := localSol_shift hN P Q i (z i) c (hz i)
    have e : x = z i + q i * c := by linarith
    rw [e]; exact this
  exact sub_eq_zero.1 this

open Classical in
/-- the algorithm's final test: output the CRT candidate only if it passes `x • P = Q`. -/
noncomputable def finalStep (P Q : G) (x : ℤ) : Option ℤ := if x • P = Q then some x else none

/-- **(d) Correctness: every output satisfies `d • P = Q`** (no hypothesis on the rest of the run). -/
theorem finalStep_sound (P Q : G) (x o : ℤ) (h : finalStep P Q x = some o) : o • P = Q := by
  unfold finalStep at h
  split_ifs at h with hx
  · cases h; exact hx

open Classical in
/-- the algorithm end-to-end after the local phase: given optional local residues, CRT-combine
(when all are present) and test. -/
noncomputable def runFinal (q : ι → ℕ) (P Q : G) (res : ι → Option ℤ) : Option ℤ :=
  if h : ∀ i, (res i).isSome then
    finalStep P Q (Classical.epsilon (fun x : ℤ => ∀ i, x ≡ ((res i).get (h i)) [ZMOD q i]))
  else none

theorem runFinal_sound (q : ι → ℕ) (P Q : G) (res : ι → Option ℤ) (o : ℤ)
    (h : runFinal q P Q res = some o) : o • P = Q := by
  unfold runFinal at h
  split_ifs at h
  exact finalStep_sound _ _ _ _ h

/-- completeness of the final phase: if every local phase delivered a local solution, the output
is `some _`, and it is a discrete log. -/
theorem runFinal_complete (hq0 : ∀ i, q i ≠ 0) (hq : Pairwise (Function.onFun Nat.Coprime q))
    (hN : ∀ g : G, (∏ j, q j) • g = 0) (P Q : G) (res : ι → Option ℤ)
    (hres : ∀ i, ∃ z, res i = some z ∧ LocalSol (q := q) P Q i z) :
    ∃ o, runFinal q P Q res = some o ∧ o • P = Q := by
  have hs : ∀ i, (res i).isSome := fun i => by obtain ⟨z, hz, -⟩ := hres i; simp [hz]
  have hget : ∀ i, LocalSol (q := q) P Q i ((res i).get (hs i)) := by
    intro i; obtain ⟨z, hz, hl⟩ := hres i; simpa [hz] using hl
  have hex := exists_crt hq0 hq (fun i => (res i).get (hs i))
  have hx := Classical.epsilon_spec hex
  have hok := crt_correct hq hN P Q _ hget _ hx
  refine ⟨_, ?_, hok⟩
  unfold runFinal
  rw [dif_pos hs]
  unfold finalStep
  rw [if_pos hok]

end crt
end ECDLP.L114
