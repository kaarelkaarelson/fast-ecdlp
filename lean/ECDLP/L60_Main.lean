import ECDLP.L60_Exp3

/-!
# L60: the rate theorem for an abstract network family

* `uniReq_expG` (Rudich `uniReq_exp`, UniMain.lean:25): `V = 2^(16 Z + 127)` meets `F.UniReq`.
* `CostedFamily`: a `NetFamily` together with the evaluation-cost bound `τ`: the number of steps of the
  family's zero test at input length `n` is at most `c (V+1)^E` whenever `V` satisfies `F.UniReq V n`
  (Rudich: `uniC_cost`).
* `rate_gen` (Rudich `subexp_of_poly` + `uniReq_exp`, with the Turing-machine glue abstracted away):
  if `F.Spec` (total and per-cluster sizes `O(n)`), then steps `≤ C_k 2^(n/k)` for every `k`.
-/

namespace ECDLP.L60

open Factoring.Aux

namespace NetFamily

variable {F : NetFamily}

theorem Kb_succ_powG (K0 ℓ : ℕ) : Kb K0 (ℓ + 1) ^ 40 = 9 ^ 40 * (Kb K0 ℓ ^ 40) ^ 16 := by
  rw [Kb_succ]; ring

/-- **The requirements are met** by `V = 2^(16 Z + 127)` with `Z = o(n)`. -/
theorem uniReq_expG (hS : F.Spec) : ∃ Z : ℕ → ℕ, (∀ n, F.UniReq (2 ^ Z n) n) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, Z n ≤ n / k + C := by
  obtain ⟨Z, hT, hD, hNP, hM, hS', hK, hL, hZ⟩ := uni_exp_gen hS
  refine ⟨fun n => 16 * Z n + 127, fun n => ?_, fun k hk => ?_⟩
  · have hmono : 2 ^ Z n ≤ 2 ^ (16 * Z n + 127) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmain : F.MainReq (2 ^ Z n) K0u (ellOf n) n :=
      mainReq_of hS (by norm_num) (hT n) (hD n) le_rfl
    refine ⟨(hmain.mono hS hmono), le_trans (hNP n) hmono, le_trans (hL n) hmono, le_trans (hS' n) hmono, ?_⟩
    rw [Kb_succ_powG]
    calc 9 ^ 40 * (Kb K0u (ellOf n) ^ 40) ^ 16 ≤ 2 ^ 127 * (2 ^ Z n) ^ 16 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (hK n) 16)
      _ = 2 ^ (16 * Z n + 127) := by rw [← pow_mul, ← pow_add]; ring_nf
  · obtain ⟨C, hC⟩ := hZ (16 * k) (by omega)
    refine ⟨16 * C + 127, fun n => ?_⟩
    show 16 * Z n + 127 ≤ n / k + (16 * C + 127)
    have := mul_div_mul_le 16 k n
    have := hC n
    omega

end NetFamily

/-- A network family together with its evaluation-cost bound `τ`.  `Inp` is the type of machine inputs
(Rudich: states `St`), `len i` the input length `n`, `adm i` the admissibility side conditions,
`cost i` the number of steps of the family's zero test on input `i`; `τ` says the cost is polynomial in
any value bound `V` meeting the family's requirements at the input length. -/
structure CostedFamily extends NetFamily where
  Inp : Type
  len : Inp → ℕ
  adm : Inp → Prop
  cost : Inp → ℕ
  τ : ∃ c E : ℕ, ∀ (V : ℕ) (i : Inp), adm i → toNetFamily.UniReq V (len i) → cost i ≤ c * (V + 1) ^ E

/-- **The rate theorem for an abstract network family.**  If the family satisfies the size interface
(total and per-cluster sizes `O(n)`), its zero test is computed within `C_k · 2^(n/k)` steps on every
admissible input of length `n`, for every `k ≥ 1`. -/
theorem rate_gen (CF : CostedFamily) (hS : CF.toNetFamily.Spec) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ i : CF.Inp, CF.adm i → CF.cost i ≤ C * 2 ^ (CF.len i / k) := by
  obtain ⟨c, E, hc⟩ := CF.τ
  obtain ⟨Z, hR, hZ⟩ := NetFamily.uniReq_expG hS
  intro k hk
  obtain ⟨C, hC⟩ := hZ ((E + 1) * k) (by nlinarith)
  refine ⟨c * 2 ^ (E * (C + 1)), fun i hi => ?_⟩
  calc CF.cost i ≤ c * (2 ^ Z (CF.len i) + 1) ^ E := hc _ i hi (hR _)
    _ ≤ c * (2 ^ (E * (C + 1)) * 2 ^ (CF.len i / k)) :=
        Nat.mul_le_mul_left _ (pow_absorb E k C (CF.len i) (Z (CF.len i)) hk (hC _))
    _ = c * 2 ^ (E * (C + 1)) * 2 ^ (CF.len i / k) := by ring

end ECDLP.L60
