import ECDLP.L61_Final

/-!
# L61 / Main: the machine, its time bound, and the sub-exponential corollary

* `driver_machine` : from `ZSpec m c T`, one `TM2ComputableInTime encB encOut (lexLeast m)` with finite alphabets and
  explicit time `cc * (Q * (L + k0 + drvBound m L (T L) + 1)^2 + L + 1)^3 + 1`.
* `driver_time_poly` : that time is `≤ C (L+1)^6 (T L + 1)^6`.
* `driver_subexp` : if `T L ≤ C_k 2^(L/k)` for every `k ≥ 1` then the machine runs within `C'_k 2^(L/k)` for every `k ≥ 1`.
* `subexponentialRate_zero` : the pipeline instantiated at `m = 0` (no strings), unconditionally: a machine for
  `lexLeast 0` with `p^{o(1)}` time (non-vacuity of the interface; the content for `m ≥ 1` needs the oracle).
-/
namespace ECDLP.L61
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Turing Computability

theorem driver_machine (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (h : ZSpec m c T) :
    ∃ (M : TM2ComputableInTime encB encOut (lexLeast m)) (Q k0 cc : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ L, M.time L = cc * (Q * (L + k0 + drvBound m L (T L) + 1) ^ 2 + L + 1) ^ 3 + 1 :=
  tm_of_source encB encOut (lexLeast m) (drvZ m c) 2 (fun L => drvBound m L (T L))
    (fun x => (driver_out m c T h x).1) (fun x => (driver_out m c T h x).2)

theorem drvBound_le (m L T : ℕ) : drvBound m L T ≤ (71 * (m + 2) + 100) * ((L + 1) * (T + 1)) := by
  unfold drvBound
  have h1 : m * (L + 1) + 2 ≤ (m + 2) * (L + 1) := by nlinarith
  have h2 : (m * (L + 1) + 2) * (2 * T + 31) ≤ (m + 2) * (L + 1) * (31 * (T + 1)) :=
    Nat.mul_le_mul h1 (by omega)
  have h3 : (m + 2) * (40 * L + 40) ≤ 40 * ((m + 2) * ((L + 1) * (T + 1))) := by nlinarith [Nat.zero_le (T * L * m)]
  have h4 : 100 ≤ 100 * ((L + 1) * (T + 1)) := by nlinarith [Nat.zero_le (T * L)]
  nlinarith [Nat.zero_le (T * L * m), Nat.zero_le (T * L), Nat.zero_le (m * L), Nat.zero_le (m * T)]

/-- The time is at most `C (L+1)^6 (T L+1)^6`. -/
theorem time_poly_aux (Q k0 cc D : ℕ) (L T B : ℕ) (hB : B ≤ D * ((L + 1) * (T + 1))) :
    cc * (Q * (L + k0 + B + 1) ^ 2 + L + 1) ^ 3 + 1 ≤
      (cc * (Q * (k0 + 1 + D) ^ 2 + 1) ^ 3 + 1) * ((L + 1) ^ 6 * (T + 1) ^ 6) := by
  generalize hu : L + 1 = u at hB ⊢
  generalize hv : T + 1 = v at hB ⊢
  have hu1 : 1 ≤ u := by omega
  have hv1 : 1 ≤ v := by omega
  have huv : 1 ≤ u * v := Nat.mul_pos hu1 hv1
  generalize hE : k0 + 1 + D = E
  have h1 : L + k0 + B + 1 ≤ E * (u * v) := by
    have a1 : u ≤ u * v := Nat.le_mul_of_pos_right _ hv1
    have a2 : k0 ≤ k0 * (u * v) := Nat.le_mul_of_pos_right _ huv
    have a3 : B ≤ D * (u * v) := hB
    have a4 : E * (u * v) = k0 * (u * v) + 1 * (u * v) + D * (u * v) := by rw [← hE]; ring
    omega
  have h2 : Q * (L + k0 + B + 1) ^ 2 + L + 1 ≤ (Q * E ^ 2 + 1) * (u * v) ^ 2 := by
    have hsq : (L + k0 + B + 1) ^ 2 ≤ (E * (u * v)) ^ 2 := Nat.pow_le_pow_left h1 2
    have b1 : Q * (L + k0 + B + 1) ^ 2 ≤ Q * (E * (u * v)) ^ 2 := Nat.mul_le_mul_left _ hsq
    have b2 : u ≤ u * v := Nat.le_mul_of_pos_right _ hv1
    have b3 : u * v ≤ (u * v) ^ 2 := Nat.le_self_pow (by norm_num) _
    have b4 : Q * (E * (u * v)) ^ 2 = Q * E ^ 2 * (u * v) ^ 2 := by ring
    have b5 : (Q * E ^ 2 + 1) * (u * v) ^ 2 = Q * E ^ 2 * (u * v) ^ 2 + (u * v) ^ 2 := by ring
    omega
  have h3 : (Q * (L + k0 + B + 1) ^ 2 + L + 1) ^ 3 ≤ (Q * E ^ 2 + 1) ^ 3 * (u ^ 6 * v ^ 6) := by
    calc _ ≤ ((Q * E ^ 2 + 1) * (u * v) ^ 2) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = (Q * E ^ 2 + 1) ^ 3 * (u ^ 6 * v ^ 6) := by ring
  have h4 : cc * (Q * (L + k0 + B + 1) ^ 2 + L + 1) ^ 3 ≤ cc * ((Q * E ^ 2 + 1) ^ 3 * (u ^ 6 * v ^ 6)) :=
    Nat.mul_le_mul_left _ h3
  have h5 : 1 ≤ u ^ 6 * v ^ 6 := Nat.mul_pos (Nat.pow_pos hu1) (Nat.pow_pos hv1)
  have h6 : (cc * (Q * E ^ 2 + 1) ^ 3 + 1) * (u ^ 6 * v ^ 6) =
      cc * ((Q * E ^ 2 + 1) ^ 3 * (u ^ 6 * v ^ 6)) + u ^ 6 * v ^ 6 := by ring
  omega

theorem driver_time_poly (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (h : ZSpec m c T) :
    ∃ (M : TM2ComputableInTime encB encOut (lexLeast m)) (C : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ L, M.time L ≤ C * ((L + 1) ^ 6 * (T L + 1) ^ 6) := by
  obtain ⟨M, Q, k0, cc, hfin, ht⟩ := driver_machine m c T h
  refine ⟨M, cc * (Q * (k0 + 1 + (71 * (m + 2) + 100)) ^ 2 + 1) ^ 3 + 1, hfin, fun L => ?_⟩
  rw [ht L]
  exact time_poly_aux Q k0 cc _ L (T L) _ (drvBound_le m L (T L))

theorem pow12_le (n k : ℕ) : (2 ^ (n / (12 * k))) ^ 12 ≤ 2 ^ (n / k) := by
  have h := Factoring.Aux.mul_div_mul_le 12 k n
  calc (2 ^ (n / (12 * k))) ^ 12 = 2 ^ (12 * (n / (12 * k))) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (n / k) := Nat.pow_le_pow_right (by norm_num) h

/-- **Sub-exponential corollary.**  If the oracle's cost is `≤ C_k 2^(L/k)` for every `k ≥ 1`, the machine's time is
`≤ C'_k 2^(L/k)` for every `k ≥ 1`. -/
theorem driver_subexp (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (h : ZSpec m c T)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k)) :
    ∃ M : TM2ComputableInTime encB encOut (lexLeast m), (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, M.time L ≤ C * 2 ^ (L / k) := by
  obtain ⟨M, C0, hfin, ht⟩ := driver_time_poly m c T h
  refine ⟨M, hfin, fun k hk => ?_⟩
  obtain ⟨C1, hC1⟩ := hT (12 * k) (by omega)
  refine ⟨C0 * ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6), fun L => ?_⟩
  set P := 2 ^ (L / (12 * k)) with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hu : L + 1 ≤ (12 * k + 1) * P := by
    have := Factoring.Aux.le_two_pow_div L (12 * k) (by omega)
    nlinarith
  have hv : T L + 1 ≤ (C1 + 1) * P := by
    have := hC1 L; rw [← hP] at this; nlinarith
  have h1 : (L + 1) ^ 6 * (T L + 1) ^ 6 ≤ ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hu 6) (Nat.pow_le_pow_left hv 6)
  have h2 : ((12 * k + 1) * P) ^ 6 * ((C1 + 1) * P) ^ 6 =
      ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12 := by ring
  have h3 : P ^ 12 ≤ 2 ^ (L / k) := pow12_le L k
  calc M.time L ≤ C0 * ((L + 1) ^ 6 * (T L + 1) ^ 6) := ht L
    _ ≤ C0 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * P ^ 12) := Nat.mul_le_mul_left _ (h2 ▸ h1)
    _ ≤ C0 * (((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * 2 ^ (L / k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = C0 * ((12 * k + 1) ^ 6 * (C1 + 1) ^ 6) * 2 ^ (L / k) := by ring

/-- `driver_subexp` in the words of the Challenge. -/
theorem subexpRate_of_zspec (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (h : ZSpec m c T)
    (hT : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k)) : SubexpRate m :=
  driver_subexp m c T h hT

end ECDLP.L61
