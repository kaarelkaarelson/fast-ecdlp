import FactoringAux.Moduli

/-!
# L113 / Crt: the pure arithmetic of the sequential (lcm) Chinese remainder reconstruction
State `(X, P)` with `P > 0`, `X < P`, `X ≡ N (mod P)`.  For a modulus `j` with residue `N mod j`:
`u` = least positive with `j ∣ u P`, `s` = least with `X + s P ≡ N (mod j)`.  Then `s < u`, `X + s P < u P`, `X + sP ≡ N (mod uP)`.
At the end `P` is a positive common multiple of `1..J`, hence `N < P` and `X = N`.
-/
set_option linter.unusedVariables false
namespace ECDLP.L113

theorem crt_exists (N X P j u : ℕ) (hP : 0 < P) (hX : X < P) (hXN : X % P = N % P) (hu1 : 1 ≤ u) (hu3 : j ∣ u * P) :
    ∃ s0, s0 < u ∧ (X + s0 * P) % j = N % j := by
  refine ⟨(N / P) % u, Nat.mod_lt _ (by omega), ?_⟩
  obtain ⟨c, hc⟩ := hu3
  have h1 : N = X + P * (N / P) := by
    have := Nat.mod_add_div N P
    rw [← hXN, Nat.mod_eq_of_lt hX] at this
    omega
  have h2 : N / P = (N / P) % u + u * ((N / P) / u) := (Nat.mod_add_div _ _).symm
  set t := N / P
  set q := t / u
  set s0 := t % u
  have : N = (X + s0 * P) + j * c * q := by
    rw [h1]; nth_rewrite 1 [h2]
    have : u * P = j * c := hc
    calc X + P * (s0 + u * q) = X + s0 * P + (u * P) * q := by ring
      _ = _ := by rw [this]
  rw [this, mul_assoc, Nat.add_mul_mod_self_left]


theorem crt_step (N X P j s u : ℕ) (hP : 0 < P) (hX : X < P) (hXN : X % P = N % P) (hu1 : 1 ≤ u) (hu3 : j ∣ u * P)
    (hu4 : ∀ v, 1 ≤ v → v < u → ¬ j ∣ v * P)
    (hs2 : (X + s * P) % j = N % j) (hs3 : ∀ k, k < s → (X + k * P) % j ≠ N % j) :
    s < u ∧ X + s * P < u * P ∧ (X + s * P) % (u * P) = N % (u * P) := by
  obtain ⟨s0, hs0, hs0'⟩ := crt_exists N X P j u hP hX hXN hu1 hu3
  have hsu : s < u := by
    by_contra h
    exact hs3 s0 (by omega) hs0'
  refine ⟨hsu, ?_, ?_⟩
  · nlinarith
  · -- Y = X + s P is ≡ N mod P and mod j, hence mod u P
    set Y := X + s * P with hY
    have hYP : Y % P = N % P := by rw [hY, Nat.add_mul_mod_self_right, hXN]
    have e1 : (P : ℤ) ∣ (N : ℤ) - Y := by
      have : Y ≡ N [MOD P] := hYP
      exact (Nat.modEq_iff_dvd.mp this)
    have e2 : (j : ℤ) ∣ (N : ℤ) - Y := by
      have : Y ≡ N [MOD j] := hs2
      exact (Nat.modEq_iff_dvd.mp this)
    obtain ⟨y, hy⟩ := e1
    have hu3' : (j : ℤ) ∣ (u : ℤ) * P := by exact_mod_cast hu3
    set q := y / (u : ℤ) with hq
    set r := y % (u : ℤ) with hr
    have hur : (u : ℤ) * q + r = y := Int.mul_ediv_add_emod y u
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hr1 : r < u := Int.emod_lt_of_pos _ (by omega)
    have hjr : (j : ℤ) ∣ r * P := by
      have : (j : ℤ) ∣ (P : ℤ) * y - (u * P) * q := by
        rw [hy] at e2; exact dvd_sub e2 (dvd_mul_of_dvd_left hu3' q)
      have e : (P : ℤ) * y - (u * P) * q = r * P := by rw [← hur]; ring
      rwa [e] at this
    have hr' : r = 0 := by
      by_contra hne
      have hpos : 1 ≤ r.toNat := by omega
      have := hu4 r.toNat hpos (by omega)
      apply this
      have e : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
      have : (j : ℤ) ∣ ((r.toNat * P : ℕ) : ℤ) := by push_cast; rw [e]; exact hjr
      exact_mod_cast this
    rw [hr', add_zero] at hur
    have : ((u * P : ℕ) : ℤ) ∣ (N : ℤ) - Y := ⟨q, by rw [hy, ← hur]; push_cast; ring⟩
    exact (Nat.modEq_iff_dvd.mpr this : Y ≡ N [MOD u * P])

theorem crt_final {N X P J : ℕ} (hP : 0 < P) (hX : X < P) (hXN : X % P = N % P)
    (hdiv : ∀ i, 1 ≤ i → i ≤ J → i ∣ P)
    (hbig : ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ J → i ∣ Y) → N < Y) : X = N := by
  have := hbig P hP hdiv
  rw [Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt this] at hXN
  exact hXN

theorem big_of_lt {N M : ℕ} (hM : 0 < M) (hN : (2 * M + 1) * N < 4 ^ M) :
    ∀ Y, 0 < Y → (∀ i, 1 ≤ i → i ≤ 2 * M → i ∣ Y) → N < Y := by
  intro Y hY hd
  by_contra h
  have : (2 * M + 1) * Y < 4 ^ M := lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hN
  have := Factoring.Aux.eq_zero_of_all_dvd hM hd this
  omega

end ECDLP.L113
