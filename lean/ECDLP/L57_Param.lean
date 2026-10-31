import ECDLP.L57_Fits

/-!
# L57 / Param: explicit parameter inequalities give `U ≤ C₁ m L` and `G · wmax ≤ C₂ L`

Arithmetic only.  With `D = 2^k` (`A·A = 2D`), digit bits `b ≤ β D`, ring-exponent multipliers `w c ≤ ω`
(so `M_c = D · w c`), at most `nmax` slots per identity, at most `occmax` identities per shared slot,
`K ≤ κ m` identities and `D² ≤ ν L`:
* `Wsum ≤ κ ν (4 nmax (β+ω+5) + 12 (ω+4)) · m · L`;
* every gate weight `Bw ≤ cw · A · D`, `cw = (occmax+1)(β+1) + (nmax+3)(ω+4)`;
* if `θ⁴ ≥ 4 ν³` and `G⁴ ≤ L` then `G · A · D ≤ θ L`.
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

theorem term_bound (a d n nm s e β ω : ℕ) (haa : a * a = 2 * d) (hn : n ≤ nm)
    (hs : s ≤ (β + 1) * d * a) (he : e ≤ (ω + 4) * d) :
    2 * n * a * s + 2 * n * a * a * e + 6 * a * a * e ≤
      d * d * (4 * nm * (β + ω + 5) + 12 * (ω + 4)) := by
  have h1 : 2 * n * a * s ≤ 2 * nm * a * ((β + 1) * d * a) := by gcongr
  have h2 : 2 * n * a * a * e ≤ 2 * nm * a * a * ((ω + 4) * d) := by gcongr
  have h3 : 6 * a * a * e ≤ 6 * a * a * ((ω + 4) * d) := by gcongr
  have e1 : 2 * nm * a * ((β + 1) * d * a) = 2 * nm * (β + 1) * d * (a * a) := by ring
  have e2 : 2 * nm * a * a * ((ω + 4) * d) = 2 * nm * (ω + 4) * d * (a * a) := by ring
  have e3 : 6 * a * a * ((ω + 4) * d) = 6 * (ω + 4) * d * (a * a) := by ring
  rw [e1, haa] at h1
  rw [e2, haa] at h2
  rw [e3, haa] at h3
  calc _ ≤ 2 * nm * (β + 1) * d * (2 * d) + 2 * nm * (ω + 4) * d * (2 * d) + 6 * (ω + 4) * d * (2 * d) := by omega
    _ = _ := by ring

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)

theorem hA_dd (N0 : NPar) : N0.A * N0.A = 2 * 2 ^ N0.k := by
  rw [N0.toPar.hA]; ring

theorem h_le_A (N0 : NPar) : N0.h ≤ N0.A := by
  have hA := N0.toPar.A_pos
  have h1 := N0.hAh
  have h2 := hA_dd N0
  have : N0.A * N0.h ≤ N0.A * N0.A := by rw [h1, h2]; have := Nat.one_le_two_pow (n := N0.k); omega
  exact Nat.le_of_mul_le_mul_left this hA

theorem eS_le (N0 : NPar) (β : ℕ) (hb : N0.b ≤ β * 2 ^ N0.k) :
    eS N0 ≤ (β + 1) * 2 ^ N0.k * N0.A := by
  have hA := N0.toPar.A_pos
  have hD : 1 ≤ 2 ^ N0.k := Nat.one_le_two_pow
  have h1 : N0.b * N0.h ≤ β * 2 ^ N0.k * N0.A :=
    Nat.mul_le_mul hb (h_le_A N0) |>.trans (by rw [mul_assoc])
  unfold eS
  have : 1 ≤ 2 ^ N0.k * N0.A := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

theorem eM_le (N0 : NPar) (w : Fin K → ℕ) (ω : ℕ) (hw : ∀ c, w c ≤ ω) (c : Fin K) :
    eM N0 w c ≤ (ω + 4) * 2 ^ N0.k := by
  have hD : 1 ≤ 2 ^ N0.k := Nat.one_le_two_pow
  unfold eM
  show 2 ^ N0.k * w c + 4 ≤ _
  nlinarith [hw c]

theorem Wsum_le (nmax β ω κ ν m L : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hw : ∀ c, w c ≤ ω)
    (hb : N0.b ≤ β * 2 ^ N0.k) (hDL : 2 ^ N0.k * 2 ^ N0.k ≤ ν * L) (hK : K ≤ κ * m) :
    Wsum N0 w (fun c => Fintype.card (ιc c)) ≤
      κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L := by
  unfold Wsum
  have hc : ∀ c : Fin K, 2 * Fintype.card (ιc c) * N0.A * eS N0 + 2 * Fintype.card (ιc c) * N0.A * N0.A * eM N0 w c
      + 6 * N0.A * N0.A * eM N0 w c ≤ 2 ^ N0.k * 2 ^ N0.k * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) :=
    fun c => term_bound N0.A (2 ^ N0.k) _ nmax _ _ β ω (hA_dd N0) (hn c) (eS_le N0 β hb) (eM_le N0 w ω hw c)
  refine (sum_le_sum fun c _ => hc c).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  calc K * (2 ^ N0.k * 2 ^ N0.k * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)))
      ≤ (κ * m) * ((ν * L) * (4 * nmax * (β + ω + 5) + 12 * (ω + 4))) := by gcongr
    _ = _ := by ring

theorem Bw_le (occmax nmax β ω : ℕ) (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax)
    (hw : ∀ c, w c ≤ ω) (hb : N0.b ≤ β * 2 ^ N0.k) (x : CG ι ιc N0.A) :
    Bw (w := w) φ x ≤ ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k) := by
  have hA := N0.toPar.A_pos
  have hS := eS_le N0 β hb
  have hA1 : 1 ≤ N0.A := hA
  set D := 2 ^ N0.k with hD
  have hD1 : 1 ≤ D := Nat.one_le_two_pow
  have hAD : 1 ≤ N0.A * D := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hP : ∀ q : ℕ, q ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) →
      ∀ y : ℕ, y ≤ q * (N0.A * D) → y ≤ ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * D) :=
    fun q hq y hy => hy.trans (Nat.mul_le_mul_right _ hq)
  have hPa : occmax * (β + 1) ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) := by
    nlinarith [Nat.zero_le (nmax * ω), Nat.zero_le (nmax), Nat.zero_le ω]
  have hPb : (β + 1) + (ω + 4) ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) := by
    nlinarith [Nat.zero_le (nmax * ω), Nat.zero_le (nmax), Nat.zero_le ω, Nat.zero_le (occmax * β), Nat.zero_le occmax]
  have hPc : (nmax + 1) * (ω + 4) ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) := by
    nlinarith [Nat.zero_le (nmax * ω), Nat.zero_le (nmax), Nat.zero_le ω, Nat.zero_le (occmax * β), Nat.zero_le occmax]
  have hPd : 2 * (ω + 4) ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) := by
    nlinarith [Nat.zero_le (nmax * ω), Nat.zero_le (nmax), Nat.zero_le ω, Nat.zero_le (occmax * β), Nat.zero_le occmax]
  have hPe : 3 * (ω + 4) ≤ (occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4) := by
    nlinarith [Nat.zero_le (nmax * ω), Nat.zero_le (nmax), Nat.zero_le ω, Nat.zero_le (occmax * β), Nat.zero_le occmax]
  cases x with
  | src i s =>
    have := hocc i
    refine hP (occmax * (β + 1)) hPa _ ?_
    simp only [Bw]
    calc occ φ i * eS N0 ≤ occmax * ((β + 1) * D * N0.A) := Nat.mul_le_mul this hS
      _ = _ := by ring
  | gt c g =>
    have hE : eM N0 w c ≤ (ω + 4) * D := eM_le N0 w ω hw c
    have hnc := hn c
    cases g with
    | fa j s =>
      refine hP ((β + 1) + (ω + 4)) hPb _ ?_
      simp only [Bw]
      calc eS N0 + N0.A * eM N0 w c ≤ (β + 1) * D * N0.A + N0.A * ((ω + 4) * D) := Nat.add_le_add hS (Nat.mul_le_mul_left _ hE)
        _ = _ := by ring
    | mid k =>
      refine hP ((nmax + 1) * (ω + 4)) hPc _ ?_
      simp only [Bw]
      calc Fintype.card (ιc c) * N0.A * eM N0 w c + N0.A * eM N0 w c ≤ nmax * N0.A * ((ω + 4) * D) + N0.A * ((ω + 4) * D) :=
            Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_right _ hnc) hE) (Nat.mul_le_mul_left _ hE)
        _ = _ := by ring
    | ib j =>
      refine hP (2 * (ω + 4)) hPd _ ?_
      simp only [Bw]
      calc N0.A * eM N0 w c + N0.A * eM N0 w c ≤ N0.A * ((ω + 4) * D) + N0.A * ((ω + 4) * D) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hE) (Nat.mul_le_mul_left _ hE)
        _ = _ := by ring
    | car j =>
      refine hP (3 * (ω + 4)) hPe _ ?_
      simp only [Bw]
      have h3 : eM N0 w c ≤ N0.A * ((ω + 4) * D) :=
        hE.trans (Nat.le_mul_of_pos_left _ hA)
      calc 2 * eM N0 w c + eM N0 w c ≤ 2 * (N0.A * ((ω + 4) * D)) + N0.A * ((ω + 4) * D) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ h3) h3
        _ = _ := by ring

end

theorem quartic_bound (a d ν θ G L : ℕ) (haa : a * a = 2 * d) (hdL : d * d ≤ ν * L) (hθ : 4 * ν ^ 3 ≤ θ ^ 4)
    (hG : G ^ 4 ≤ L) : G * (a * d) ≤ θ * L := by
  by_contra hcon
  push Not at hcon
  have h4 : (θ * L) ^ 4 < (G * (a * d)) ^ 4 := Nat.pow_lt_pow_left hcon (by norm_num)
  have e1 : (G * (a * d)) ^ 4 = G ^ 4 * ((a * a) * (a * a)) * (d ^ 4) := by ring
  rw [e1, haa] at h4
  have h5 : d ^ 4 * d ^ 2 ≤ (ν * L) ^ 3 := by
    calc d ^ 4 * d ^ 2 = (d * d) ^ 3 := by ring
      _ ≤ (ν * L) ^ 3 := Nat.pow_le_pow_left hdL 3
  have h6 : (θ * L) ^ 4 ≥ 4 * ν ^ 3 * L ^ 4 := by
    rw [mul_pow]; exact Nat.mul_le_mul_right _ hθ
  have h7 : G ^ 4 * (2 * d * (2 * d)) * d ^ 4 ≤ L * (4 * (ν * L) ^ 3) := by
    calc G ^ 4 * (2 * d * (2 * d)) * d ^ 4 = G ^ 4 * 4 * (d ^ 4 * d ^ 2) := by ring
      _ ≤ L * 4 * ((ν * L) ^ 3) := by gcongr
      _ = _ := by ring
  have e2 : L * (4 * (ν * L) ^ 3) = 4 * ν ^ 3 * L ^ 4 := by ring
  omega

end ECDLP.L57
end
