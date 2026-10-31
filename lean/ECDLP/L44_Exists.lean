import ECDLP.L44_Main

/-!
# L44 / Exists: the network parameters can always be chosen (non-vacuity of `main_count`)

For every instance there are `N : NPar`, `B` satisfying all size hypotheses of `main_count`: `b = 1`,
`k = 2Z+1`, `A = 2^(Z+1)`, `h = 2^Z`, `B = 6 (2^(2^k))² + 1`, `w = T + 1` with `T = 2·mass·2^k·4`
(`mass` = mass of the combined form), where `Z` bounds all constants and `ℓ`.
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst ECDLP.L34 ECDLP.L35 ECDLP.L38

variable {n K : ℕ}

theorem params_exist (I : Inst) (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (ℓ Z : ℕ)
    (hZ : ∀ c, I.cv c < Z) (hℓ : ℓ ≤ Z) :
    ∃ (N : NPar) (B : ℤ), 1 ≤ N.b ∧ ℓ ≤ N.b * 2 ^ N.k ∧ (∀ c, I.cv c < 2 ^ (N.b * 2 ^ N.k)) ∧ 0 < B ∧
      (∀ c, ((famF sg e c).mass : ℤ) * ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B) ∧
      N.SizeOK (combine (famF sg e) B) := by
  set k : ℕ := 2 * Z + 1 with hk
  set B : ℤ := 6 * (((2 ^ (1 * 2 ^ k) : ℕ) : ℤ)) ^ 2 + 1 with hB
  set T : ℕ := 2 * (combine (famF sg e) B).mass * (2 ^ k * 4) with hT
  let N : NPar :=
    { k := k, A := 2 ^ (Z + 1), w := T + 1, b := 1, h := 2 ^ Z
      hA := by rw [← pow_add]; congr 1; omega
      hAh := by rw [← pow_add]; congr 1; omega }
  have hZk : Z < 2 ^ k := lt_of_le_of_lt (by omega : Z ≤ k) (Nat.lt_two_pow_self)
  have hk2 : 2 ^ k < 2 ^ (1 * 2 ^ k) := by
    rw [one_mul]; exact Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self
  have hbW : N.b * 2 ^ N.k = 1 * 2 ^ k := rfl
  refine ⟨N, B, le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbW]; omega
  · intro c
    rw [hbW]
    have := hZ c
    have h3 : (Z : ℤ) < 2 ^ (1 * 2 ^ k) := by exact_mod_cast lt_trans hZk hk2
    exact lt_trans (by exact_mod_cast this) h3
  · rw [hB]; positivity
  · intro c
    rw [hbW]
    have h6 : (famF sg e c).mass ≤ 6 := mass_le sg (e.symm c)
    have h7 : ((famF sg e c).mass : ℤ) ≤ 6 := by exact_mod_cast h6
    have h8 : (0 : ℤ) ≤ (((2 ^ (1 * 2 ^ k) : ℕ) : ℤ)) ^ 2 := by positivity
    rw [hB]
    nlinarith
  · refine ⟨?_, ?_, ?_⟩
    · show 1 ≤ 2 ^ k * (T + 1)
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · show 2 * 2 ^ k ≤ 2 ^ (Z + 1) * 2 ^ (Z + 1)
      rw [← pow_add, show Z + 1 + (Z + 1) = k + 1 by omega, pow_succ]
      exact le_of_eq (by ring)
    · show 2 * ((combine (famF sg e) B).mass * (2 ^ k * (2 ^ 1 * 2 ^ 1))) ≤ 2 ^ (2 ^ k * (T + 1))
      have h1 : 2 * ((combine (famF sg e) B).mass * (2 ^ k * (2 ^ 1 * 2 ^ 1))) = T := by
        rw [hT]; ring
      rw [h1]
      calc T ≤ 2 ^ T := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (2 ^ k * (T + 1)) := Nat.pow_le_pow_right (by norm_num) (by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          nlinarith)

/-- The packed network of an instance and prefix, as a `Net` value. -/
def packedValue (I : Inst) (N : NPar) (B : ℤ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K) {g : ℕ}
    (eg : Gate (Slot n) N.A ≃ Fin g) : ℤ :=
  (((gadgetNet N (combine (famF (fun i : Fin (n + 1) => sgOf ℓ π i) e) B)
    (okC N (Cl I (N.b * 2 ^ N.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
      (fun i : Fin (n + 1) => xcOf ℓ π i)))).toForced.toGNet).toNet eg).value

open Classical in
/-- **Main theorem (non-vacuous form).** For every instance and prefix there is a network (explicit parameters)
whose value is the number of generic factor-base decompositions whose string has the prefix. -/
theorem main_exists (I : Inst) [hpp : Fact I.p.Prime] [(shortW I.p I.a I.b).IsElliptic]
    (π : List Bool) (ℓ : ℕ) (hlen : π.length ≤ (n + 1) * (ℓ + 1)) (e : Cn n ≃ Fin K)
    (ha0 : 0 ≤ I.a) (ha : I.a < I.p) (hb0 : 0 ≤ I.b) (hb : I.b < I.p) (hXp : I.X ≤ I.p)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hO : 2 * (I.p : ℤ) ≤ I.O) (hN : I.O + 2 * (I.p : ℤ) < I.N)
    (hR : 0 ≤ I.R.1 ∧ I.R.1 < I.p ∧ 0 ≤ I.R.2 ∧ I.R.2 < I.p)
    (hRns : (shortW I.p I.a I.b).Nonsingular (I.R.1 : ZMod I.p) (I.R.2 : ZMod I.p)) :
    ∃ (N : NPar) (B : ℤ) (g : ℕ) (eg : Gate (Slot n) N.A ≃ Fin g), 1 ≤ N.b ∧
      packedValue I N B π ℓ e eg =
        ((((GenSet (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X)
          ((I.R.1 : ZMod I.p), (I.R.2 : ZMod I.p)) n).filter
            (fun P => π <+: strOf I.p ℓ P)).card : ℕ) : ℤ) := by
  set Z : ℕ := ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 with hZdef
  have hZ : ∀ c, I.cv c < Z := by
    intro c
    have h1 : (I.cv c).toNat ≤ Finset.univ.sup fun c : Cst => (I.cv c).toNat :=
      Finset.le_sup (f := fun c : Cst => (I.cv c).toNat) (Finset.mem_univ c)
    have h2 := Int.self_le_toNat (I.cv c)
    have : (I.cv c) < ((ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 : ℕ) : ℤ) := by
      push_cast
      have h3 : ((I.cv c).toNat : ℤ) ≤ ((Finset.univ.sup fun c : Cst => (I.cv c).toNat : ℕ) : ℤ) := by
        exact_mod_cast h1
      have : (0 : ℤ) ≤ ℓ := by positivity
      linarith
    exact this
  obtain ⟨N, B, hb1, hℓN, hcvB, hB, hBd, hS⟩ := params_exist I (fun i : Fin (n + 1) => sgOf ℓ π i) e ℓ Z hZ
    (by omega)
  refine ⟨N, B, _, Fintype.equivFin _, hb1, ?_⟩
  exact main_count I N π ℓ hℓN hlen e ha0 ha hb0 hb hXp hXX hO hN hR hRns hcvB B hB hBd hS hb1 _

end ECDLP.L44
end

#print axioms ECDLP.L44.main_exists
#check @ECDLP.L44.main_exists
