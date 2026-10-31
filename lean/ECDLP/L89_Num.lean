import ECDLP.L84_PExB0
import ECDLP.L65_Params
import ECDLP.L65_Fam

/-!
# L89 / Num: the numeric side conditions `FaNum`, `MidNum`, `NodeNum`, `DecNum`-parts, ... against the value bound `V` of `EdgeReq`

All of them are consequences of `hset : 2 ^ Sb n <= V` (a field of L65's `EdgeReq`, `Sb n = 19680 X^3`) and the explicit parameters
(`A <= 3X`, `A D <= 12 X^3`, `b <= 36 D`, `M = D w <= 80 D`, `eS = b h + 1 <= 37 A D`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L89
open Factoring.Aux ECDLP.L59 ECDLP.L65 ECDLP.L79 ECDLP.L84 ECDLP.L54

theorem two_pow_ge_self (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

/-- any number `<= Sb n` is `<= V` -/
theorem le_V {n V x : ℕ} (hset : 2 ^ Sb n ≤ V) (hx : x ≤ Sb n) : x ≤ V :=
  le_trans (le_trans hx (Nat.lt_two_pow_self).le) hset

theorem pow_le_V {n V t : ℕ} (hset : 2 ^ Sb n ≤ V) (ht : t ≤ Sb n) : 2 ^ t ≤ V :=
  le_trans (Nat.pow_le_pow_right (by norm_num) ht) hset

theorem Sb_ge (n : ℕ) : 19680 * Xs n ^ 3 = Sb n := rfl

/-- the explicit parameter bounds in terms of `X = Xs n` -/
structure ParB (L n : ℕ) : Prop where
  hA : AP L ≤ 3 * Xs n
  hD : DP L ≤ 12 * Xs n ^ 3
  hAD : AP L * DP L ≤ 12 * Xs n ^ 3
  hM : DP L * wP L ≤ 960 * Xs n ^ 3
  hb : bP L ≤ 432 * Xs n ^ 3
  hbh : bP L * hP L ≤ 444 * Xs n ^ 3
  hw : wP L ≤ 80

theorem parB (L n : ℕ) (hn : L + 4 ≤ 4 * n) : ParB L n := by
  have hAX := A_le_X L n hn
  have hADX := AD_le_X L n hn
  have hA1 : 1 ≤ AP L := Nat.one_le_two_pow
  have hD2 := DP_ge_two L
  have hX := Xs_pos n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  have hD : DP L ≤ 12 * Xs n ^ 3 := le_trans (Nat.le_mul_of_pos_left _ hA1) hADX
  have hMl := M_le L
  have hbl := bP_le L
  have hes := eS_le_explicit L
  have hes' : bP L * hP L + 1 ≤ 37 * (AP L * DP L) := hes
  refine ⟨hAX, hD, hADX, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · have : DP L * wP L ≤ 80 * DP L := hMl
    exact Nat.le_of_mul_le_mul_left (by linarith) (show 0 < DP L by omega)

theorem two_pow_le_V_of_le {n V : ℕ} (hset : 2 ^ Sb n ≤ V) (t : ℕ) (ht : t ≤ Sb n) : 2 ^ t ≤ V := pow_le_V hset ht

theorem Xs_le_cube (n : ℕ) : Xs n ≤ Xs n ^ 3 := by
  have := Xs_pos n
  calc Xs n = Xs n ^ 1 := (pow_one _).symm
    _ ≤ Xs n ^ 3 := Nat.pow_le_pow_right this (by norm_num)

theorem sq_le_cube (n : ℕ) : Xs n ^ 2 ≤ Xs n ^ 3 := Nat.pow_le_pow_right (Xs_pos n) (by norm_num)

theorem s_lt_Xs (n : ℕ) : sOf n < Xs n := Nat.lt_two_pow_self

theorem X5_le_V {n V : ℕ} (hset : 2 ^ Sb n ≤ V) : 19440 * Xs n ^ 5 ≤ V := by
  have e : Xs n ^ 5 = 2 ^ (5 * sOf n) := by unfold Xs; rw [← pow_mul]; ring_nf
  have h1 : 19440 * Xs n ^ 5 ≤ 2 ^ (5 * sOf n + 15) := by
    rw [e, pow_add]
    have : 19440 ≤ 2 ^ 15 := by norm_num
    nlinarith [Nat.two_pow_pos (5 * sOf n)]
  refine le_trans h1 (pow_le_V hset ?_)
  have := s_lt_Xs n
  have := Xs_le_cube n
  have : Sb n = 19680 * Xs n ^ 3 := rfl
  omega

section
variable {K : ℕ}

/-- **FaNum, MidNum, the ib numeric conditions and NodeNum for the real parameters, from `2^(Sb n) <= V`.** -/
theorem edge_num (L n : ℕ) (hn : L + 4 ≤ 4 * n) {V : ℕ} (hset : 2 ^ Sb n ≤ V) :
    FaNum V (NParE L) (fun _ : Fin K => wP L) ∧ MidNum V (NParE L) (fun _ : Fin K => wP L) ∧
    (∀ c : Fin K, (fun _ : Fin K => wP L) c * ((NParE L).A * (NParE L).A) * ((NParE L).A * (NParE L).A * (NParE L).A) ≤ V) ∧
    NodeNum V (NParE L) (fun _ : Fin K => wP L) ∧ (NParE L).A * (NParE L).A ≤ V ∧ 8 ≤ V ∧
    (∀ c : Fin K, 2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).M ≤ V) := by
  obtain ⟨hA, hD, hAD, hM, hb, hbh, hw⟩ := parB L n hn
  have hX := Xs_pos n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  have hSb : Sb n = 19680 * Xs n ^ 3 := rfl
  have hMc : ∀ c : Fin K, (NP (NParE L) (fun _ : Fin K => wP L) c).M = DP L * wP L := fun c => rfl
  have hA1 : 1 ≤ AP L := Nat.one_le_two_pow
  have hA3 : AP L * AP L * AP L ≤ 27 * Xs n ^ 3 := by
    have : AP L * AP L * AP L ≤ (3 * Xs n) * (3 * Xs n) * (3 * Xs n) := Nat.mul_le_mul (Nat.mul_le_mul hA hA) hA
    calc _ ≤ _ := this
      _ = 27 * Xs n ^ 3 := by ring
  have hAA : AP L * AP L ≤ 9 * Xs n ^ 3 := by
    have : AP L * AP L ≤ (3 * Xs n) * (3 * Xs n) := Nat.mul_le_mul hA hA
    have h2 := sq_le_cube n
    calc _ ≤ _ := this
      _ = 9 * Xs n ^ 2 := by ring
      _ ≤ 9 * Xs n ^ 3 := by omega
  have hA3V : AP L * AP L * AP L ≤ V := le_V hset (by omega)
  have hAAV : AP L * AP L ≤ V := le_V hset (by omega)
  have hw1 : 1 ≤ wP L := by unfold wP; exact Nat.le_add_left _ _
  have hqq : ∀ c : Fin K, (2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).M + 1) *
      (2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).M + 1) ≤ V := by
    intro c
    rw [hMc c]
    have h1 : (2 ^ (DP L * wP L) + 1) * (2 ^ (DP L * wP L) + 1) ≤ 2 ^ (2 * (DP L * wP L) + 2) := by
      have : 1 ≤ 2 ^ (DP L * wP L) := Nat.one_le_two_pow
      have e : 2 ^ (2 * (DP L * wP L) + 2) = 4 * (2 ^ (DP L * wP L) * 2 ^ (DP L * wP L)) := by
        rw [pow_add, pow_mul']; ring_nf
      rw [e]; nlinarith
    exact le_trans h1 (pow_le_V hset (by omega))
  have hwA : ∀ c : Fin K, wP L * (AP L * AP L * AP L) ≤ V := fun c =>
    le_V hset (by have := Nat.mul_le_mul hw hA3; omega)
  have hX5 := X5_le_V (n := n) hset
  have hw5 : wP L * (AP L * AP L) * (AP L * AP L * AP L) ≤ V := by
    refine le_trans ?_ hX5
    have h1 : AP L * AP L ≤ 9 * Xs n ^ 2 := by
      have : AP L * AP L ≤ (3 * Xs n) * (3 * Xs n) := Nat.mul_le_mul hA hA
      calc _ ≤ _ := this
        _ = 9 * Xs n ^ 2 := by ring
    calc wP L * (AP L * AP L) * (AP L * AP L * AP L) ≤ 80 * (9 * Xs n ^ 2) * (27 * Xs n ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul hw h1) hA3
      _ = 19440 * Xs n ^ 5 := by ring
  have hM1 : ∀ c : Fin K, 1 ≤ (NP (NParE L) (fun _ : Fin K => wP L) c).M := fun c => by
    rw [hMc c]; have := DP_pos L; exact Nat.mul_pos this hw1
  have hMV : ∀ c : Fin K, 2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).M ≤ V := fun c => by
    rw [hMc c]; exact pow_le_V hset (by omega)
  have hBh : (2 ^ bP L) ^ hP L ≤ V := by
    rw [← pow_mul]; exact pow_le_V hset (by omega)
  refine ⟨⟨hqq, hA1, hA3V, hwA, fun c => hBh, hM1⟩, ⟨hqq, hA1, hA3V, hwA, fun c => ?_, hM1⟩, fun c => hw5, ?_, hAAV, ?_, hMV⟩
  · -- hEA
    refine le_trans ?_ hX5
    have h1 : AP L * AP L - 1 ≤ 9 * Xs n ^ 2 := by
      have : AP L * AP L ≤ (3 * Xs n) * (3 * Xs n) := Nat.mul_le_mul hA hA
      have e : (3 * Xs n) * (3 * Xs n) = 9 * Xs n ^ 2 := by ring
      omega
    calc wP L * (AP L * AP L - 1) * (AP L * AP L * AP L) ≤ 80 * (9 * Xs n ^ 2) * (27 * Xs n ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul hw h1) hA3
      _ = 19440 * Xs n ^ 5 := by ring
  · refine ⟨?_, ?_, ?_, hBh, ?_, ?_, ?_⟩
    · exact le_V hset (by have : hP L ≤ AP L := by unfold hP AP; exact Nat.pow_le_pow_right (by norm_num) (by omega)
                          have := Xs_le_cube n; simp only [NParE_h]; omega)
    · exact le_V hset (by simp only [NParE_b]; omega)
    · exact pow_le_V hset (by simp only [NParE_b]; omega)
    · exact le_V hset (by simp only [NParE_b, NParE_h]; omega)
    · intro c
      rw [hMc c] at *
      have h8 : 8 * 2 ^ (DP L * wP L) + 1 ≤ 2 ^ (DP L * wP L + 4) := by
        have : 1 ≤ 2 ^ (DP L * wP L) := Nat.one_le_two_pow
        rw [pow_add]; norm_num; omega
      exact le_trans h8 (pow_le_V hset (by omega))
    · intro c
      show (NP (NParE L) (fun _ : Fin K => wP L) c).M + 3 ≤ V
      rw [hMc c]; exact le_V hset (by omega)
  · exact le_V hset (by omega)
end

end ECDLP.L89
end
