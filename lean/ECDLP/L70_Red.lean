import ECDLP.L70_Wrap

/-!
# L70 / Red: the edge input of a driver query, and its length

`redInp x τ` = the `EdgeInp` `(p, a % p, b % p, xR % p, yR % p, τ)`.  For `Good (r+1) x τ` it is `adm r` (`adm_red`)
and its length is at most `(r+7) (|encB x| + 1)` (`len_red_le`).
-/
namespace ECDLP.L70
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 Computability

/-- the reduced edge input of a query -/
def redInp (x : Inst) (τ : List Bool) : EdgeInp :=
  ⟨x.1, x.2.1 % x.1, x.2.2.1 % x.1, x.2.2.2.1 % x.1, x.2.2.2.2.1 % x.1, τ⟩

theorem Wc_red (p a b : ℕ) : Wc p (a % p) (b % p) = Wc p a b := by
  simp [Wc, ZMod.natCast_mod]

theorem adm_red (r : ℕ) (x : Inst) (τ : List Bool) (h : Good (r + 1) x τ) : (redInp x τ).adm r := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨hp, hΔ, hns, hl⟩ := h
  have hp0 : 0 < p := hp.pos
  refine ⟨hp, Nat.mod_lt _ hp0, Nat.mod_lt _ hp0, Nat.mod_lt _ hp0, Nat.mod_lt _ hp0, ?_, ?_, ?_⟩
  · show (Wc p (a % p) (b % p)).Δ ≠ 0
    rw [Wc_red]; exact hΔ
  · show (Wc p (a % p) (b % p)).toAffine.Nonsingular (((xR % p : ℕ)) : ZMod p) (((yR % p : ℕ)) : ZMod p)
    rw [Wc_red, ZMod.natCast_mod, ZMod.natCast_mod]; exact hns
  · exact hl

theorem len_red_le (m : ℕ) (x : Inst) (τ : List Bool) (h : Good m x τ) :
    (redInp x τ).len ≤ (m + 6) * ((encB x).length + 1) := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨hp, -, -, hl⟩ := h
  have hp0 : 0 < p := hp.pos
  have h1 : Nat.size p ≤ (encodeNat p).length := by
    rw [Nat.size_le]; exact Factoring.Aux.Trial.lt_two_pow_length p
  have h2 : (encodeNat p).length ≤ (encB (p, a, b, xR, yR, π)).length := len_encB_ge p a b xR yR π
  have h3 := nlen_le m p a b xR yR π
  have s1 : Nat.size (a % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt a hp0).le
  have s2 : Nat.size (b % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt b hp0).le
  have s3 : Nat.size (xR % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt xR hp0).le
  have s4 : Nat.size (yR % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt yR hp0).le
  have key : (redInp (p, a, b, xR, yR, π) τ).len ≤ 5 * Nat.size p + τ.length + 1 := by
    show Nat.size p + Nat.size (a % p) + Nat.size (b % p) + Nat.size (xR % p) + Nat.size (yR % p) + τ.length + 1 ≤ _
    omega
  have hl' : τ.length ≤ m * ((encodeNat p).length + 1) := le_trans hl h3
  set L := (encB (p, a, b, xR, yR, π)).length
  have : m * ((encodeNat p).length + 1) ≤ m * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

end ECDLP.L70
