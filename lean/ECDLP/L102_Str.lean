import ECDLP.L102_Arith

/-!
# L102 / Str: for `m = 1` the strings of an instance are `{bitsR}` (if the prefix fits) or empty
-/
noncomputable section
namespace ECDLP.L102
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L70 ECDLP.L92 WeierstrassCurve.Affine

/-- the string of the point `R = (X, Y)`: `size p` bits of `X` (big-endian) then the sign bit of `Y` -/
def bitsR (p x y : ℕ) : List Bool :=
  (List.range (Nat.size p)).reverse.map (fun j => x.testBit j) ++ [decide ((p - 1) / 2 < y)]

theorem sInf_one (p : ℕ) : sInf {B | p ≤ B ^ 1} = p := by
  apply le_antisymm
  · exact Nat.sInf_le (by simp)
  · exact le_csInf ⟨p, by simp⟩ (fun b hb => by simpa using hb)

theorem SO_one (p : ℕ) (hp : p.Prime) (A Bc X Y : ZMod p) (π : List Bool)
    (hΔ : (⟨0, 0, 0, A, Bc⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0)
    (hns : (⟨0, 0, 0, A, Bc⟩ : WeierstrassCurve (ZMod p)).toAffine.Nonsingular X Y) :
    SO 1 p hp A Bc X Y π = if π <+: bitsR p X.val Y.val then {bitsR p X.val Y.val} else ∅ := by
  haveI := Fact.mk hp
  have hB : sInf {B | p ≤ B ^ 1} = p := sInf_one p
  ext s
  simp only [SO, hB]
  constructor
  · rintro ⟨-, P, hP, hπ, hP0, -, hsum, hxy⟩
    have h0 : P 0 ≠ 0 := (hP0 0).1
    have hs : (List.ofFn P).sum = P 0 := by simp [List.ofFn_succ]
    rw [hs] at hxy
    have hPi : P = fun _ => P 0 := funext fun i => by fin_cases i; rfl
    rw [hPi] at hP
    revert hP hπ hxy h0
    generalize P 0 = Q
    intro hP hπ hxy h0
    cases Q with
    | zero => exact absurd rfl h0
    | some x y h =>
        simp only [xyP, Prod.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        have hstr : s = bitsR p x.val y.val := by
          rw [← hP]; simp [bitsR, List.ofFn_succ, xyP]; exact decide_eq_decide.2 Iff.rfl
        subst hstr
        simp [hπ]
  · intro h
    split_ifs at h with hpre
    · have hs : s = bitsR p X.val Y.val := by simpa using h
      subst hs
      refine ⟨hΔ, fun _ => Point.some X Y hns, ?_, hpre, ?_, ?_, ?_, ?_⟩
      · simp [bitsR, List.ofFn_succ, xyP]; exact decide_eq_decide.2 Iff.rfl
      · intro i; refine ⟨by simp, ?_⟩
        simp only [xyP]; have := ZMod.val_lt X; simpa using this
      · intro k hk; exact absurd k.2 (by omega)
      · simp [List.ofFn_succ]
      · simp [List.ofFn_succ, xyP]
    · simp at h


theorem Zc_one (x : Inst) (τ : List Bool) (hg : Good 1 x τ) :
    Zc 1 x τ = if τ <+: bitsR x.1 (x.2.2.2.1 % x.1) (x.2.2.2.2.1 % x.1) then 1 else 0 := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨hp, hΔ, hns, -⟩ := hg
  unfold Zc withPre
  simp only
  rw [strings_eq_SO, dif_pos hp, SO_one p hp _ _ _ _ τ hΔ hns]
  simp only [ZMod.val_natCast]
  split_ifs <;> simp


/-- the `q`-th expected bit -/
def eF (p x y q : ℕ) : Bool := if q < Nat.size p then x.testBit (Nat.size p - 1 - q) else decide ((p - 1) / 2 < y)

theorem length_bitsR (p x y : ℕ) : (bitsR p x y).length = Nat.size p + 1 := by simp [bitsR]

theorem bitsR_get (p x y i : ℕ) (hi : i < Nat.size p + 1) : (bitsR p x y)[i]? = some (eF p x y i) := by
  unfold bitsR eF
  by_cases h : i < Nat.size p
  · rw [List.getElem?_append_left (by simp [h]), if_pos h]
    simp [List.getElem?_reverse, h]
  · have : i = Nat.size p := by omega
    subst this
    rw [List.getElem?_append_right (by simp)]
    simp

theorem prefix_bitsR (τ : List Bool) (p x y : ℕ) :
    τ <+: bitsR p x y ↔ τ.length ≤ Nat.size p + 1 ∧ ∀ q (h : q < τ.length), τ[q] = eF p x y q := by
  rw [List.prefix_iff_getElem?]
  constructor
  · intro H
    have hl : τ.length ≤ Nat.size p + 1 := by
      by_contra hc
      have := H (Nat.size p + 1) (by omega)
      rw [List.getElem?_eq_none (by rw [length_bitsR])] at this
      exact absurd this (by simp)
    refine ⟨hl, fun q h => ?_⟩
    have := H q h
    rw [bitsR_get p x y q (by omega)] at this
    exact (Option.some.inj this).symm
  · rintro ⟨hl, H⟩ i hi
    rw [bitsR_get p x y i (by omega), H i hi]

end ECDLP.L102
