import ECDLP.L92_LookOk

/-!
# L92 / Count: `Zc m x τ <= (2 B)^(m-1)` (the last point is determined by the first `m-1`), and `Zc < 2^len` for large `p`
-/
noncomputable section
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L70

section pts
variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))

/-- a point is determined by its `x`-value and its sign bit -/
def encP (P : W.toAffine.Point) : ℕ × Bool := ((xyP W P).1.val, decide ((p - 1) / 2 < (xyP W P).2.val))

theorem xyP_inj {P Q : W.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : xyP W P = xyP W Q) : P = Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y hxy =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x' y' hxy' =>
      simp only [xyP, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem encP_inj (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {P Q : W.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : encP W P = encP W Q) : P = Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y hxy =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x' y' hxy' =>
      simp only [encP, xyP, Prod.mk.injEq] at h
      obtain ⟨hx, hs⟩ := h
      have hx' : x = x' := ZMod.val_injective p hx
      subst hx'
      have e1 := (WeierstrassCurve.Affine.equation_iff (W := W.toAffine) x y).1 hxy.1
      have e2 := (WeierstrassCurve.Affine.equation_iff (W := W.toAffine) x y').1 hxy'.1
      rw [ha1, ha3] at e1 e2
      have e3 : (y - y') * (y + y') = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.1 e3 with h1 | h1
      · have : y = y' := sub_eq_zero.1 h1
        subst this; rfl
      · have hy' : y' = -y := by linear_combination h1
        by_cases hyy : y = y'
        · subst hyy; rfl
        · exfalso
          have hy0 : y ≠ 0 := by
            intro h0; apply hyy; rw [hy', h0]; simp
          have hv : y'.val = p - y.val := by
            rw [hy', ZMod.neg_val, if_neg hy0]
          have hlt : y.val < p := ZMod.val_lt y
          have hne : y.val ≠ y'.val := fun h => hyy (ZMod.val_injective p h)
          have hpos : 0 < y.val := Nat.pos_of_ne_zero (fun h => hy0 ((ZMod.val_eq_zero y).1 h))
          have hb : ((p - 1) / 2 < y.val) ↔ ((p - 1) / 2 < y'.val) := decide_eq_decide.1 hs
          rw [hv] at hb hne
          omega

end pts

theorem count_le (n p : ℕ) (hp : p.Prime) (A Bc X Y : ZMod p) (π : List Bool) :
    (SO (n + 1) p hp A Bc X Y π).ncard ≤ (sInf {B | p ≤ B ^ (n + 1)} * 2) ^ n := by
  haveI := Fact.mk hp
  set B := sInf {B | p ≤ B ^ (n + 1)} with hB
  set W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, A, Bc⟩ with hW
  have ha1 : W.a₁ = 0 := rfl
  have ha3 : W.a₃ = 0 := rfl
  let V : Set (Fin (n + 1) → W.toAffine.Point) := {P | (∀ i, P i ≠ 0 ∧ (xyP W (P i)).1.val < B) ∧
    (List.ofFn P).sum ≠ 0 ∧ xyP W (List.ofFn P).sum = (X, Y)}
  let Ψ : (Fin (n + 1) → W.toAffine.Point) → (Fin n → ℕ × Bool) := fun P i => encP W (P i.castSucc)
  let T : Finset (Fin n → ℕ × Bool) := Fintype.piFinset fun _ => (Finset.range B) ×ˢ (Finset.univ : Finset Bool)
  have hmaps : Set.MapsTo Ψ V (↑T : Set _) := by
    intro P hP
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
      and_true]
    intro i
    exact (hP.1 i.castSucc).2
  have hinj : Set.InjOn Ψ V := by
    intro P hP P' hP' hΨ
    have hi : ∀ i : Fin n, P i.castSucc = P' i.castSucc := fun i =>
      encP_inj W ha1 ha3 (hP.1 _).1 (hP'.1 _).1 (congr_fun hΨ i)
    have hsum : (List.ofFn P).sum = (List.ofFn P').sum :=
      xyP_inj W hP.2.1 hP'.2.1 (by rw [hP.2.2, hP'.2.2])
    rw [List.sum_ofFn, List.sum_ofFn, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    have hs1 : ∑ i : Fin n, P i.castSucc = ∑ i : Fin n, P' i.castSucc := Finset.sum_congr rfl fun i _ => hi i
    rw [hs1] at hsum
    have hl : P (Fin.last n) = P' (Fin.last n) := add_left_cancel hsum
    funext i
    refine Fin.lastCases ?_ (fun j => hi j) i
    exact hl
  have hVfin : V.Finite := Set.Finite.of_injOn hmaps hinj T.finite_toSet
  have h1 : V.ncard ≤ T.card := by
    calc V.ncard ≤ (↑T : Set _).ncard := Set.ncard_le_ncard_of_injOn Ψ (fun a ha => hmaps ha) hinj T.finite_toSet
      _ = T.card := Set.ncard_coe_finset T
  have hTc : T.card = (B * 2) ^ n := by
    simp [T, Fintype.card_piFinset]
  let str : (Fin (n + 1) → W.toAffine.Point) → List Bool := fun P => (List.ofFn fun i =>
    (List.range (Nat.size B)).reverse.map (fun j => (xyP W (P i)).1.val.testBit j) ++
      [decide ((p - 1) / 2 < (xyP W (P i)).2.val)]).flatten
  have hsub : SO (n + 1) p hp A Bc X Y π ⊆ str '' V := by
    intro s hs
    obtain ⟨-, P, hPs, -, h1, -, h3, h4⟩ := hs
    exact ⟨P, ⟨h1, h3, h4⟩, hPs⟩
  calc (SO (n + 1) p hp A Bc X Y π).ncard ≤ (str '' V).ncard := Set.ncard_le_ncard hsub (hVfin.image _)
    _ ≤ V.ncard := Set.ncard_image_le hVfin
    _ ≤ (B * 2) ^ n := by rw [← hTc]; exact h1

end ECDLP.L92
end

noncomputable section
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L70

/-- **The count bound for large `p`**: `Zc < 2^len` whenever `3 m^2 <= size p`. -/
theorem zc_lt (r : ℕ) (x : Inst) (τ : List Bool) (hg : Good (r + 1) x τ) (hsp : 3 * (r + 1) ^ 2 ≤ Nat.size x.1) :
    Zc (r + 1) x τ < 2 ^ (redInp x τ).len := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hp : p.Prime := hg.1
  simp only at hsp
  have hZ : Zc (r + 1) (p, a, b, xR, yR, π) τ ≤ (sInf {B | p ≤ B ^ (r + 1)} * 2) ^ r := by
    unfold Zc withPre
    simp only
    rw [strings_eq_SO, dif_pos hp]
    exact count_le r p hp _ _ _ _ τ
  set sp := Nat.size p with hsp'
  set q := sp / (r + 1) with hq
  have hmq : (r + 1) * q ≤ sp := Nat.mul_div_le sp (r + 1)
  have hq3 : 3 * (r + 1) ≤ q := by
    rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
  have hlt : sp < (r + 1) * (q + 1) := by
    have := Nat.lt_mul_div_succ sp (show 0 < r + 1 by omega)
    exact this
  have hB : sInf {B | p ≤ B ^ (r + 1)} ≤ 2 ^ (q + 1) := by
    apply Nat.sInf_le
    show p ≤ (2 ^ (q + 1)) ^ (r + 1)
    rw [← pow_mul]
    have h1 : p < 2 ^ sp := Nat.lt_size_self p
    have h2 : 2 ^ sp ≤ 2 ^ ((q + 1) * (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have hB2 : sInf {B | p ≤ B ^ (r + 1)} * 2 ≤ 2 ^ (q + 2) := by
    calc sInf {B | p ≤ B ^ (r + 1)} * 2 ≤ 2 ^ (q + 1) * 2 := Nat.mul_le_mul_right _ hB
      _ = 2 ^ (q + 2) := by ring
  have hlen : sp + 1 ≤ (redInp (p, a, b, xR, yR, π) τ).len := by
    simp only [redInp, ECDLP.L65.EdgeInp.len]; omega
  have hexp : (q + 2) * r < (redInp (p, a, b, xR, yR, π) τ).len := by
    have : (q + 2) * r ≤ sp := by nlinarith
    omega
  calc Zc (r + 1) (p, a, b, xR, yR, π) τ ≤ (sInf {B | p ≤ B ^ (r + 1)} * 2) ^ r := hZ
    _ ≤ (2 ^ (q + 2)) ^ r := Nat.pow_le_pow_left hB2 r
    _ = 2 ^ ((q + 2) * r) := by rw [← pow_mul]
    _ < 2 ^ (redInp (p, a, b, xR, yR, π) τ).len := Nat.pow_lt_pow_right (by norm_num) hexp

end ECDLP.L92
end

noncomputable section
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L70

theorem sInf_le_pow (p m : ℕ) (hm : 0 < m) : sInf {B | p ≤ B ^ m} ≤ 2 ^ (Nat.size p / m + 1) := by
  apply Nat.sInf_le
  show p ≤ (2 ^ (Nat.size p / m + 1)) ^ m
  rw [← pow_mul]
  have h1 : p < 2 ^ Nat.size p := Nat.lt_size_self p
  have hlt := Nat.lt_mul_div_succ (Nat.size p) hm
  have h2 : 2 ^ Nat.size p ≤ 2 ^ ((Nat.size p / m + 1) * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

/-- length of the reduced input of a good query -/
theorem len_red_ub (r : ℕ) (x : Inst) (τ : List Bool) (hg : Good (r + 1) x τ) :
    (redInp x τ).len ≤ 6 * Nat.size x.1 + 3 * (r + 1) + 1 := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨hp, -, -, hl⟩ := hg
  have hp0 : 0 < p := hp.pos
  have s1 : Nat.size (a % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt a hp0).le
  have s2 : Nat.size (b % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt b hp0).le
  have s3 : Nat.size (xR % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt xR hp0).le
  have s4 : Nat.size (yR % p) ≤ Nat.size p := Nat.size_le_size (Nat.mod_lt yR hp0).le
  have hB := sInf_le_pow p (r + 1) (by omega)
  have hs : Nat.size (sInf {B | p ≤ B ^ (r + 1)}) ≤ Nat.size p / (r + 1) + 2 := by
    have := Nat.size_le_size hB
    rw [Nat.size_pow] at this; omega
  have hn : nlen (r + 1) (p, a, b, xR, yR, π) ≤ Nat.size p + 3 * (r + 1) := by
    unfold nlen
    simp only
    have h1 : (r + 1) * (Nat.size (sInf {B | p ≤ B ^ (r + 1)}) + 1) ≤ (r + 1) * (Nat.size p / (r + 1) + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 := Nat.mul_div_le (Nat.size p) (r + 1)
    nlinarith
  have hτ : τ.length ≤ Nat.size p + 3 * (r + 1) := le_trans hl hn
  simp only [redInp, ECDLP.L65.EdgeInp.len]
  omega

/-- **`hlt` on long inputs**: `Zc < 2^len` as soon as `len >= T0 m`. -/
def T0of (r : ℕ) : ℕ := 18 * (r + 1) ^ 2 + 3 * (r + 1) + 1

theorem zc_lt_len (r : ℕ) (x : Inst) (τ : List Bool) (hg : Good (r + 1) x τ) (hlen : T0of r ≤ (redInp x τ).len) :
    Zc (r + 1) x τ < 2 ^ (redInp x τ).len := by
  apply zc_lt r x τ hg
  have := len_red_ub r x τ hg
  unfold T0of at hlen
  omega

end ECDLP.L92
end
