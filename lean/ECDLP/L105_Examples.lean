import ECDLP.L35_Challenge
open ECDLP WeierstrassCurve.Affine
set_option maxHeartbeats 800000

theorem two_iff (p a b xR yR : ℕ) (π s : List Bool) (hp : p.Prime) :
    s ∈ strings 2 (p,a,b,xR,yR,π) ↔
    (haveI := Fact.mk hp
     (WeierstrassCurve.Δ (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)) ≠ 0 ∧
     ∃ x0 y0 x1 y1 : ZMod p, y0^2 = x0^3 + a*x0 + b ∧ y1^2 = x1^3 + a*x1 + b ∧
       x0.val < sInf {B | p ≤ B ^ 2} ∧ x1.val < sInf {B | p ≤ B ^ 2} ∧ x0 ≠ x1 ∧
       ((y0-y1)/(x0-x1))^2 - x0 - x1 = xR ∧
       -(((y0-y1)/(x0-x1)) * ((((y0-y1)/(x0-x1))^2 - x0 - x1) - x0) + y0) = yR ∧
       ((List.range (Nat.size (sInf {B | p ≤ B ^ 2}))).reverse.map (fun j => x0.val.testBit j) ++ [decide ((p - 1) / 2 < y0.val)] ++
        ((List.range (Nat.size (sInf {B | p ≤ B ^ 2}))).reverse.map (fun j => x1.val.testBit j) ++ [decide ((p - 1) / 2 < y1.val)])) = s ∧ π <+: s)) := by
  haveI := Fact.mk hp
  simp only [strings, hp, dite_true, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hΔ, P, hs, hπ, hx, hk, hsum, hR⟩
    refine ⟨hΔ, ?_⟩
    have hl : List.ofFn P = [P 0, P 1] := by simp [List.ofFn_succ]
    have hk1 := hk 1 (by simp)
    simp only [hl, Fin.val_one, List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, add_zero] at hk1 hsum hR hs
    obtain ⟨h0, b0⟩ := hx 0
    obtain ⟨h1, b1⟩ := hx 1
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, List.flatten_cons, List.flatten_nil, List.append_nil] at hs
    clear hk hx hl
    rcases hq0 : P 0 with _ | ⟨x0, y0, n0⟩
    · exact absurd hq0 h0
    rcases hq1 : P 1 with _ | ⟨x1, y1, n1⟩
    · exact absurd hq1 h1
    simp only [hq0, hq1] at hk1 hR hs b0 b1
    have hne : x0 ≠ x1 := hk1.2
    have hxy : ¬(x0 = x1 ∧ y0 = (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine.negY x1 y1) := fun h => hne h.1
    rw [Point.add_some hxy] at hR
    simp only [Prod.mk.injEq] at hR
    have e0 := n0.1
    have e1 := n1.1
    simp [WeierstrassCurve.Affine.equation_iff] at e0 e1
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne] at hR
    refine ⟨x0, y0, x1, y1, e0, e1, b0, b1, hne, ?_, ?_, hs, hπ⟩
    · have := hR.1
      simpa [WeierstrassCurve.Affine.addX] using this
    · have := hR.2
      simpa [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY] using this
  · rintro ⟨hΔ, x0, y0, x1, y1, e0, e1, b0, b1, hne, hX, hY, hs, hπ⟩
    refine ⟨hΔ, ?_⟩
    have n0 : (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine.Nonsingular x0 y0 :=
      (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (by simp [WeierstrassCurve.Affine.equation_iff]; linear_combination e0)
    have n1 : (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine.Nonsingular x1 y1 :=
      (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (by simp [WeierstrassCurve.Affine.equation_iff]; linear_combination e1)
    have hxy : ¬(x0 = x1 ∧ y0 = (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)).toAffine.negY x1 y1) := fun h => hne h.1
    have hadd := Point.add_some hxy (h₁ := n0) (h₂ := n1)
    refine ⟨![Point.some x0 y0 n0, Point.some x1 y1 n1], ?_, hπ, ?_, ?_, ?_, ?_⟩
    · rw [← hs]; simp [List.ofFn_succ]; congr
    · intro i; fin_cases i <;> simp [b0, b1]
    · intro k hk; fin_cases k
      · simp at hk
      · simp [List.ofFn_succ, hne]
    · simp [List.ofFn_succ, hadd]
    · simp [List.ofFn_succ, hadd, WeierstrassCurve.Affine.slope_of_X_ne hne]
      refine ⟨?_, ?_⟩
      · exact hX
      · simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]; linear_combination hY

theorem lex_of_min (m : ℕ) (x : Inst) (s0 : List Bool) (h0 : s0 ∈ strings m x)
    (hmin : ∀ t ∈ strings m x, s0 ≤ t) : lexLeast m x = some s0 := by
  classical
  have : ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t := ⟨s0, h0, hmin⟩
  simp only [lexLeast, this, dite_true]
  have hm : this.choose = s0 := by
    have h1 := this.choose_spec.1
    have h2 := this.choose_spec.2 s0 h0
    exact le_antisymm h2 (hmin _ h1)
  rw [hm]

theorem sInf_sq (p B : ℕ) (h1 : p ≤ B ^ 2) (h2 : ∀ b < B, ¬ p ≤ b ^ 2) : sInf {B | p ≤ B ^ 2} = B := by
  apply le_antisymm (Nat.sInf_le (show B ∈ {B | p ≤ B ^ 2} from h1))
  by_contra hlt
  exact h2 _ (not_le.mp hlt) (Nat.sInf_mem (s := {B | p ≤ B ^ 2}) ⟨B, h1⟩)

def Cond (p B : ℕ) [Fact p.Prime] (a b xR yR : ℕ) (x0 y0 x1 y1 : ZMod p) : Prop :=
  y0^2 = x0^3 + a*x0 + b ∧ y1^2 = x1^3 + a*x1 + b ∧ x0.val < B ∧ x1.val < B ∧ x0 ≠ x1 ∧
  ((y0-y1)/(x0-x1))^2 - x0 - x1 = xR ∧
  -(((y0-y1)/(x0-x1)) * ((((y0-y1)/(x0-x1))^2 - x0 - x1) - x0) + y0) = yR

def Cond' (p B : ℕ) [Fact p.Prime] (a b xR yR : ℕ) (x0 y0 x1 y1 : ZMod p) : Prop :=
  y0^2 = x0^3 + a*x0 + b ∧ y1^2 = x1^3 + a*x1 + b ∧ x0.val < B ∧ x1.val < B ∧ x0 ≠ x1 ∧
  ∃ l : ZMod p, l * (x0 - x1) = y0 - y1 ∧ l^2 - x0 - x1 = xR ∧ -(l * ((l^2 - x0 - x1) - x0) + y0) = yR

theorem cond_iff (p B : ℕ) [Fact p.Prime] (a b xR yR : ℕ) (x0 y0 x1 y1 : ZMod p) :
    Cond p B a b xR yR x0 y0 x1 y1 ↔ Cond' p B a b xR yR x0 y0 x1 y1 := by
  unfold Cond Cond'
  constructor
  · rintro ⟨e0, e1, b0, b1, hne, hX, hY⟩
    refine ⟨e0, e1, b0, b1, hne, (y0-y1)/(x0-x1), ?_, hX, hY⟩
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hne)
  · rintro ⟨e0, e1, b0, b1, hne, l, hl, hX, hY⟩
    have : l = (y0-y1)/(x0-x1) := by
      rw [eq_div_iff (sub_ne_zero.mpr hne)]; exact hl
    subst this
    exact ⟨e0, e1, b0, b1, hne, hX, hY⟩

instance (p B : ℕ) [Fact p.Prime] (a b xR yR : ℕ) (x0 y0 x1 y1 : ZMod p) : Decidable (Cond' p B a b xR yR x0 y0 x1 y1) := by
  unfold Cond'; infer_instance

def Bits (p B : ℕ) [Fact p.Prime] (x0 y0 x1 y1 : ZMod p) : List Bool :=
  (List.range (Nat.size B)).reverse.map (fun j => x0.val.testBit j) ++ [decide ((p - 1) / 2 < y0.val)] ++
  ((List.range (Nat.size B)).reverse.map (fun j => x1.val.testBit j) ++ [decide ((p - 1) / 2 < y1.val)])

instance (p B : ℕ) [Fact p.Prime] (a b xR yR : ℕ) (x0 y0 x1 y1 : ZMod p) : Decidable (Cond p B a b xR yR x0 y0 x1 y1) := by
  unfold Cond; infer_instance

/-- generic reduction for m = 2 to a finite check -/
theorem ex2 (p a b xR yR B : ℕ) (hp : p.Prime) (hB : sInf {B | p ≤ B ^ 2} = B)
    (hΔ : haveI := Fact.mk hp; WeierstrassCurve.Δ (⟨0,0,0,(a:ZMod p),(b:ZMod p)⟩ : WeierstrassCurve (ZMod p)) ≠ 0)
    (s0 : List Bool) (hall : haveI := Fact.mk hp; ∀ x0 y0 x1 y1 : ZMod p, Cond' p B a b xR yR x0 y0 x1 y1 → s0 ≤ Bits p B x0 y0 x1 y1)
    (w : haveI := Fact.mk hp; ∃ x0 y0 x1 y1 : ZMod p, Cond' p B a b xR yR x0 y0 x1 y1 ∧ Bits p B x0 y0 x1 y1 = s0) :
    lexLeast 2 (p,a,b,xR,yR,[]) = some s0 := by
  haveI := Fact.mk hp
  apply lex_of_min
  · rw [two_iff _ _ _ _ _ _ _ hp]
    simp only [hB]
    obtain ⟨x0, y0, x1, y1, hc, hb⟩ := w
    obtain ⟨e0, e1, b0, b1, hne, hX, hY⟩ := (cond_iff ..).mpr hc
    exact ⟨hΔ, x0, y0, x1, y1, e0, e1, b0, b1, hne, hX, hY, hb, List.nil_prefix⟩
  · intro t ht
    rw [two_iff _ _ _ _ _ _ _ hp] at ht
    simp only [hB] at ht
    obtain ⟨_, x0, y0, x1, y1, e0, e1, b0, b1, hne, hX, hY, hs, _⟩ := ht
    rw [← hs]; exact hall x0 y0 x1 y1 ((cond_iff ..).mp ⟨e0, e1, b0, b1, hne, hX, hY⟩)

theorem E1 : lexLeast 2 (13,1,1,8,1,[]) = some [false,false,false,false,false,false,true,false] := by
  apply ex2 13 1 1 8 1 4 (by decide) (sInf_sq _ _ (by decide) (by decide))
  · decide +kernel
  · decide +kernel
  · exact ⟨0, 1, 1, 4, by decide +kernel, by decide +kernel⟩

theorem E2 : lexLeast 2 (13,1,1,8,12,[]) = some [false,false,false,true,false,false,true,true] := by
  apply ex2 13 1 1 8 12 4 (by decide) (sInf_sq _ _ (by decide) (by decide))
  · decide +kernel
  · decide +kernel
  · exact ⟨0, 12, 1, 9, by decide +kernel, by decide +kernel⟩

theorem lex_none_of_empty (m : ℕ) (x : Inst) (h : strings m x = ∅) : lexLeast m x = none := by
  classical
  have : ¬ ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t := by simp [h]
  simp [lexLeast, this]

theorem ex2none (p a b xR yR : ℕ) (hp : p.Prime) (B : ℕ)
    (hB : sInf {B | p ≤ B ^ 2} = B)
    (hall : haveI := Fact.mk hp; ∀ x0 y0 x1 y1 : ZMod p, ¬ Cond' p B a b xR yR x0 y0 x1 y1) :
    lexLeast 2 (p,a,b,xR,yR,[]) = none := by
  haveI := Fact.mk hp
  apply lex_none_of_empty
  ext s
  rw [two_iff _ _ _ _ _ _ _ hp]
  simp only [hB, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, x0, y0, x1, y1, e0, e1, b0, b1, hne, hX, hY, _, _⟩
  exact hall x0 y0 x1 y1 ((cond_iff ..).mp ⟨e0, e1, b0, b1, hne, hX, hY⟩)

/-- p = 13, R = (0,1): no generic decomposition with x < 4 (python brute force agrees) -/
theorem E4 : lexLeast 2 (13,1,1,0,1,[]) = none := by
  apply ex2none 13 1 1 0 1 (by decide) 4 (sInf_sq _ _ (by decide) (by decide))
  decide +kernel

#print axioms E1
#print axioms E2
#print axioms E4
#print axioms two_iff
