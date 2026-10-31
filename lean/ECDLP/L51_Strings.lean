import Mathlib
import ECDLP.L51_Count

/-!
# L51 / Strings: L35's set `strings (n+1) (p,a,b,xR,yR,π)` and the filtered `GenSet`

`ncard_strings_eq` : `(strings (n+1) (p,a,b,xR,yR,π)).ncard = #{P ∈ GenSet … | π <+: strOf p ℓ P}`
(`ℓ = Nat.size B`, `B = sInf {B | p ≤ B^(n+1)}`).  The sign bit needs no special treatment: the
count is of decompositions, and `strOf` (x-bits + sign bit) is injective on them.
-/
namespace ECDLP.L51

open Finset ECDLP.L46 ECDLP.L44 ECDLP.L30

variable {p : ℕ} [Fact p.Prime]

/-- L35's curve. -/
abbrev Wc (p a b : ℕ) : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, (a : ZMod p), (b : ZMod p)⟩

/-- the `xy` of L35's `strings` -/
def xyf {a b : ℕ} : (Wc p a b).toAffine.Point → ZMod p × ZMod p
  | .zero => (0, 0)
  | .some x y _ => (x, y)

theorem xyf_eq {a b : ℕ} (Q : (Wc p a b).toAffine.Point) :
    xyf Q = ECDLP.L30.coord (Wc p a b).toAffine Q := by
  cases Q <;> rfl

open Classical in
theorem mem_strings (n a b xR yR : ℕ) (π : List Bool) (hΔ : (Wc p a b).Δ ≠ 0)
    {R0 : (Wc p a b).toAffine.Point} (hR0 : R0 ≠ 0)
    (hc : ECDLP.L30.coord _ R0 = ((xR : ZMod p), (yR : ZMod p)))
    (s : List Bool) :
    s ∈ ECDLP.strings (n + 1) (p, a, b, xR, yR, π) ↔
      ∃ t ∈ Dec (Wc p a b).toAffine (fun x => x.val < sInf {B | p ≤ B ^ (n + 1)}) n R0,
        π <+: strOf p (Nat.size (sInf {B | p ≤ B ^ (n + 1)})) (fun i => ECDLP.L30.coord _ (t i)) ∧
        strOf p (Nat.size (sInf {B | p ≤ B ^ (n + 1)})) (fun i => ECDLP.L30.coord _ (t i)) = s := by
  have hp : p.Prime := Fact.out
  simp only [ECDLP.strings, dif_pos hp, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, P, hs, hpre, hP0, hgen, hsum0, hxy⟩
    have key := (cond_iff (n := n) _ (sInf {B | p ≤ B ^ (n + 1)})
      (xR : ZMod p) (yR : ZMod p) P).1 ⟨fun i => ?_, fun k hk => ?_, hsum0, ?_⟩
    · obtain ⟨R, hRne, hRc, hmem⟩ := key
      have hRR : R = R0 := coord_inj hRne hR0 (hRc.trans hc.symm)
      subst hRR
      have hs' : strOf p (Nat.size (sInf {B | p ≤ B ^ (n + 1)})) (fun i => ECDLP.L30.coord _ (P i)) = s :=
        by rw [← hs]; unfold strOf chunk; congr 2; funext i; beta_reduce
           generalize P i = Q; cases Q <;> rfl
      exact ⟨P, hmem, hs' ▸ hpre, hs'⟩
    · have h := hP0 i
      revert h; generalize P i = Q; cases Q <;> exact id
    · have h := hgen k hk
      revert h
      generalize (List.take (↑k) (List.ofFn P)).sum = S
      generalize P k = Q
      cases S <;> cases Q <;> exact id
    · have h := hxy
      revert h
      generalize (List.ofFn P).sum = S
      cases S <;> exact id
  · rintro ⟨t, ht, hpre, rfl⟩
    have := (cond_iff (n := n) _ (sInf {B | p ≤ B ^ (n + 1)})
      (xR : ZMod p) (yR : ZMod p) t).2 ⟨R0, hR0, hc, ht⟩
    refine ⟨hΔ, t, by unfold strOf chunk; congr 2; funext i; beta_reduce; generalize t i = Q; cases Q <;> rfl, hpre, fun i => ?_, fun k hk => ?_, this.2.2.1, ?_⟩
    · have h := this.1 i
      revert h; generalize t i = Q; cases Q <;> exact id
    · have h := this.2.1 k hk
      revert h
      generalize (List.take (↑k) (List.ofFn t)).sum = S
      generalize t k = Q
      cases S <;> cases Q <;> exact id
    · have h := this.2.2.2
      revert h
      generalize (List.ofFn t).sum = S
      cases S <;> exact id

theorem coord_curve {a b : ℕ} (Q : (Wc p a b).toAffine.Point) (hQ : Q ≠ 0) :
    (ECDLP.L30.coord _ Q).2 * (ECDLP.L30.coord _ Q).2 =
      (ECDLP.L30.coord _ Q).1 ^ 3 + (a : ZMod p) * (ECDLP.L30.coord _ Q).1 + (b : ZMod p) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h =>
    have := (WeierstrassCurve.Affine.equation_iff _ _).1 h.1
    simp only [ECDLP.L30.coord]
    simp at this
    linear_combination this

open Classical in
/-- **(1)** L35's string set has as many elements as the generic decompositions whose string has
prefix `π` (the points of Mathlib are replaced by their coordinates). -/
theorem ncard_strings_eq (n a b xR yR : ℕ) (π : List Bool) (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p)) :
    (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard =
      ((GenSet (Wc p a b).toAffine (fun x : ZMod p => x.val < sInf {B | p ≤ B ^ (n + 1)})
        ((xR : ZMod p), (yR : ZMod p)) n).filter
          (fun P => π <+: strOf p (Nat.size (sInf {B | p ≤ B ^ (n + 1)})) P)).card := by
  set Bd := sInf {B | p ≤ B ^ (n + 1)} with hBd
  have hR0 : (WeierstrassCurve.Affine.Point.some _ _ hRns : (Wc p a b).toAffine.Point) ≠ 0 := nofun
  let R0 : (Wc p a b).toAffine.Point := .some _ _ hRns
  have hc : ECDLP.L30.coord _ R0 = ((xR : ZMod p), (yR : ZMod p)) := rfl
  let f : (Fin (n + 1) → (Wc p a b).toAffine.Point) → List Bool :=
    fun t => strOf p (Nat.size Bd) (fun i => ECDLP.L30.coord _ (t i))
  let T := (Dec (Wc p a b).toAffine (fun x : ZMod p => x.val < Bd) n R0).filter
    (fun t => π <+: f t)
  have hset : ECDLP.strings (n + 1) (p, a, b, xR, yR, π) = f '' (T : Set _) := by
    ext s
    rw [mem_strings n a b xR yR π hΔ hR0 hc]
    simp only [Set.mem_image, Finset.mem_coe, T, mem_filter]
    constructor
    · rintro ⟨t, ht, hpre, rfl⟩; exact ⟨t, ⟨ht, hpre⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hpre⟩, rfl⟩; exact ⟨t, ht, hpre, rfl⟩
  have hinj : Set.InjOn f (T : Set _) := by
    intro t ht t' ht' h
    simp only [Finset.mem_coe, T, mem_filter] at ht ht'
    have m1 := (mem_Dec (W := (Wc p a b).toAffine) _ n R0 t).1 ht.1
    have m2 := (mem_Dec (W := (Wc p a b).toAffine) _ n R0 t').1 ht'.1
    have := strOf_inj p (a : ZMod p) (b : ZMod p) (Nat.size Bd) (fun i => ECDLP.L30.coord _ (t i))
      (fun i => ECDLP.L30.coord _ (t' i)) (fun i => coord_curve _ (m1.1 i).1)
      (fun i => coord_curve _ (m2.1 i).1)
      (fun i => by
        have := (m1.1 i).2
        rw [xco_eq_coord] at this
        exact lt_trans this (Nat.lt_size_self Bd))
      (fun i => by
        have := (m2.1 i).2
        rw [xco_eq_coord] at this
        exact lt_trans this (Nat.lt_size_self Bd)) h
    funext i
    exact coord_inj (m1.1 i).1 (m2.1 i).1 (congrFun this i)
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset]
  have := card_dec_filter_eq (W := (Wc p a b).toAffine) (fun x : ZMod p => x.val < Bd) n hR0
    (fun P => π <+: strOf p (Nat.size Bd) P)
  convert this using 2 <;> first | rfl | (ext t; simp only [T, f, mem_filter]; exact Iff.rfl)

end ECDLP.L51

#print axioms ECDLP.L51.ncard_strings_eq
