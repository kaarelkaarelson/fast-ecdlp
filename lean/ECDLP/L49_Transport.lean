import Mathlib
import ECDLP.L49_Iso
import ECDLP.L46_Bridge
import ECDLP.L46_Cover

/-!
# L49 (1'): transport of discrete logs and of decomposition counts along `E ≅ E_u`

* `dilEquiv A B u : E.Point ≃+ E_u.Point` (additive isomorphism, `(x,y) ↦ (u²x, u³y)`).
* `dlp_transfer` : `Q = d • P ↔ dil Q = d • dil P` (DLP on `E` is DLP on `E_u`).
* `Gen_eq_E` : `Gen T n (u⁴A) (u⁶B)` (the coverage count of the chain) equals the number of
  `R ∈ E.Point` having an ordered generic decomposition into `n+1` points of `E` whose
  dilated x-coordinates `u²x` lie in `T` (the box `{x : u²x ∈ T}` for the fixed curve `E`).
-/
namespace ECDLP.L49

open Finset WeierstrassCurve WeierstrassCurve.Affine ECDLP.L43 ECDLP.L46 ECDLP.L40

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem ns_undil (A B : K) (u : Kˣ) {x y : K} (h : (Eu A B u).Nonsingular x y) :
    (shortW A B).Nonsingular (((u⁻¹ : Kˣ) : K) ^ 2 * x) (((u⁻¹ : Kˣ) : K) ^ 3 * y) := by
  have h' := ns_dil ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) u⁻¹ h
  have hu : (u : K) ≠ 0 := u.ne_zero
  have e : Eu ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) u⁻¹ = shortW A B := by
    simp only [Eu, shortW, Units.val_inv_eq_inv_val]
    congr 1 <;> field_simp
  rw [e] at h'
  exact h'

/-- the inverse map (junk-free: defined on all points) -/
def undilFun (A B : K) (u : Kˣ) : (Eu A B u).Point → (shortW A B).Point
  | .zero => .zero
  | .some x y h => .some _ _ (ns_undil A B u h)

theorem dil_undil (A B : K) (u : Kˣ) (P : (Eu A B u).Point) :
    dil A B u (undilFun A B u P) = P := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  cases P with
  | zero => rfl
  | some x y h =>
    show dilFun A B u (undilFun A B u (.some x y h)) = _
    simp only [undilFun, dilFun, Units.val_inv_eq_inv_val]
    congr 1 <;> field_simp

theorem dil_surjective (A B : K) (u : Kˣ) : Function.Surjective (dil A B u) :=
  fun P => ⟨undilFun A B u P, dil_undil A B u P⟩

/-- **The isomorphism of point groups `E ≅ E_u`.** -/
noncomputable def dilEquiv (A B : K) (u : Kˣ) : (shortW A B).Point ≃+ (Eu A B u).Point :=
  AddEquiv.ofBijective (dil A B u) ⟨dil_injective A B u, dil_surjective A B u⟩

/-- DLP transfer: `Q = d • P` on `E` iff the images satisfy it on `E_u`. -/
theorem dlp_transfer (A B : K) (u : Kˣ) (P Q : (shortW A B).Point) (d : ℕ) :
    Q = d • P ↔ dil A B u Q = d • dil A B u P := by
  rw [← map_nsmul]
  exact ⟨fun h => by rw [h], fun h => dil_injective A B u h⟩

theorem xc_dil (A B : K) (u : Kˣ) (P : (shortW A B).Point) :
    xc _ (dil A B u P) = (xc _ P).map (fun x => (u : K) ^ 2 * x) := by
  show xc _ (dilFun A B u P) = _
  cases P <;> rfl

theorem psum_dil {m : ℕ} (A B : K) (u : Kˣ) (i : Fin m) (t : Fin m → (shortW A B).Point) :
    psum i (fun j => dil A B u (t j)) = dil A B u (psum i t) := by
  unfold psum; rw [map_sum]

theorem generic_dil {n : ℕ} (A B : K) (u : Kˣ) (t : Fin (n + 1) → (shortW A B).Point) :
    Generic (xc (Eu A B u)) (fun j => dil A B u (t j)) ↔ Generic (xc (shortW A B)) t := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hinj : Function.Injective (fun x : K => (u : K) ^ 2 * x) :=
    fun a b h => mul_left_cancel₀ (pow_ne_zero _ hu) h
  unfold Generic
  refine forall_congr' (fun k => ?_)
  rw [psum_dil, xc_dil, xc_dil]
  have h0 : dil A B u (psum k.succ t) ≠ 0 ↔ psum k.succ t ≠ 0 := by
    rw [Ne, Ne, ← map_zero (dil A B u)]
    exact not_congr (dil_injective A B u).eq_iff
  rw [h0, Ne, Ne, (Option.map_injective hinj).eq_iff]

open Classical in
theorem card_dec_dil {n : ℕ} (A B : K) (u : Kˣ) (FB : K → Prop) (R : (shortW A B).Point) :
    (Dec (Eu A B u) FB n (dil A B u R)).card =
      (Dec (shortW A B) (fun x => FB ((u : K) ^ 2 * x)) n R).card := by
  symm
  refine card_bij (fun t _ => fun j => dil A B u (t j)) ?_ ?_ ?_
  · intro t ht
    simp only [Dec, fbase, mem_filter, Fintype.mem_piFinset, mem_univ, true_and] at ht ⊢
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨fun j => ⟨?_, ?_⟩, (generic_dil A B u t).2 h2, ?_⟩
    · rw [Ne, ← map_zero (dil A B u)]; exact fun h => (h1 j).1 (dil_injective A B u h)
    · have := (h1 j).2
      show FB (xco _ (dil A B u (t j)))
      rw [xco_dil]; exact this
    · rw [← map_sum, h3]
  · intro t ht t' ht' h
    funext j
    exact dil_injective A B u (congrFun h j)
  · intro s hs
    simp only [Dec, fbase, mem_filter, Fintype.mem_piFinset, mem_univ, true_and] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    choose t ht using fun j => dil_surjective A B u (s j)
    have hs' : s = fun j => dil A B u (t j) := funext fun j => (ht j).symm
    refine ⟨t, ?_, hs'.symm⟩
    subst hs'
    simp only [Dec, fbase, mem_filter, Fintype.mem_piFinset, mem_univ, true_and]
    refine ⟨fun j => ⟨?_, ?_⟩, (generic_dil A B u t).1 h2, ?_⟩
    · intro h0; apply (h1 j).1
      change dil A B u (t j) = 0
      rw [h0, map_zero]
    · have := (h1 j).2
      change FB (xco _ (dil A B u (t j))) at this
      rw [xco_dil] at this; exact this
    · apply dil_injective A B u
      rw [map_sum]; exact h3

open Classical in
/-- **Coverage count = number of `R ∈ E` with a generic decomposition in the dilated box.** -/
theorem Gen_eq_E (T : Finset K) (n : ℕ) (A B : K) (u : Kˣ) :
    Gen T n ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) =
      (univ.filter (fun R : (shortW A B).Point =>
        (Dec (shortW A B) (fun x => (u : K) ^ 2 * x ∈ T) n R).Nonempty)).card := by
  rw [Gen_eq]
  symm
  refine card_bij (fun R _ => dil A B u R) ?_ ?_ ?_
  · intro R hR
    simp only [mem_filter, mem_univ, true_and] at hR ⊢
    rw [← card_pos] at hR ⊢
    have := card_dec_dil (n := n) A B u (fun x => x ∈ T) R
    show 0 < (Dec (Eu A B u) (fun x => x ∈ T) n (dil A B u R)).card
    rw [this]; exact hR
  · intro R _ R' _ h; exact dil_injective A B u h
  · intro R' hR'
    obtain ⟨R, rfl⟩ := dil_surjective A B u R'
    refine ⟨R, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and] at hR' ⊢
    rw [← card_pos] at hR' ⊢
    have := card_dec_dil (n := n) A B u (fun x => x ∈ T) R
    rw [← this]; exact hR'

end ECDLP.L49
