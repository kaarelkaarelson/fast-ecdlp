import Mathlib

/-!
# L114 / Unif: (c) the uniformity lemma S1 (counting form)

Abstract data: finite tag group `A` (in the application `(ZMod N)^4`), `ev : A →+ G` (tags ↦ points),
`ρ : A →+ Loc` (reduction to the `ℓ`-part), `K ≤ Loc` the local relation lattice, with
`ρ (ker ev) = K` (`ker_reduces`).  Rows `i : ι` carry tags `a i ∈ A` with `ev (a i) = T i`.
`Φ_Λ(a)_j = ∑_i Λ_ji • ρ(a i)`.

* `unif_fibres` : if `Λ` has a right inverse and every `Φ_Λ(a)` (over the coset `ev a = T`) lands in `K^κ`,
  then all points of `K^κ` have the same number of preimages: **`(μ_j)_j` is uniform on `K^κ`** given the
  transcript (hence also independent of it).  [Paper Lemmas `unif`, `S1shift`.]
* `unif_joint` : the same for `Λ` depending on `T = ev ∘ a` (the oracle's view).
-/
namespace ECDLP.L114

open Finset

section unif
variable {A G Loc S : Type*} [AddCommGroup A] [AddCommGroup G] [AddCommGroup Loc]
  [CommRing S] [Module S Loc] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `Φ(a)_j = ∑_i Λ_ji • ρ (a i)`. -/
def combHom (ρ : A →+ Loc) (Lam : Matrix κ ι S) : (ι → A) →+ (κ → Loc) where
  toFun a j := ∑ i, Lam j i • ρ (a i)
  map_zero' := by funext j; simp
  map_add' x y := by funext j; simp [smul_add, Finset.sum_add_distrib]

theorem combHom_apply (ρ : A →+ Loc) (Lam : Matrix κ ι S) (a : ι → A) (j : κ) :
    combHom ρ Lam a j = ∑ i, Lam j i • ρ (a i) := rfl

/-- from kernel-part surjectivity and a right inverse of `Λ`, `Φ` maps `(ker ev)^ι` onto `K^κ`. -/
theorem comb_surj [DecidableEq κ] (ev : A →+ G) (ρ : A →+ Loc) (K : AddSubgroup Loc)
    (hK2 : ∀ μ ∈ K, ∃ a ∈ ev.ker, ρ a = μ) (Lam : Matrix κ ι S) (W : Matrix ι κ S)
    (hLW : Lam * W = 1) (hlift : ∀ s : S, ∃ z : ℤ, (z : S) = s)
    (v : κ → Loc) (hv : ∀ j, v j ∈ K) :
    ∃ k : ι → A, (∀ i, ev (k i) = 0) ∧ combHom ρ Lam k = v := by
  choose b hb1 hb2 using fun j => hK2 (v j) (hv j)
  choose w hw using fun i j => hlift (W i j)
  refine ⟨fun i => ∑ j, w i j • b j, ?_, ?_⟩
  · intro i
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_zsmul, AddMonoidHom.mem_ker.1 (hb1 j), smul_zero]
  · funext j'
    rw [combHom_apply]
    have h1 : ∀ i, ρ (∑ j, w i j • b j) = ∑ j, W i j • v j := by
      intro i
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, hb2 j, ← hw i j, Int.cast_smul_eq_zsmul]
    simp only [h1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ j, ∑ i, Lam j' i * W i j = (Lam * W) j' j := fun j => by simp [Matrix.mul_apply]
    simp only [this, hLW, Matrix.one_apply]
    simp

open Classical in
/-- **S1 (conditional form)**: given the points `T i = ev (a i)`, the combination `Φ_Λ(a)` is uniform on
`K^κ`: all of its values in `K^κ` have the same number of tag-tuples. -/
theorem unif_fibres [Fintype A] [DecidableEq ι] (ev : A →+ G) (ρ : A →+ Loc) (K : AddSubgroup Loc)
    (hK2 : ∀ μ ∈ K, ∃ a ∈ ev.ker, ρ a = μ) (Lam : Matrix κ ι S) (W : Matrix ι κ S)
    (hLW : Lam * W = 1) (hlift : ∀ s : S, ∃ z : ℤ, (z : S) = s)
    (T : ι → G) (hT : ∀ i, T i ∈ Set.range ev)
    (hΦ : ∀ a : ι → A, (∀ i, ev (a i) = T i) → ∀ j, combHom ρ Lam a j ∈ K)
    (m m' : κ → Loc) (hm : ∀ j, m j ∈ K) (hm' : ∀ j, m' j ∈ K) :
    (univ.filter (fun a : ι → A => (∀ i, ev (a i) = T i) ∧ combHom ρ Lam a = m)).card =
    (univ.filter (fun a : ι → A => (∀ i, ev (a i) = T i) ∧ combHom ρ Lam a = m')).card := by
  let E : (ι → A) →+ (ι → G) := AddMonoidHom.compLeft ev ι
  let Ψ : (ι → A) →+ (ι → G) × (κ → Loc) := E.prod (combHom ρ Lam)
  have key : ∀ v : κ → Loc, (∀ j, v j ∈ K) →
      (univ.filter (fun a : ι → A => (∀ i, ev (a i) = T i) ∧ combHom ρ Lam a = v)).card =
      (univ.filter (fun a : ι → A => Ψ a = (T, v))).card := by
    intro v _
    refine congrArg Finset.card (Finset.filter_congr fun a _ => ?_)
    simp only [Ψ, E, AddMonoidHom.prod_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨funext h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i => congrFun h1 i, h2⟩
  have hrange : ∀ v : κ → Loc, (∀ j, v j ∈ K) → ((T, v) : (ι → G) × (κ → Loc)) ∈ Set.range Ψ := by
    intro v hv
    choose a0 ha0 using hT
    -- a0 i : A with ev (a0 i) = T i
    have h0 : ∀ j, combHom ρ Lam a0 j ∈ K := hΦ a0 ha0
    obtain ⟨k, hk1, hk2⟩ := comb_surj ev ρ K hK2 Lam W hLW hlift (fun j => v j - combHom ρ Lam a0 j)
      (fun j => K.sub_mem (hv j) (h0 j))
    refine ⟨a0 + k, ?_⟩
    simp only [Ψ, E, AddMonoidHom.prod_apply]
    refine Prod.ext ?_ ?_
    · funext i; simp [hk1 i, ha0 i]
    · simp only [map_add, hk2]; funext j; simp
  rw [key m hm, key m' hm']
  exact AddMonoidHom.card_fiber_eq_of_mem_range Ψ (hrange m hm) (hrange m' hm')

/-- restriction of a draw-indexed tag family to the selected rows -/
def restrictHom (pos : ι → κd) : (κd → A) →+ (ι → A) where
  toFun a i := a (pos i)
  map_zero' := rfl
  map_add' _ _ := rfl

open Classical in
/-- **S1 with row selection.**  Tags `a t` are indexed by *all draws* `t ∈ κd` (the point of draw `t` is
`T t = ev (a t)` after conditioning); the algorithm uses only the injectively selected draws `pos i`
(the accepted ones).  Then `Φ_Λ` of the selected tags is uniform on `K^κ` as soon as it lands in `K^κ`. -/
theorem unif_fibres_sel {κd : Type*} [Fintype κd] [Fintype A] [DecidableEq ι]
    (ev : A →+ G) (ρ : A →+ Loc) (K : AddSubgroup Loc)
    (hK2 : ∀ μ ∈ K, ∃ a ∈ ev.ker, ρ a = μ) (Lam : Matrix κ ι S) (W : Matrix ι κ S)
    [DecidableEq κ] (hLW : Lam * W = 1) (hlift : ∀ s : S, ∃ z : ℤ, (z : S) = s)
    (pos : ι → κd) (hpos : Function.Injective pos)
    (T : κd → G) (hT : ∀ t, T t ∈ Set.range ev)
    (hΦ : ∀ a : κd → A, (∀ t, ev (a t) = T t) → ∀ j, combHom ρ Lam (fun i => a (pos i)) j ∈ K)
    (m m' : κ → Loc) (hm : ∀ j, m j ∈ K) (hm' : ∀ j, m' j ∈ K) :
    (univ.filter (fun a : κd → A => (∀ t, ev (a t) = T t) ∧
        combHom ρ Lam (fun i => a (pos i)) = m)).card =
    (univ.filter (fun a : κd → A => (∀ t, ev (a t) = T t) ∧
        combHom ρ Lam (fun i => a (pos i)) = m')).card := by
  let E : (κd → A) →+ (κd → G) := AddMonoidHom.compLeft ev κd
  let Ψ : (κd → A) →+ (κd → G) × (κ → Loc) := E.prod ((combHom ρ Lam).comp (restrictHom pos))
  have key : ∀ v : κ → Loc,
      (univ.filter (fun a : κd → A => (∀ t, ev (a t) = T t) ∧
        combHom ρ Lam (fun i => a (pos i)) = v)).card =
      (univ.filter (fun a : κd → A => Ψ a = (T, v))).card := by
    intro v
    refine congrArg Finset.card (Finset.filter_congr fun a _ => ?_)
    simp only [Ψ, E, AddMonoidHom.prod_apply, Prod.mk.injEq, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨funext h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun t => congrFun h1 t, h2⟩
  have hrange : ∀ v : κ → Loc, (∀ j, v j ∈ K) →
      ((T, v) : (κd → G) × (κ → Loc)) ∈ Set.range Ψ := by
    intro v hv
    choose a0 ha0 using hT
    have h0 : ∀ j, combHom ρ Lam (fun i => a0 (pos i)) j ∈ K := hΦ a0 ha0
    obtain ⟨k, hk1, hk2⟩ := comb_surj ev ρ K hK2 Lam W hLW hlift
      (fun j => v j - combHom ρ Lam (fun i => a0 (pos i)) j) (fun j => K.sub_mem (hv j) (h0 j))
    let ek : κd → A := fun t => if h : ∃ i, pos i = t then k h.choose else 0
    have hek : ∀ i, ek (pos i) = k i := by
      intro i
      have h : ∃ i', pos i' = pos i := ⟨i, rfl⟩
      simp only [ek, h, dite_true]
      rw [hpos h.choose_spec]
    have hek0 : ∀ t, ev (ek t) = 0 := by
      intro t
      simp only [ek]
      split_ifs with h
      · exact hk1 _
      · exact map_zero _
    refine ⟨a0 + ek, ?_⟩
    simp only [Ψ, E, AddMonoidHom.prod_apply, AddMonoidHom.comp_apply]
    refine Prod.ext ?_ ?_
    · funext t; simp [hek0 t, ha0 t]
    · show combHom ρ Lam (restrictHom pos (a0 + ek)) = v
      have : restrictHom pos (a0 + ek) = restrictHom pos a0 + k := by
        funext i; simp [restrictHom, hek i]
      rw [this, map_add]
      have e2 : combHom ρ Lam k = fun j => v j - combHom ρ Lam (fun i => a0 (pos i)) j := hk2
      rw [e2]; funext j; simp [restrictHom]
  rw [key m, key m']
  exact AddMonoidHom.card_fiber_eq_of_mem_range Ψ (hrange m hm) (hrange m' hm')

end unif
end ECDLP.L114
