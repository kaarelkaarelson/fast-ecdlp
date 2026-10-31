import Mathlib

/-!
# L40 (3a): counting "trivial" value tuples
A list is *trivial* if every value occurs an even number of times.  The number of trivial
lists of length `2n` with entries in `T` is at most `(2n-1)!! * |T|^n`.
-/
namespace ECDLP.L40

open Finset

variable {K : Type*} [DecidableEq K]

/-- every value occurs an even number of times -/
def TrivL (l : List K) : Prop := ∀ v, Even (l.count v)

/-- `∏_{i<n} (2i+1) = (2n-1)!!` -/
def dfac (n : ℕ) : ℕ := ∏ i ∈ range n, (2 * i + 1)

theorem dfac_eq (n : ℕ) : dfac n = (2 * n - 1).doubleFactorial := by
  induction n with
  | zero => simp [dfac]
  | succ n ih =>
    unfold dfac at *
    rw [prod_range_succ, ih]
    rcases n with _ | n
    · simp
    · have h1 : 2 * (n + 1 + 1) - 1 = (2 * (n + 1) - 1) + 2 := by omega
      have h2 : 2 * (n + 1) - 1 + 2 = 2 * (n + 1) + 1 := by omega
      rw [h1, Nat.doubleFactorial_add_two, h2]; ring

/-- explicit finite family containing all trivial lists of length `2n` over `T` -/
def Ltriv (T : Finset K) : ℕ → Finset (List K)
  | 0 => {[]}
  | n + 1 => ((T ×ˢ range (2 * n + 1)) ×ˢ Ltriv T n).image
      (fun x => x.1.1 :: x.2.insertIdx x.1.2 x.1.1)

theorem card_Ltriv (T : Finset K) (n : ℕ) : (Ltriv T n).card ≤ dfac n * T.card ^ n := by
  induction n with
  | zero => simp [Ltriv, dfac]
  | succ n ih =>
    simp only [Ltriv]
    refine (card_image_le).trans ?_
    rw [card_product, card_product, card_range]
    calc T.card * (2 * n + 1) * (Ltriv T n).card
        ≤ T.card * (2 * n + 1) * (dfac n * T.card ^ n) := Nat.mul_le_mul_left _ ih
      _ = dfac (n + 1) * T.card ^ (n + 1) := by
        unfold dfac; rw [prod_range_succ]; ring

theorem mem_Ltriv (T : Finset K) (n : ℕ) :
    ∀ l : List K, (∀ x ∈ l, x ∈ T) → l.length = 2 * n → TrivL l → l ∈ Ltriv T n := by
  induction n with
  | zero => intro l _ hl _; simp [Ltriv, List.length_eq_zero_iff.1 (by simpa using hl)]
  | succ n ih =>
    intro l hT hl htr
    match l, hT, hl, htr with
    | [], _, hl, _ => simp at hl
    | a :: l', hT, hl, htr =>
      have hl' : l'.length = 2 * n + 1 := by simp at hl; omega
      have hca := htr a
      have hmem : a ∈ l' := by
        by_contra hna
        have : l'.count a = 0 := List.count_eq_zero.2 hna
        simp [List.count_cons, this] at hca
      set j := l'.idxOf a with hj
      have hjlt : j < l'.length := List.idxOf_lt_length_iff.2 hmem
      have hja : l'[j] = a := List.getElem_idxOf hjlt
      set r := l'.eraseIdx j with hr
      have hperm : List.Perm (a :: r) l' := by
        have := List.getElem_cons_eraseIdx_perm hjlt
        rwa [hja] at this
      have hrl : r.length = 2 * n := by
        have := hperm.length_eq; simp at this; omega
      have hins : r.insertIdx j a = l' := by
        have := List.insertIdx_eraseIdx_getElem hjlt
        rwa [hja] at this
      have hrT : ∀ x ∈ r, x ∈ T := fun x hx =>
        hT x (List.mem_cons_of_mem _ (hperm.subset (List.mem_cons_of_mem _ hx)))
      have hrtr : TrivL r := by
        intro v
        have h1 := htr v
        have h2 : (a :: l').count v = (a :: a :: r).count v :=
          ((hperm.symm.cons a)).count_eq v
        rw [h2] at h1
        by_cases hv : v = a
        · subst hv; simp at h1
          obtain ⟨k, hk⟩ := h1; exact ⟨k - 1, by omega⟩
        · have hv' : ¬ a = v := fun h => hv h.symm
          simpa [hv'] using h1
      simp only [Ltriv, mem_image, mem_product, mem_range]
      exact ⟨((a, j), r), ⟨⟨hT a (by simp), by simp only [List.length_eq_zero_iff] at *; omega⟩, ih r hrT hrl hrtr⟩, by simp [hins]⟩

open scoped Classical in
/-- number of trivial value tuples `t : Fin (2n) → K` with entries in `T` -/
theorem card_trivial_tuples (T : Finset K) (n : ℕ) :
    ((Fintype.piFinset (fun _ : Fin (2 * n) => T)).filter (fun t => TrivL (List.ofFn t))).card
      ≤ dfac n * T.card ^ n := by
  refine le_trans ?_ (card_Ltriv T n)
  rw [← card_image_of_injective _ (List.ofFn_injective (n := 2 * n) (α := K))]
  refine card_le_card ?_
  intro l hl
  simp only [mem_image, mem_filter, Fintype.mem_piFinset] at hl
  obtain ⟨t, ⟨ht, htr⟩, rfl⟩ := hl
  refine mem_Ltriv T n _ ?_ (by simp) htr
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact ht i

end ECDLP.L40
