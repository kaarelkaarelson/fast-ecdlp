import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Lex
import Mathlib.Order.Basic

/-!
# L31 (a): prefix self-reduction (search from counts)

`S` is a finite set of bit strings of length `n`; `Z π` counts the `s ∈ S` with prefix `π`.
`go Z k π` extends `π` by `k` bits: by `false` when `Z (π ++ [false]) > 0`, else by `true`.
-/
namespace ECDLP.L31

/-- `Z S π` = number of elements of `S` having `π` as a prefix. -/
def Z (S : Finset (List Bool)) (π : List Bool) : ℕ := (S.filter (fun s => π <+: s)).card

/-- The bitwise procedure, parametrised by an arbitrary count oracle `c`. -/
def go (c : List Bool → ℕ) : ℕ → List Bool → List Bool
  | 0, π => π
  | k + 1, π => go c k (if 0 < c (π ++ [false]) then π ++ [false] else π ++ [true])

/-- The prefixes queried by `go` (one per step). -/
def queries (c : List Bool → ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, π => (π ++ [false]) ::
      queries c k (if 0 < c (π ++ [false]) then π ++ [false] else π ++ [true])

/-- The full search: test `Z [] > 0`, then `n` steps. -/
def search (c : List Bool → ℕ) (n : ℕ) : List Bool := go c n []

theorem queries_length (c) (k : ℕ) : ∀ π, (queries c k π).length = k := by
  induction k with
  | zero => intro π; rfl
  | succ k ih => intro π; simp [queries, ih]

theorem Z_pos_iff (S : Finset (List Bool)) (π) : 0 < Z S π ↔ ∃ s ∈ S, π <+: s := by
  simp [Z, Finset.card_pos, Finset.Nonempty]

theorem prefix_cases {π s : List Bool} (h : π <+: s) (hl : π.length < s.length) :
    π ++ [false] <+: s ∨ π ++ [true] <+: s := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hl
  | cons b t => cases b <;> simp

/-- Lexicographic `≤` on bit strings (`false < true`). -/
def LexLE (r t : List Bool) : Prop := r = t ∨ List.Lex (· < ·) r t

theorem lexlt (π u v : List Bool) : List.Lex (· < ·) (π ++ [false] ++ u) (π ++ [true] ++ v) := by
  simp only [List.append_assoc, List.singleton_append]
  induction π with
  | nil => exact List.Lex.rel (by decide)
  | cons a π ih => exact List.Lex.cons ih

/-- Main invariant: if every string of `S` has length `n`, `Z π > 0`, `|π| + k = n`, then
`go (Z S) k π` is an element of `S` extending `π`, and is `≤` every element of `S` extending `π`. -/
theorem go_spec (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n) :
    ∀ k π, π.length + k = n → 0 < Z S π →
      go (Z S) k π ∈ S ∧ π <+: go (Z S) k π ∧
        ∀ t ∈ S, π <+: t → LexLE (go (Z S) k π) t := by
  intro k
  induction k with
  | zero =>
    intro π hπ hZ
    obtain ⟨s, hs, hps⟩ := (Z_pos_iff S π).1 hZ
    have : π = s := hps.eq_of_length (by rw [hS s hs]; omega)
    subst this
    refine ⟨hs, List.prefix_refl _, ?_⟩
    intro t ht hpt
    have : π = t := hpt.eq_of_length (by rw [hS t ht]; omega)
    simp [go, this, LexLE]
  | succ k ih =>
    intro π hπ hZ
    obtain ⟨s, hs, hps⟩ := (Z_pos_iff S π).1 hZ
    have hsl := hS s hs
    have hlt : π.length < s.length := by omega
    by_cases h0 : 0 < Z S (π ++ [false])
    · have := ih (π ++ [false]) (by simp; omega) h0
      simp only [go, h0, ite_true]
      refine ⟨this.1, (List.prefix_append _ _).trans this.2.1, ?_⟩
      intro t ht hpt
      rcases prefix_cases hpt (by rw [hS t ht]; omega) with h | h
      · exact this.2.2 t ht h
      · -- result extends π++[false], t extends π++[true]
        have hr := this.2.1
        obtain ⟨u, hu⟩ := hr
        obtain ⟨v, hv⟩ := h
        rw [← hu, ← hv]
        exact Or.inr (lexlt π u v)
    · have hne : ∀ t ∈ S, π <+: t → ¬ (π ++ [false] <+: t) := by
        intro t ht hpt h; exact h0 ((Z_pos_iff S _).2 ⟨t, ht, h⟩)
      have h1 : 0 < Z S (π ++ [true]) := by
        rcases prefix_cases hps hlt with h | h
        · exact absurd h (hne s hs hps)
        · exact (Z_pos_iff S _).2 ⟨s, hs, h⟩
      have := ih (π ++ [true]) (by simp; omega) h1
      simp only [go, h0, ite_false]
      refine ⟨this.1, (List.prefix_append _ _).trans this.2.1, ?_⟩
      intro t ht hpt
      rcases prefix_cases hpt (by rw [hS t ht]; omega) with h | h
      · exact absurd h (hne t ht hpt)
      · exact this.2.2 t ht h

/-- **Prefix self-reduction.** If `Z [] > 0`, `search` returns an element of `S`, and the
lexicographically least one, after `n` steps making `n` oracle calls (plus the initial test). -/
theorem search_spec (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n)
    (h : 0 < Z S []) :
    search (Z S) n ∈ S ∧ (∀ t ∈ S, LexLE (search (Z S) n) t) ∧
      (queries (Z S) n []).length = n := by
  have := go_spec S n hS n [] (by simp) h
  exact ⟨this.1, fun t ht => this.2.2 t ht (List.nil_prefix), queries_length _ _ _⟩

theorem Z_leaf (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n) (π : List Bool)
    (hπ : π.length = n) : Z S π = if π ∈ S then 1 else 0 := by
  unfold Z
  have : S.filter (fun s => π <+: s) = if π ∈ S then {π} else ∅ := by
    ext s
    simp only [Finset.mem_filter]
    split_ifs with h
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨hs, hp⟩; exact (hp.eq_of_length (by rw [hS s hs]; omega)).symm
      · rintro rfl; exact ⟨h, List.prefix_refl _⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hs hp; exact h (by rw [hp.eq_of_length (by rw [hS s hs]; omega)]; exact hs)
  rw [this]; split_ifs <;> simp

theorem Z_add (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n) (π : List Bool)
    (hπ : π.length < n) : Z S π = Z S (π ++ [false]) + Z S (π ++ [true]) := by
  unfold Z
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hs, hp⟩
      rcases prefix_cases hp (by rw [hS s hs]; omega) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    · rintro (⟨hs, h⟩ | ⟨hs, h⟩)
      · exact ⟨hs, (List.prefix_append _ _).trans h⟩
      · exact ⟨hs, (List.prefix_append _ _).trans h⟩
  · rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_filter] at h1 h2
    obtain ⟨_, ⟨u, rfl⟩⟩ := h1
    obtain ⟨_, ⟨v, hv⟩⟩ := h2
    simp [List.append_assoc] at hv

/-- Any additive oracle with the right leaves equals `Z S` on strings of length `≤ n`. -/
theorem oracle_eq (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n)
    (c : List Bool → ℕ)
    (hadd : ∀ π, π.length < n → c π = c (π ++ [false]) + c (π ++ [true]))
    (hleaf : ∀ s, s.length = n → c s = if s ∈ S then 1 else 0) :
    ∀ d π, π.length + d = n → c π = Z S π := by
  intro d
  induction d with
  | zero => intro π h; rw [hleaf π (by omega), Z_leaf S n hS π (by omega)]
  | succ d ih =>
    intro π h
    rw [hadd π (by omega), Z_add S n hS π (by omega),
      ih (π ++ [false]) (by simp; omega), ih (π ++ [true]) (by simp; omega)]

theorem go_congr (c c' : List Bool → ℕ) (n : ℕ) (h : ∀ π, π.length ≤ n → c π = c' π) :
    ∀ k π, π.length + k ≤ n → go c k π = go c' k π := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro π hπ
    have : c (π ++ [false]) = c' (π ++ [false]) := h _ (by simp; omega)
    simp only [go, this]
    apply ih
    split_ifs <;> simp <;> omega

/-- **Prefix self-reduction (abstract oracle).** Let `c` be any function on bit strings with
`c π = c (π0) + c (π1)` for `|π| < n` and `c s = [s ∈ S]` for `|s| = n`, where `S` is a finite set of
strings of length `n`.  If `c [] > 0` the search returns an element of `S` (the lexicographically
least), making exactly `n` oracle calls after the initial test `c [] > 0`. -/
theorem search_abstract (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n)
    (c : List Bool → ℕ)
    (hadd : ∀ π, π.length < n → c π = c (π ++ [false]) + c (π ++ [true]))
    (hleaf : ∀ s, s.length = n → c s = if s ∈ S then 1 else 0) (h : 0 < c []) :
    search c n ∈ S ∧ (∀ t ∈ S, LexLE (search c n) t) ∧ (queries c n []).length = n := by
  have hc := oracle_eq S n hS c hadd hleaf n [] (by simp)
  have hg : search c n = search (Z S) n :=
    go_congr c (Z S) n (fun π hπ => by
      by_cases hl : π.length = n
      · rw [hleaf π hl, Z_leaf S n hS π hl]
      · exact oracle_eq S n hS c hadd hleaf (n - π.length) π (by omega)) n [] (by simp)
  rw [hg]
  have := search_spec S n hS (by rw [← hc]; exact h)
  exact ⟨this.1, this.2.1, queries_length _ _ _⟩

end ECDLP.L31

#print axioms ECDLP.L31.search_spec
#print axioms ECDLP.L31.search_abstract
