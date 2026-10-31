import ECDLP.L61_Challenge
import ECDLP.L31_Search
import FactoringAux.Trial.Bits

/-!
# L61 / Facts: the strings of an instance, the count oracle, and the greedy walk with leaf detection

* `Zc m x τ` = number of L35 strings of the instance `x` with prefix `τ` (the instance's own prefix is replaced
  by `τ`); this is the quantity the zero-test oracle decides.
* `stepF Z` : one round of the search with leaf detection (no knowledge of the string length `n`):
  `(τ, false) ↦ (τ0, false)` if `Z(τ0) > 0`, else `(τ1, false)` if `Z(τ1) > 0`, else `(τ, true)` (done).
* `lexLeast_eq_iter` : for `R + |π| ≥ n + 1`, `lexLeast m x = if Z π > 0 then some (stepF^[R] (π,false)).1 else none`.
-/
namespace ECDLP.L61
open ECDLP Computability

/-- The prefix of an instance. -/
def pre (x : Inst) : List Bool := x.2.2.2.2.2

/-- The instance with its prefix replaced. -/
def withPre (x : Inst) (τ : List Bool) : Inst := (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, τ)

theorem withPre_pre (x : Inst) : withPre x (pre x) = x := rfl

/-- The common length of the strings of an instance. -/
noncomputable def nlen (m : ℕ) (x : Inst) : ℕ := m * (Nat.size (sInf {B | x.1 ≤ B ^ m}) + 1)

/-- The number of strings of the instance (prefix `τ`). -/
noncomputable def Zc (m : ℕ) (x : Inst) (τ : List Bool) : ℕ := (strings m (withPre x τ)).ncard

theorem strings_len' (m : ℕ) (x : Inst) {s : List Bool} (hs : s ∈ strings m x) : s.length = nlen m x := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  simp only [strings] at hs
  split_ifs at hs with hp
  · obtain ⟨_, P, hP, -⟩ := hs
    subst hP
    simp [nlen, List.length_flatten, List.sum_ofFn]
  · exact absurd hs (by simp)

theorem strings_len'' (m : ℕ) (x : Inst) (τ : List Bool) {s : List Bool} (hs : s ∈ strings m (withPre x τ)) :
    s.length = nlen m x := strings_len' m (withPre x τ) hs

theorem strings_pre (m : ℕ) (x : Inst) {s : List Bool} (hs : s ∈ strings m x) : pre x <+: s := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  simp only [strings] at hs
  split_ifs at hs with hp
  · obtain ⟨_, P, hP, hpre, -⟩ := hs
    subst hP
    exact hpre
  · exact absurd hs (by simp)

theorem strings_prefix' (m : ℕ) (x : Inst) (τ : List Bool) :
    strings m (withPre x τ) = {s | s ∈ strings m (withPre x []) ∧ τ <+: s} := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  change strings m (p, a, b, xR, yR, τ) = {s | s ∈ strings m (p, a, b, xR, yR, []) ∧ τ <+: s}
  ext s
  simp only [strings, Set.mem_ofPred_eq]
  split_ifs with hp
  · constructor
    · rintro ⟨hΔ, P, hs, hpre, rest⟩
      exact ⟨⟨hΔ, P, hs, List.nil_prefix, rest⟩, hpre⟩
    · rintro ⟨⟨hΔ, P, hs, -, rest⟩, hpre⟩
      exact ⟨hΔ, P, hs, hpre, rest⟩
  · simp

theorem sInf_le_prime (m p : ℕ) : sInf {B | p ≤ B ^ m} ≤ p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero]
    by_cases h : p ≤ 1
    · have : {B : ℕ | p ≤ 1} = Set.univ := by ext; simp [h]
      rw [this]; simp
    · have : {B : ℕ | p ≤ 1} = ∅ := by ext; simp [h]
      rw [this]; simp
  · exact Nat.sInf_le (by
      show p ≤ p ^ m
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · exact Nat.le_self_pow (by omega) p)

/-- If the instance has a string, its length is at most `m * (|encodeNat p| + 1)`. -/
theorem nlen_le (m : ℕ) (p a b x y : ℕ) (π : List Bool) :
    nlen m (p, a, b, x, y, π) ≤ m * ((encodeNat p).length + 1) := by
  unfold nlen
  refine Nat.mul_le_mul_left _ ?_
  have h1 : Nat.size (sInf {B | p ≤ B ^ m}) ≤ Nat.size p := Nat.size_le_size (sInf_le_prime m p)
  have h2 : Nat.size p ≤ (encodeNat p).length := by
    rw [Nat.size_le]
    exact Factoring.Aux.Trial.lt_two_pow_length p
  simp only
  omega


/-! ### The walk with leaf detection -/

/-- One round: extend by `0` if that keeps the count positive, else by `1` if that does, else stop. -/
def stepF (Z : List Bool → ℕ) : List Bool × Bool → List Bool × Bool
  | (τ, true) => (τ, true)
  | (τ, false) =>
      if 0 < Z (τ ++ [false]) then (τ ++ [false], false)
      else if 0 < Z (τ ++ [true]) then (τ ++ [true], false) else (τ, true)

theorem iter_done (Z : List Bool → ℕ) (τ : List Bool) : ∀ j, (stepF Z)^[j] (τ, true) = (τ, true)
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply]; exact iter_done Z τ j

open ECDLP.L31 in
theorem iter_go (S : Finset (List Bool)) (n : ℕ) (hS : ∀ s ∈ S, s.length = n) :
    ∀ k τ, τ.length + k = n → 0 < Z S τ → ∀ j, ((stepF (Z S))^[k + j] (τ, false)).1 = go (Z S) k τ := by
  intro k
  induction k with
  | zero =>
    intro τ hτ hZ j
    have h0 : ∀ b, Z S (τ ++ [b]) = 0 := by
      intro b
      by_contra hne
      obtain ⟨s, hs, hp⟩ := (Z_pos_iff S _).1 (Nat.pos_of_ne_zero hne)
      have := hp.length_le
      rw [hS s hs] at this
      simp at this; omega
    cases j with
    | zero => rfl
    | succ j =>
      have : stepF (Z S) (τ, false) = (τ, true) := by simp [stepF, h0]
      simp only [Nat.zero_add]
      rw [Function.iterate_succ_apply, this, iter_done]
      rfl
  | succ k ih =>
    intro τ hτ hZ j
    have hlt : τ.length < n := by omega
    have hadd := Z_add S n hS τ hlt
    rw [show k + 1 + j = (k + j) + 1 by omega, Function.iterate_succ_apply]
    by_cases h0 : 0 < Z S (τ ++ [false])
    · have : stepF (Z S) (τ, false) = (τ ++ [false], false) := by simp [stepF, h0]
      rw [this, ih _ (by simp; omega) h0 j]
      simp [go, h0]
    · have h1 : 0 < Z S (τ ++ [true]) := by omega
      have : stepF (Z S) (τ, false) = (τ ++ [true], false) := by simp [stepF, h0, h1]
      rw [this, ih _ (by simp; omega) h1 j]
      simp [go, h0]

theorem lexLE_le' {r t : List Bool} (h : ECDLP.L31.LexLE r t) : r ≤ t := by
  rcases h with rfl | h
  · exact le_rfl
  · exact le_of_lt ((List.lt_iff_lex_lt _ _).2 h)

open Classical in
/-- **The search with leaf detection computes `lexLeast`.**  With `R + |π| ≥ n + 1` rounds. -/
theorem lexLeast_eq_iter (m : ℕ) (x : Inst) (R : ℕ) (hR : 0 < Zc m x (pre x) → nlen m x + 1 ≤ R + (pre x).length) :
    lexLeast m x =
      if 0 < Zc m x (pre x) then some (((stepF (Zc m x))^[R] (pre x, false)).1) else none := by
  set S0 := strings m (withPre x []) with hS0
  set n := nlen m x with hn
  have hfin : S0.Finite :=
    (List.finite_length_eq Bool n).subset (fun s hs => strings_len'' m x [] hs)
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ s, s ∈ S ↔ s ∈ S0 := fun s => hfin.mem_toFinset
  have hSlen : ∀ s ∈ S, s.length = n := fun s hs => strings_len'' m x [] ((hSmem s).1 hs)
  have hZ : ∀ τ, Zc m x τ = ECDLP.L31.Z S τ := by
    intro τ
    unfold Zc
    rw [strings_prefix', ECDLP.L31.Z]
    have : {s | s ∈ S0 ∧ τ <+: s} = ((S.filter (fun s => τ <+: s) : Finset _) : Set (List Bool)) := by
      ext s; simp [hSmem]
    rw [this, Set.ncard_coe_finset]
  have hZfun : Zc m x = ECDLP.L31.Z S := funext hZ
  have hstr : ∀ s, s ∈ strings m x ↔ (s ∈ S0 ∧ pre x <+: s) := by
    intro s
    have := strings_prefix' m x (pre x)
    rw [withPre_pre] at this
    rw [this]; rfl
  rw [hZfun] at hR ⊢
  by_cases h0 : 0 < ECDLP.L31.Z S (pre x)
  · rw [if_pos h0]
    obtain ⟨s, hs, hps⟩ := (ECDLP.L31.Z_pos_iff S _).1 h0
    have hR := hR h0
    have hlen : (pre x).length ≤ n := by
      have := hps.length_le; rw [hSlen s hs] at this; exact this
    have hit := iter_go S n hSlen (n - (pre x).length) (pre x) (by omega) h0 (R - (n - (pre x).length))
    rw [show n - (pre x).length + (R - (n - (pre x).length)) = R by omega] at hit
    rw [hit]
    obtain ⟨hmem, hpre, hmin⟩ := ECDLP.L31.go_spec S n hSlen (n - (pre x).length) (pre x) (by omega) h0
    have hex : ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t := by
      refine ⟨ECDLP.L31.go (ECDLP.L31.Z S) (n - (pre x).length) (pre x), ?_, fun t ht => ?_⟩
      · exact (hstr _).2 ⟨(hSmem _).1 hmem, hpre⟩
      · have ht' := (hstr t).1 ht
        exact lexLE_le' (hmin t ((hSmem t).2 ht'.1) ht'.2)
    unfold lexLeast
    rw [dif_pos hex]
    congr 1
    obtain ⟨hch, hchmin⟩ := hex.choose_spec
    have hg : ECDLP.L31.go (ECDLP.L31.Z S) (n - (pre x).length) (pre x) ∈ strings m x :=
      (hstr _).2 ⟨(hSmem _).1 hmem, hpre⟩
    refine le_antisymm (hchmin _ hg) ?_
    have hch' := (hstr _).1 hch
    exact lexLE_le' (hmin _ ((hSmem _).2 hch'.1) hch'.2)
  · rw [if_neg h0]
    have hnone : ¬ ∃ s ∈ strings m x, ∀ t ∈ strings m x, s ≤ t := by
      rintro ⟨s, hs, -⟩
      have hs' := (hstr s).1 hs
      have := (ECDLP.L31.Z_pos_iff S (pre x)).2 ⟨s, (hSmem s).2 hs'.1, hs'.2⟩
      omega
    unfold lexLeast
    rw [dif_neg hnone]

end ECDLP.L61

#print axioms ECDLP.L61.lexLeast_eq_iter
