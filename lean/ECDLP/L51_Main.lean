import Mathlib
import ECDLP.L51_Net
import ECDLP.L31_Search
import ECDLP.L35_Challenge

/-!
# L51 / Main: search over L44-network counts computes `lexLeast`

`net_count_eq_Z`   : for every prefix `π` of length `≤ T = (n+1)(ℓ+1)`, the L44 network value equals
                     `L31.Z S π`, `S` = finite set of L35 strings.
`search_computes_lexLeast` : L31's bitwise search driven by the network counts returns exactly
                     `ECDLP.lexLeast (n+1) (p,a,b,xR,yR,[])` (as an `Option`).
-/
noncomputable section
namespace ECDLP.L51
open Finset ECDLP.L44 ECDLP.L34 ECDLP.L38

/-- Every string of the set has length `T = (n+1)(ℓ+1)`. -/
theorem strings_len (p n a b xR yR : ℕ) (π : List Bool) (s : List Bool)
    (hs : s ∈ ECDLP.strings (n + 1) (p, a, b, xR, yR, π)) : s.length = (n + 1) * (ell p n + 1) := by
  simp only [ECDLP.strings] at hs
  split_ifs at hs with hp
  · obtain ⟨_, P, hP, -⟩ := hs
    subst hP
    simp [List.length_flatten, List.sum_ofFn, ell, Bd]
    ring
  · exact absurd hs (by simp)

theorem strings_prefix (p n a b xR yR : ℕ) (π : List Bool) :
    ECDLP.strings (n + 1) (p, a, b, xR, yR, π) =
      {s | s ∈ ECDLP.strings (n + 1) (p, a, b, xR, yR, []) ∧ π <+: s} := by
  ext s
  simp only [ECDLP.strings, Set.mem_setOf_eq]
  split_ifs with hp
  · constructor
    · rintro ⟨hΔ, P, hs, hpre, rest⟩
      exact ⟨⟨hΔ, P, hs, List.nil_prefix, rest⟩, hpre⟩
    · rintro ⟨⟨hΔ, P, hs, -, rest⟩, hpre⟩
      exact ⟨hΔ, P, hs, hpre, rest⟩
  · simp

/-- The count the network provides for the prefix `π` (parameters `par π`). -/
def netCount {n K : ℕ} (p a b xR yR : ℕ) (e : Cn n ≃ Fin K) (par : List Bool → NPar × ℤ)
    (π : List Bool) : ℕ :=
  (packedValue (instOf p a b xR yR n) (par π).1 (par π).2 π (ell p n) e (Fintype.equivFin _)).toNat

theorem lexLE_le {r t : List Bool} (h : ECDLP.L31.LexLE r t) : r ≤ t := by
  rcases h with rfl | h
  · exact le_rfl
  · exact le_of_lt ((List.lt_iff_lex_lt _ _).2 h)

open Classical in
/-- **(2)** The network value of every prefix of length `≤ T` is the number of L35 strings with that prefix. -/
theorem net_count_eq_ncard {n K : ℕ} (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × ℤ) (π : List Bool)
    (hlen : π.length ≤ (n + 1) * (ell p n + 1))
    (hpar : ParOK (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    netCount p a b xR yR e par π = (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard := by
  unfold netCount
  rw [net_eq_ncard p hn a b xR yR ha hb hx hy hΔ hRns π hlen e _ _ hpar]
  simp

open Classical in
/-- **Main theorem.**  Driving L31's prefix search by the L44-network counts computes `lexLeast`. -/
theorem search_computes_lexLeast {n K : ℕ} (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × ℤ)
    (hpar : ∀ π : List Bool, π.length ≤ (n + 1) * (ell p n + 1) →
      ParOK (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
      if 0 < netCount p a b xR yR e par [] then
        some (ECDLP.L31.search (netCount p a b xR yR e par) ((n + 1) * (ell p n + 1)))
      else none := by
  set T := (n + 1) * (ell p n + 1) with hT
  set S0 := ECDLP.strings (n + 1) (p, a, b, xR, yR, []) with hS0
  have hfin : S0.Finite :=
    (List.finite_length_eq Bool T).subset (fun s hs => strings_len p n a b xR yR [] s hs)
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ s, s ∈ S ↔ s ∈ S0 := fun s => hfin.mem_toFinset
  have hSlen : ∀ s ∈ S, s.length = T := fun s hs => strings_len p n a b xR yR [] s ((hSmem s).1 hs)
  set c := netCount p a b xR yR e par with hc
  have hcZ : ∀ π, π.length ≤ T → c π = ECDLP.L31.Z S π := by
    intro π hπ
    rw [hc, net_count_eq_ncard p hn a b xR yR ha hb hx hy hΔ hRns e par π hπ (hpar π hπ),
      strings_prefix, ECDLP.L31.Z]
    have : {s | s ∈ S0 ∧ π <+: s} = ((S.filter (fun s => π <+: s) : Finset _) : Set (List Bool)) := by
      ext s
      simp [hSmem]
    rw [this, Set.ncard_coe_finset]
  have hadd : ∀ π : List Bool, π.length < T → c π = c (π ++ [false]) + c (π ++ [true]) := by
    intro π hπ
    rw [hcZ π hπ.le, hcZ (π ++ [false]) (by simp; omega), hcZ (π ++ [true]) (by simp; omega)]
    exact ECDLP.L31.Z_add S T hSlen π hπ
  have hleaf : ∀ s : List Bool, s.length = T → c s = if s ∈ S then 1 else 0 := by
    intro s hs
    rw [hcZ s hs.le]
    exact ECDLP.L31.Z_leaf S T hSlen s hs
  by_cases h0 : 0 < c []
  · rw [if_pos h0]
    obtain ⟨hmem, hmin, -⟩ := ECDLP.L31.search_abstract S T hSlen c hadd hleaf h0
    have hex : ∃ s ∈ S0, ∀ t ∈ S0, s ≤ t :=
      ⟨_, (hSmem _).1 hmem, fun t ht => lexLE_le (hmin t ((hSmem t).2 ht))⟩
    unfold ECDLP.lexLeast
    rw [dif_pos hex]
    congr 1
    obtain ⟨hch, hchmin⟩ := hex.choose_spec
    exact le_antisymm (hchmin _ ((hSmem _).1 hmem)) (lexLE_le (hmin _ ((hSmem _).2 hch)))
  · rw [if_neg h0]
    have hz : ECDLP.L31.Z S [] = 0 := by
      rw [← hcZ [] (by simp)]; omega
    have hnone : ¬ ∃ s ∈ S0, ∀ t ∈ S0, s ≤ t := by
      rintro ⟨s, hs, -⟩
      have := (ECDLP.L31.Z_pos_iff S []).2 ⟨s, (hSmem s).2 hs, List.nil_prefix⟩
      omega
    unfold ECDLP.lexLeast
    rw [dif_neg hnone]

/-- **(3) Sign bit.** For a prefix that stops before the sign position of point `i`, L44's network
imposes no sign requirement on it (so the count covers both signs, i.e. all decompositions whose
x-digits match; `strOf` being injective, this is the number of strings). -/
theorem sgOf_none (ℓ : ℕ) (π : List Bool) (i : ℕ) (h : π.length ≤ i * (ℓ + 1) + ℓ) :
    sgOf ℓ π i = .none := by
  unfold sgOf
  rw [List.getElem?_eq_none (by omega)]

/-- Non-vacuity: parameters satisfying `ParOK` exist for every prefix, so the hypothesis `hpar` of the
main theorem can always be met. -/
theorem search_computes_lexLeast_exists {n K : ℕ} (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) :
    ∃ par : List Bool → NPar × ℤ,
      (∀ π : List Bool, ParOK (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) ∧
      ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
        if 0 < netCount p a b xR yR e par [] then
          some (ECDLP.L31.search (netCount p a b xR yR e par) ((n + 1) * (ell p n + 1)))
        else none := by
  choose N B hNB using fun π : List Bool => par_exists (instOf p a b xR yR n) (ell p n) π e
  refine ⟨fun π => (N π, B π), fun π => hNB π, ?_⟩
  exact search_computes_lexLeast p hn a b xR yR ha hb hx hy hΔ hRns e (fun π => (N π, B π))
    (fun π _ => hNB π)

end ECDLP.L51

#print axioms ECDLP.L51.net_eq_ncard
#print axioms ECDLP.L51.search_computes_lexLeast_exists
#print axioms ECDLP.L51.sgOf_none
#print axioms ECDLP.L51.net_count_eq_ncard
#print axioms ECDLP.L51.search_computes_lexLeast
