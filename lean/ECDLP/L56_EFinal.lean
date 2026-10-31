import ECDLP.L56_EdgeCount

/-!
# L56 / Final: the end results re-proved for the edge (child-specific message) network with tight pair widths
-/
noncomputable section
namespace ECDLP.L56
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38 ECDLP.L51 ECDLP.L35 ECDLP.L54

variable {n K : ℕ}

/-- edge network of an instance and prefix, tight pair widths, as a `Net` value -/
def edgeValue (I : ECDLP.L44.Inst) (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K) {g : ℕ}
    (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) : ℤ :=
  ((((edgeNet (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
        (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toGNet).toNet eg).value)

open Classical in
theorem edgeValue_eq (I : ECDLP.L44.Inst) (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K)
    (hpar : ParOK' I ℓ π e N0 w) {g g' : ℕ}
    (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g)
    (eg' : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g') :
    edgeValue I N0 w π ℓ e eg = packedValue' I N0 w π ℓ e eg' := by
  obtain ⟨hb1, -, -, hS⟩ := hpar
  unfold edgeValue packedValue'
  rw [edge_value (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e) _ hS hb1 eg,
    comp_value (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e) _ hS hb1 eg']

theorem net_eq_ncard_edge (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (π : List Bool) (hlen : π.length ≤ (n + 1) * (ell p n + 1)) (e : Cn n ≃ Fin K)
    (N0 : NPar) (w : Fin K → ℕ) (hok : ParOK' (instOf p a b xR yR n) (ell p n) π e N0 w) {g : ℕ}
    (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf (ell p n) π i) e) N0.A ≃ Fin g) :
    edgeValue (instOf p a b xR yR n) N0 w π (ell p n) e eg =
      ((ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard : ℤ) := by
  classical
  rw [edgeValue_eq _ N0 w π _ e hok eg (Fintype.equivFin _)]
  exact net_eq_ncard' p hn a b xR yR ha hb hx hy hΔ hRns π hlen e N0 w hok

/-- The count the edge network provides for the prefix `π` (parameters `par π`). -/
def netCountE (p a b xR yR : ℕ) (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (π : List Bool) : ℕ :=
  (edgeValue (instOf p a b xR yR n) (par π).1 (par π).2 π (ell p n) e (Fintype.equivFin _)).toNat

theorem net_count_eq_ncardE (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ)) (π : List Bool)
    (hlen : π.length ≤ (n + 1) * (ell p n + 1))
    (hpar : ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    netCountE p a b xR yR e par π = (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard := by
  unfold netCountE
  rw [net_eq_ncard_edge p hn a b xR yR ha hb hx hy hΔ hRns π hlen e _ _ hpar]
  simp

/-- **Main theorem for the edge network.**  L31's prefix search driven by the edge network's counts
(child-specific messages, tight widths) returns `lexLeast`. -/
theorem search_computes_lexLeast_edge (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (hpar : ∀ π : List Bool, π.length ≤ (n + 1) * (ell p n + 1) →
      ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
      if 0 < netCountE p a b xR yR e par [] then
        some (ECDLP.L31.search (netCountE p a b xR yR e par) ((n + 1) * (ell p n + 1)))
      else none := by
  set T := (n + 1) * (ell p n + 1) with hT
  set S0 := ECDLP.strings (n + 1) (p, a, b, xR, yR, []) with hS0
  have hfin : S0.Finite :=
    (List.finite_length_eq Bool T).subset (fun s hs => strings_len p n a b xR yR [] s hs)
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ s, s ∈ S ↔ s ∈ S0 := fun s => hfin.mem_toFinset
  have hSlen : ∀ s ∈ S, s.length = T := fun s hs => strings_len p n a b xR yR [] s ((hSmem s).1 hs)
  set c := netCountE p a b xR yR e par with hc
  have hcZ : ∀ π, π.length ≤ T → c π = ECDLP.L31.Z S π := by
    intro π hπ
    rw [hc, net_count_eq_ncardE p hn a b xR yR ha hb hx hy hΔ hRns e par π hπ (hpar π hπ),
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


/-- Non-vacuity: the parameter hypothesis can always be met. -/
theorem search_computes_lexLeast_exists_edge (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) :
    ∃ par : List Bool → NPar × (Fin K → ℕ),
      (∀ π : List Bool, ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) ∧
      ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
        if 0 < netCountE p a b xR yR e par [] then
          some (ECDLP.L31.search (netCountE p a b xR yR e par) ((n + 1) * (ell p n + 1)))
        else none := by
  choose N0 w hNw using fun π : List Bool => par_exists' (instOf p a b xR yR n) (ell p n) π e
  refine ⟨fun π => (N0 π, w π), fun π => hNw π, ?_⟩
  exact search_computes_lexLeast_edge p hn a b xR yR ha hb hx hy hΔ hRns e (fun π => (N0 π, w π))
    (fun π _ => hNw π)

open Classical in
/-- **Main theorem (edge network, plain widths).**  `Net.value` of the edge network with child-specific messages
equals the number of ordered generic factor-base decompositions with the prefix; same right-hand side as
`ECDLP.L54.main_count'`. -/
theorem main_count_edge (I : ECDLP.L44.Inst) [hpp : Fact I.p.Prime] [(shortW I.p I.a I.b).IsElliptic]
    (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (hℓ : ℓ ≤ N0.b * 2 ^ N0.k)
    (hlen : π.length ≤ (n + 1) * (ℓ + 1)) (e : Cn n ≃ Fin K)
    (ha0 : 0 ≤ I.a) (ha : I.a < I.p) (hb0 : 0 ≤ I.b) (hb : I.b < I.p) (hXp : I.X ≤ I.p)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hO : 2 * (I.p : ℤ) ≤ I.O) (hN : I.O + 2 * (I.p : ℤ) < I.N)
    (hR : 0 ≤ I.R.1 ∧ I.R.1 < I.p ∧ 0 ≤ I.R.2 ∧ I.R.2 < I.p)
    (hRns : (shortW I.p I.a I.b).Nonsingular (I.R.1 : ZMod I.p) (I.R.2 : ZMod I.p))
    (hcvB : ∀ c, I.cv c < 2 ^ (N0.b * 2 ^ N0.k))
    (hS : ∀ c, (NP N0 w c).SizeOK (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e c)) (hb1 : 1 ≤ N0.b)
    {g : ℕ} (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) :
    ((((edgeNet (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
        (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toGNet).toNet eg).value) =
      ((((GenSet (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X)
        ((I.R.1 : ZMod I.p), (I.R.2 : ZMod I.p)) n).filter
          (fun P => π <+: strOf I.p ℓ P)).card : ℕ) : ℤ) := by
  rw [edge_value (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e) _ hS hb1 eg]
  rw [← comp_value (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e) _ hS hb1 (Fintype.equivFin _)]
  exact main_count' I N0 w π ℓ hℓ hlen e ha0 ha hb0 hb hXp hXX hO hN hR hRns hcvB hS hb1 (Fintype.equivFin _)

end ECDLP.L56
end
