import Mathlib
import ECDLP.L54_Main
import ECDLP.L51_Main

/-!
# L54 / Search: the per-identity network drives L31's search to `lexLeast`

`net_eq_ncard'`: value of the per-identity network for the instance of L35's input and prefix `π` is
`(strings (n+1) (p,a,b,xR,yR,π)).ncard`.  `search_computes_lexLeast'`: L31's bitwise search driven by these
counts returns `ECDLP.lexLeast (n+1) (p,a,b,xR,yR,[])`.
-/
noncomputable section
namespace ECDLP.L54
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38 ECDLP.L51

variable {n K : ℕ}

/-- The per-identity network of an instance and prefix, as a `Net` value. -/
def packedValue' (I : ECDLP.L44.Inst) (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K) {g : ℕ}
    (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) : ℤ :=
  ((((compNet (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
        (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toForced.toGNet).toNet eg).value)

/-- parameter conditions of `main_count'` for the prefix `π` -/
def ParOK' (I : ECDLP.L44.Inst) (ℓ : ℕ) (π : List Bool) (e : Cn n ≃ Fin K) (N0 : NPar) (w : Fin K → ℕ) : Prop :=
  1 ≤ N0.b ∧ ℓ ≤ N0.b * 2 ^ N0.k ∧ (∀ c, I.cv c < 2 ^ (N0.b * 2 ^ N0.k)) ∧
    ∀ c, (NP N0 w c).SizeOK (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e c)

theorem par_exists' (I : ECDLP.L44.Inst) (ℓ : ℕ) (π : List Bool) (e : Cn n ≃ Fin K) :
    ∃ (N0 : NPar) (w : Fin K → ℕ), ParOK' I ℓ π e N0 w := by
  set Z : ℕ := ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 with hZdef
  have hZ : ∀ c, I.cv c < Z := by
    intro c
    have h1 : (I.cv c).toNat ≤ Finset.univ.sup fun c : Cst => (I.cv c).toNat :=
      Finset.le_sup (f := fun c : Cst => (I.cv c).toNat) (Finset.mem_univ c)
    have h2 := Int.self_le_toNat (I.cv c)
    have : (I.cv c) < ((ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 : ℕ) : ℤ) := by
      push_cast
      have h3 : ((I.cv c).toNat : ℤ) ≤ ((Finset.univ.sup fun c : Cst => (I.cv c).toNat : ℕ) : ℤ) := by
        exact_mod_cast h1
      have : (0 : ℤ) ≤ ℓ := by positivity
      linarith
    exact this
  set k : ℕ := 2 * Z + 1 with hk
  set T : ℕ := 12 * (2 ^ k * 4) with hT
  let N0 : NPar :=
    { k := k, A := 2 ^ (Z + 1), w := 0, b := 1, h := 2 ^ Z
      hA := by rw [← pow_add]; congr 1; omega
      hAh := by rw [← pow_add]; congr 1; omega }
  have hZk : Z < 2 ^ k := lt_of_le_of_lt (by omega : Z ≤ k) (Nat.lt_two_pow_self)
  have hk2 : 2 ^ k < 2 ^ (1 * 2 ^ k) := by
    rw [one_mul]; exact Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self
  have hbW : N0.b * 2 ^ N0.k = 1 * 2 ^ k := rfl
  refine ⟨N0, fun _ => T + 1, le_refl _, ?_, ?_, fun c => ?_⟩
  · rw [hbW]; omega
  · intro c
    rw [hbW]
    have := hZ c
    have h3 : (Z : ℤ) < 2 ^ (1 * 2 ^ k) := by exact_mod_cast lt_trans hZk hk2
    exact lt_trans (by exact_mod_cast this) h3
  · refine sizeOK_fr _ e N0 (fun _ => T + 1) c ?_ ?_ ?_
    · show 1 ≤ 2 ^ k * (T + 1)
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · show 2 * 2 ^ k ≤ 2 ^ (Z + 1) * 2 ^ (Z + 1)
      rw [← pow_add, show Z + 1 + (Z + 1) = k + 1 by omega, pow_succ]
      exact le_of_eq (by ring)
    · show 12 * (2 ^ k * (2 ^ 1 * 2 ^ 1)) ≤ 2 ^ (2 ^ k * (T + 1))
      have h1 : 12 * (2 ^ k * (2 ^ 1 * 2 ^ 1)) = T := by rw [hT]; ring
      rw [h1]
      calc T ≤ 2 ^ T := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (2 ^ k * (T + 1)) := Nat.pow_le_pow_right (by norm_num) (by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          nlinarith)

open Classical in
/-- **Per-identity network value = number of L35 strings with prefix `π`.** -/
theorem net_eq_ncard' (p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (π : List Bool) (hlen : π.length ≤ (n + 1) * (ell p n + 1)) (e : Cn n ≃ Fin K)
    (N0 : NPar) (w : Fin K → ℕ) (hok : ParOK' (instOf p a b xR yR n) (ell p n) π e N0 w) :
    packedValue' (instOf p a b xR yR n) N0 w π (ell p n) e (Fintype.equivFin _) =
      ((ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard : ℤ) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨hb1, hℓ, hcv, hS⟩ := hok
  haveI hpI : Fact (instOf p a b xR yR n).p.Prime := hp
  haveI hell : (shortW (instOf p a b xR yR n).p (instOf p a b xR yR n).a
      (instOf p a b xR yR n).b).IsElliptic := by
    show (shortW p (a : ℤ) (b : ℤ)).IsElliptic
    rw [shortW_eq]
    exact ⟨isUnit_iff_ne_zero.2 hΔ⟩
  have key := main_count' (instOf p a b xR yR n) N0 w π (ell p n) hℓ hlen e
    (by simp [instOf]) (by simpa [instOf] using ha) (by simp [instOf]) (by simpa [instOf] using hb)
    (by simpa [instOf] using Bd_le hp0 n)
    (fun x h0 h1 => Bd_xx hp0 hn x h0 (by simpa [instOf] using h1))
    (by simp [instOf]) (by simp [instOf]; omega)
    (by simp [instOf]; exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩)
    (by show (shortW p (a : ℤ) (b : ℤ)).Nonsingular (((xR : ℤ) : ZMod p)) (((yR : ℤ) : ZMod p))
        rw [shortW_eq]; simpa using hRns)
    hcv hS hb1 (Fintype.equivFin _)
  have e1 := ncard_strings_eq (p := p) n a b xR yR π hΔ hRns
  have h3 := genfilter_congr (shortW p (a : ℤ) (b : ℤ)) (Wc p a b) (shortW_eq p a b)
    (fun x : ZMod p => x.val < Bd p n) (((xR : ℤ) : ZMod p), ((yR : ℤ) : ZMod p))
    ((xR : ZMod p), (yR : ZMod p)) (by simp) n (fun P => π <+: strOf p (ell p n) P)
  have key' : packedValue' (instOf p a b xR yR n) N0 w π (ell p n) e (Fintype.equivFin _) =
      ((((GenSet (shortW p (a : ℤ) (b : ℤ)) (fun x : ZMod p => x.val < Bd p n)
        (((xR : ℤ) : ZMod p), ((yR : ℤ) : ZMod p)) n).filter
          (fun P => π <+: strOf p (ell p n) P)).card : ℕ) : ℤ) := key
  have h5 : ((GenSet (Wc p a b) (fun x : ZMod p => x.val < Bd p n) ((xR : ZMod p), (yR : ZMod p)) n).filter
          (fun P => π <+: strOf p (ell p n) P)).card =
      (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard := e1.symm
  rw [key']
  have h6 := h3.trans h5
  exact_mod_cast h6

/-- The count the per-identity network provides for the prefix `π` (parameters `par π`). -/
def netCount' (p a b xR yR : ℕ) (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (π : List Bool) : ℕ :=
  (packedValue' (instOf p a b xR yR n) (par π).1 (par π).2 π (ell p n) e (Fintype.equivFin _)).toNat

open Classical in
theorem net_count_eq_ncard' (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ)) (π : List Bool)
    (hlen : π.length ≤ (n + 1) * (ell p n + 1))
    (hpar : ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    netCount' p a b xR yR e par π = (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard := by
  unfold netCount'
  rw [net_eq_ncard' p hn a b xR yR ha hb hx hy hΔ hRns π hlen e _ _ hpar]
  simp

open Classical in
/-- **Main theorem.**  Driving L31's prefix search by the per-identity-network counts computes `lexLeast`. -/
theorem search_computes_lexLeast' (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (hpar : ∀ π : List Bool, π.length ≤ (n + 1) * (ell p n + 1) →
      ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
      if 0 < netCount' p a b xR yR e par [] then
        some (ECDLP.L31.search (netCount' p a b xR yR e par) ((n + 1) * (ell p n + 1)))
      else none := by
  set T := (n + 1) * (ell p n + 1) with hT
  set S0 := ECDLP.strings (n + 1) (p, a, b, xR, yR, []) with hS0
  have hfin : S0.Finite :=
    (List.finite_length_eq Bool T).subset (fun s hs => strings_len p n a b xR yR [] s hs)
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ s, s ∈ S ↔ s ∈ S0 := fun s => hfin.mem_toFinset
  have hSlen : ∀ s ∈ S, s.length = T := fun s hs => strings_len p n a b xR yR [] s ((hSmem s).1 hs)
  set c := netCount' p a b xR yR e par with hc
  have hcZ : ∀ π, π.length ≤ T → c π = ECDLP.L31.Z S π := by
    intro π hπ
    rw [hc, net_count_eq_ncard' p hn a b xR yR ha hb hx hy hΔ hRns e par π hπ (hpar π hπ),
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
theorem search_computes_lexLeast_exists' (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) :
    ∃ par : List Bool → NPar × (Fin K → ℕ),
      (∀ π : List Bool, ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) ∧
      ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
        if 0 < netCount' p a b xR yR e par [] then
          some (ECDLP.L31.search (netCount' p a b xR yR e par) ((n + 1) * (ell p n + 1)))
        else none := by
  choose N0 w hNw using fun π : List Bool => par_exists' (instOf p a b xR yR n) (ell p n) π e
  refine ⟨fun π => (N0 π, w π), fun π => hNw π, ?_⟩
  exact search_computes_lexLeast' p hn a b xR yR ha hb hx hy hΔ hRns e (fun π => (N0 π, w π))
    (fun π _ => hNw π)

end ECDLP.L54
end
