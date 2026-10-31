import ECDLP.L54_Search

/-!
# L54 / Tight: tight edge widths

L35's `Forced.toGNet` uses the (valid but very lazy) pair width `c i j = 2^(w i) + 2^(w j)`.  Here the width of
the pair `(i, j)` is `w(parent) + 1` for an edge (the parent's message plus one, since messages are shifted by 1)
and `0` for a non-adjacent pair.  The value of the network is unchanged
(`GNet.value_toNet` only needs `v < 2^c`, and `Good` does not mention `c`).
-/
noncomputable section
namespace ECDLP.L54
open Finset Factoring.Aux ECDLP.L35 ECDLP.L38

section
variable {R : Type*} [CommRing R] {ι : Type} (F : Forced R ι)

open Classical in
/-- the gate network with tight pair widths -/
def tightGNet [DecidableEq ι] : GNet R ι :=
  { F.toGNet with c := fun i j => if j ∈ F.pa i then F.w j + 1 else if i ∈ F.pa j then F.w i + 1 else 0 }

theorem v_lt_tight [DecidableEq ι] (i j : ι) (z : F.S i) :
    F.v i j z < 2 ^ (tightGNet F).c i j := by
  classical
  show F.v i j z < 2 ^ (if j ∈ F.pa i then F.w j + 1 else if i ∈ F.pa j then F.w i + 1 else 0)
  unfold Forced.v
  by_cases h1 : j ∈ F.pa i
  · simp only [dif_pos h1, if_pos h1]
    have : (z.2 ⟨j, h1⟩).val < 2 ^ F.w j := (z.2 ⟨j, h1⟩).isLt
    show (z.2 ⟨j, h1⟩).val + 1 < 2 ^ (F.w j + 1)
    rw [pow_succ]; omega
  · by_cases h2 : i ∈ F.pa j
    · simp only [dif_neg h1, if_neg h1, if_pos h2]
      have : (F.out i z).val < 2 ^ F.w i := (F.out i z).isLt
      show (F.out i z).val + 1 < 2 ^ (F.w i + 1)
      rw [pow_succ]; omega
    · simp [h1, h2]

open Classical in
theorem forced_value_tight [Fintype ι] [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g)
    (hW : ∀ i s, F.W i s = 0 ∨ F.W i s = 1) :
    (((tightGNet F).toNet e).value) = (((F.toGNet).toNet e).value) := by
  rw [GNet.value_toNet (tightGNet F) e hW (fun i j z => v_lt_tight F i j z),
    GNet.value_toNet F.toGNet e hW (fun i j z => F.v_lt i j z)]
  rfl

end

section
variable {R : Type*} [CommRing R] {ι : Type} (T : TForced R ι)

open Classical in
theorem tforced_value_tight [Fintype ι] [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g)
    (hW : ∀ i s, T.W i s = 0 ∨ T.W i s = 1) :
    (((tightGNet T.toForced).toNet e).value) = (((T.toForced.toGNet).toNet e).value) :=
  forced_value_tight T.toForced e (fun i s => by
    rcases hW i (s.1, fun j => T.dec j.1 (s.2 j)) with h | h
    · exact Or.inl h
    · exact Or.inr h)

end

section
open ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L51
variable {n K : ℕ}

/-- the per-identity network with tight pair widths, as a `Net` value -/
def packedValueT (I : ECDLP.L44.Inst) (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K) {g : ℕ}
    (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) : ℤ :=
  ((((tightGNet (compNet (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
        (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toForced)).toNet eg).value)

theorem packedValueT_eq (I : ECDLP.L44.Inst) (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (e : Cn n ≃ Fin K)
    {g : ℕ} (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) :
    packedValueT I N0 w π ℓ e eg = packedValue' I N0 w π ℓ e eg := by
  classical
  exact tforced_value_tight _ eg (fun g z => comp_01 _ _ _ g z)

def netCountT (p a b xR yR : ℕ) (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (π : List Bool) : ℕ :=
  (packedValueT (instOf p a b xR yR n) (par π).1 (par π).2 π (ell p n) e (Fintype.equivFin _)).toNat

theorem netCountT_eq (p a b xR yR : ℕ) (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ)) :
    netCountT p a b xR yR e par = netCount' p a b xR yR e par := by
  funext π
  unfold netCountT netCount'
  rw [packedValueT_eq]

/-- **Main theorem with tight pair widths.** -/
theorem search_computes_lexLeast_tight (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (e : Cn n ≃ Fin K) (par : List Bool → NPar × (Fin K → ℕ))
    (hpar : ∀ π : List Bool, π.length ≤ (n + 1) * (ell p n + 1) →
      ParOK' (instOf p a b xR yR n) (ell p n) π e (par π).1 (par π).2) :
    ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
      if 0 < netCountT p a b xR yR e par [] then
        some (ECDLP.L31.search (netCountT p a b xR yR e par) ((n + 1) * (ell p n + 1)))
      else none := by
  rw [netCountT_eq]
  exact search_computes_lexLeast' p hn a b xR yR ha hb hx hy hΔ hRns e par hpar

theorem net_eq_ncard_tight (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (π : List Bool) (hlen : π.length ≤ (n + 1) * (ell p n + 1)) (e : Cn n ≃ Fin K)
    (N0 : NPar) (w : Fin K → ℕ) (hok : ParOK' (instOf p a b xR yR n) (ell p n) π e N0 w) :
    packedValueT (instOf p a b xR yR n) N0 w π (ell p n) e (Fintype.equivFin _) =
      ((ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard : ℤ) := by
  rw [packedValueT_eq]
  exact net_eq_ncard' p hn a b xR yR ha hb hx hy hΔ hRns π hlen e N0 w hok

end

end ECDLP.L54
end
