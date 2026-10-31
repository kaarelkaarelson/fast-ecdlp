import ECDLP.L65_Bridge
import ECDLP.L56_EFinal
import ECDLP.L70_Red
import ECDLP.L64_Edge

/-!
# L93 / Count: the count of the real edge network is `Zc`

`edgeCount_real_eq_Zc`: for `Good (r+1) x τ` (and `1 ≤ r`) the number `edgeCount φ F ok` of the REAL edge network of the reduced
instance `redInp x τ` (explicit parameters `NParE (size p)`, `wP (size p)`, `frF`, `okC`, any numbering `e`) is `Zc (r+1) x τ`.
Chain: `edge_value` (L56) + `net_eq_ncard_edge` (L56) + invariance of `strings` under `a ↦ a % p` etc.
-/
noncomputable section
namespace ECDLP.L93
open Finset ECDLP.L30 ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L59 ECDLP.L51
  ECDLP.L58 ECDLP.L61 ECDLP.L65 ECDLP.L70 ECDLP Factoring.Aux

/-- the body of `strings` as a function of the residues -/
def G (m p : ℕ) (hp : p.Prime) (a b xR yR : ZMod p) (π : List Bool) : Set (List Bool) :=
  haveI := Fact.mk hp
  let W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, a, b⟩
  let B := sInf {B | p ≤ B ^ m}
  let xy : W.toAffine.Point → ZMod p × ZMod p := fun P => match P with | .zero => (0, 0) | .some x y _ => (x, y)
  let str (P : Fin m → W.toAffine.Point) : List Bool := (List.ofFn fun i =>
    (List.range (Nat.size B)).reverse.map (fun j => (xy (P i)).1.val.testBit j) ++
      [decide ((p - 1) / 2 < (xy (P i)).2.val)]).flatten
  {s | W.Δ ≠ 0 ∧ ∃ P : Fin m → W.toAffine.Point, str P = s ∧ π <+: s ∧
    (∀ i, P i ≠ 0 ∧ (xy (P i)).1.val < B) ∧
    (∀ k : Fin m, 0 < k.val → let S := ((List.ofFn P).take k).sum
      S ≠ 0 ∧ (xy S).1 ≠ (xy (P k)).1) ∧
    (List.ofFn P).sum ≠ 0 ∧ xy (List.ofFn P).sum = (xR, yR)}

theorem strings_eq_G (m p a b xR yR : ℕ) (π : List Bool) (hp : p.Prime) :
    strings m (p, a, b, xR, yR, π) = G m p hp (a : ZMod p) (b : ZMod p) (xR : ZMod p) (yR : ZMod p) π := by
  simp only [strings, dif_pos hp]
  rfl

theorem strings_red (m p a b xR yR : ℕ) (τ : List Bool) :
    strings m (p, a, b, xR, yR, τ) = strings m (p, a % p, b % p, xR % p, yR % p, τ) := by
  by_cases hp : p.Prime
  · rw [strings_eq_G m p _ _ _ _ _ hp, strings_eq_G m p _ _ _ _ _ hp]
    simp only [ZMod.natCast_mod]
  · simp only [strings, dif_neg hp]

open Classical in
/-- **The count of the real edge network is `Zc`.**  The real edge network of the reduced instance
`(p, a % p, b % p, xR % p, yR % p, τ)`: explicit parameters `NParE (size p)`, `wP (size p)`, forms `frF`, constraints `okC`,
any numbering `e` of the identities. -/
theorem edgeCount_real_eq_Zc (r : ℕ) (hr : 1 ≤ r) (p a b xR yR : ℕ) (π τ : List Bool)
    (hG : Good (r + 1) (p, a, b, xR, yR, π) τ) {K : ℕ} (e : Cn r ≃ Fin K) :
    edgeCount (fun c => Subtype.val)
      (frF (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e)
      (okC (NParE (Nat.size p)) (Cl (instOf p (a % p) (b % p) (xR % p) (yR % p) r)
        ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
        (fun i : Fin (r + 1) => sgOf (ell p r) τ i) (fun i : Fin (r + 1) => xcOf (ell p r) τ i))) =
      Zc (r + 1) (p, a, b, xR, yR, π) τ := by
  obtain ⟨hp, ha, hb, hx, hy, hΔ, hns, hl⟩ := adm_red r (p, a, b, xR, yR, π) τ hG
  simp only [redInp] at hp ha hb hx hy hΔ hns hl
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hpar := parOK_explicit (K := K) p (a % p) (b % p) (xR % p) (yR % p) r hp0 ha hb hx hy τ e
  obtain ⟨hb1, -, -, hS⟩ := hpar
  have hpar' := parOK_explicit (K := K) p (a % p) (b % p) (xR % p) (yR % p) r hp0 ha hb hx hy τ e
  have h1 := edge_value (w := fun _ : Fin K => wP (Nat.size p)) (N0 := NParE (Nat.size p)) (fun c => Subtype.val)
    (frF (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e)
    (okC (NParE (Nat.size p)) (Cl (instOf p (a % p) (b % p) (xR % p) (yR % p) r)
        ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
        (fun i : Fin (r + 1) => sgOf (ell p r) τ i) (fun i : Fin (r + 1) => xcOf (ell p r) τ i)))
    hS hb1 (Fintype.equivFin _)
  have h2 := net_eq_ncard_edge (n := r) (K := K) p hr (a % p) (b % p) (xR % p) (yR % p) ha hb hx hy hΔ hns τ hl e
    (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) hpar' (Fintype.equivFin _)
  have h3 : (edgeValue (instOf p (a % p) (b % p) (xR % p) (yR % p) r) (NParE (Nat.size p))
      (fun _ : Fin K => wP (Nat.size p)) τ (ell p r) e (Fintype.equivFin _)) =
      ((edgeCount (fun c => Subtype.val)
      (frF (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e)
      (okC (NParE (Nat.size p)) (Cl (instOf p (a % p) (b % p) (xR % p) (yR % p) r)
        ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
        (fun i : Fin (r + 1) => sgOf (ell p r) τ i) (fun i : Fin (r + 1) => xcOf (ell p r) τ i))) : ℕ) : ℤ) := h1
  rw [h3] at h2
  have h4 : edgeCount (fun c => Subtype.val)
      (frF (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e)
      (okC (NParE (Nat.size p)) (Cl (instOf p (a % p) (b % p) (xR % p) (yR % p) r)
        ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
        (fun i : Fin (r + 1) => sgOf (ell p r) τ i) (fun i : Fin (r + 1) => xcOf (ell p r) τ i))) =
      (strings (r + 1) (p, a % p, b % p, xR % p, yR % p, τ)).ncard := by exact_mod_cast h2
  rw [h4]
  unfold Zc withPre
  exact congrArg Set.ncard (strings_red (r + 1) p a b xR yR τ).symm

end ECDLP.L93
end
