import ECDLP.L63_Mem
import ECDLP.L63_Cost
import ECDLP.L63_Size

/-!
# L63 / Main: instance data as public inputs; the local checks of the network are computed from the bits
-/
noncomputable section
namespace ECDLP.L63
open Finset Factoring.Aux Factoring.Aux.Ex ECDLP.L44 ECDLP.L51 ECDLP.L59 Slot

/-- width of a pinned constant for the explicit parameters is `≤ 36 L` -/
theorem bW_le (L : ℕ) (hL : 4 ≤ L) : (NParE L).b * 2 ^ (NParE L).k ≤ 36 * L := by
  simp only [NParE_b, NParE_k]
  have h1 := bP_le L
  have h2 := D_sq_le L hL
  show bP L * DP L ≤ 36 * L
  calc bP L * DP L ≤ (36 * DP L) * DP L := Nat.mul_le_mul_right _ h1
    _ = 36 * (DP L * DP L) := by ring
    _ ≤ 36 * L := Nat.mul_le_mul_left _ h2

/-- **Local checks from public bits.**  For the concrete input layout (`memIn`, `stIn`) of `(p,a,b,X=Bd p n,xR,yR)`
and the prefix `π`, with `p` odd, `a,b,xR,yR < p`: the layout satisfies `Reads`, and
the constraints used by the network's local checks `okC N0 (Cl I bW sg xc)` and the identity forms are those
computed by the expressions `cvBitE`, `sgE`, `xcDefE`, `xcBitE`. -/
theorem local_checks_from_bits (p a b xR yR n : ℕ) (ℓ bW : ℕ) (π : List Bool)
    (hp : 0 < p) (hodd : p % 2 = 1) (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p) :
    let σ := stIn (Nat.size p) ℓ bW π
    let A := memIn p a b (Bd p n) xR yR π
    Reads σ A p a b (Bd p n) xR yR π ℓ bW ∧
    (∀ (c : Cst) (j : Ex) (β : Bool),
      (eval σ A j, β) ∈ Cl (instOf p a b xR yR n) bW (fun i : Fin (m + 1) => sgOf ℓ π i)
          (fun i : Fin (m + 1) => xcOf ℓ π i) (.cst c) ↔
        eval σ A j < bW ∧ eval σ A (cvBitE c j) = β.toNat) ∧
    (∀ (i : Fin (m + 1)) (j : Ex) (β : Bool),
      (eval σ A j, β) ∈ Cl (instOf p a b xR yR n) bW (fun i : Fin (m + 1) => sgOf ℓ π i)
          (fun i : Fin (m + 1) => xcOf ℓ π i) (.tg i) ↔
        eval σ A (sgE (.lit i)) = 0 ∧ eval σ A j < bW ∧ β.toNat = 0) ∧
    (∀ (i : Fin (m + 1)) (j : Ex) (β : Bool),
      (eval σ A j, β) ∈ Cl (instOf p a b xR yR n) bW (fun i : Fin (m + 1) => sgOf ℓ π i)
          (fun i : Fin (m + 1) => xcOf ℓ π i) (.v (.x i)) ↔
        eval σ A (xcDefE (.lit i) j) = 1 ∧ eval σ A (xcBitE (.lit i) j) = β.toNat) ∧
    (∀ s : Slot m, ((∀ c, s ≠ .cst c) ∧ (∀ i, s ≠ .tg i) ∧ (∀ i, s ≠ .v (.x i))) →
      Cl (instOf p a b xR yR n) bW (fun i : Fin (m + 1) => sgOf ℓ π i)
          (fun i : Fin (m + 1) => xcOf ℓ π i) s = []) ∧
    (∀ c : Cn m, formF (fun i : Fin (m + 1) => sgDec (eval σ A (sgE (.lit i)))) c =
        formF (fun i : Fin (m + 1) => sgOf ℓ π i) c) := by
  intro σ A
  have hX : Bd p n < 2 ^ Nat.size p := lt_of_le_of_lt (Bd_le hp n) (Nat.lt_size_self p)
  have hlt : ∀ v, v < p → v < 2 ^ Nat.size p := fun v hv => lt_trans hv (Nat.lt_size_self p)
  have hR : Reads σ A p a b (Bd p n) xR yR π ℓ bW :=
    reads_memIn p a b _ xR yR π _ ℓ bW (Nat.lt_size_self p) (hlt a ha) (hlt b hb) hX (hlt xR hx) (hlt yR hy)
  refine ⟨hR, fun c j β => Cl_cst_iff hR rfl hodd c j β, fun i j β => Cl_tg_iff hR i j β,
    fun i j β => Cl_x_iff hR i j β, fun s hs => Cl_other _ _ _ _ s hs, fun c => formF_dec hR c⟩

/-- **τ (Definition 2) for the input layer.**  For `L = Nat.size p ≥ 4`, `m ≤ L` points and pinned-constant width
`bW = N0.b 2^{N0.k} ≤ 36 L` (explicit parameters of L59): evaluating any of the bit expressions at variables with
values `≤ 36 L` costs at most `200 (36 L + 1)²` source steps (`130 · 36 L + 300` for a constant bit); the
expressions themselves have at most 60 nodes. -/
theorem tau_explicit (L : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (x y : ℕ) (hx : σ x ≤ 36 * L) (hy : σ y ≤ 36 * L)
    (h2 : σ 2 ≤ 36 * L) :
    (∀ c, cost σ A (cvBitE c (.var y)) ≤ 130 * (36 * L) + 300) ∧
    cost σ A (xcDefE (.var x) (.var y)) ≤ 200 * (36 * L + 1) ^ 2 ∧
    cost σ A (xcBitE (.var x) (.var y)) ≤ 200 * (36 * L + 1) ^ 2 ∧
    cost σ A (sgE (.var x)) ≤ 200 * (36 * L + 1) ^ 2 ∧
    (∀ c, sz (cvBitE c (.var y)) ≤ 60) ∧ sz (xcDefE (.var x) (.var y)) ≤ 60 ∧ sz (xcBitE (.var x) (.var y)) ≤ 60 ∧
    sz (sgE (.var x)) ≤ 60 := by
  obtain ⟨a1, a2, a3⟩ := cost_prefix_var (σ := σ) (A := A) hx hy h2
  obtain ⟨b1, b2, b3⟩ := sz_prefix_var x y
  refine ⟨fun c => (cost_cvBitE_var c y).trans (by omega), a1, a2, a3, fun c => sz_cvBitE_var c y, b1, b2, b3⟩

end ECDLP.L63
end
