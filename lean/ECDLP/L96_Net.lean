import ECDLP.L96_NoRdTop
import ECDLP.L93_Main
import ECDLP.L94_Wt
import ECDLP.L75_Held

/-!
# L96 / Net: the canonical frame network `frameNet` (explicit WNet of the real clamped edge network of explicit instance data)
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51 ECDLP.L85B

section
variable {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ}

/-- the reads hypothesis of L83's instance, for the explicit instance data -/
abbrev ReadsR (Ctx : (ℕ → ℕ) → Prop) (A : ℕ → ℕ → ℕ) (r p a b xR yR : ℕ) (τ : List Bool) : Prop :=
  ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b (Bd p r) xR yR τ (ell p r) (ECDLP.L72.bWof (Nat.size p))

/-- the real constraints -/
abbrev okR (r p a b xR yR : ℕ) (τ : List Bool) :=
  ECDLP.L93.rOk r p a b xR yR τ (cnEquiv r)


/-- **the weighted coded real network of explicit instance data** (`m`-modulus, node weight `wtB`) -/
def frameNet (r p a b xR yR : ℕ) (τ : List Bool) (m : ℕ) : WNet m :=
  haveI := edge_free_nonempty (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
    (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m
  { gI := (layOf (sgR r (ell p r) τ)).gTot (NParE (Nat.size p)).A
    inner := (toGNetE (edgeNetM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m)
      (ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m)).toNet
      ((layOf (sgR r (ell p r) τ)).enum (NParE (Nat.size p)).A)
    κ := pfCoding (edgeNetM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m)
      (ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m)
      (ECDLP.L68.edgeEFM (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m)
      ((layOf (sgR r (ell p r) τ)).enum (NParE (Nat.size p)).A)
    wt := fun j => ECDLP.L94.wtB (phiR r (ell p r) τ) (NParE (Nat.size p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size p))
      (((layOf (sgR r (ell p r) τ)).enum (NParE (Nat.size p)).A).symm j) }


/-- explicit instance data of a frame -/
structure FrData where
  p : ℕ
  a : ℕ
  b : ℕ
  xR : ℕ
  yR : ℕ
  τ : List Bool

/-- **the frame predicate** (on a memory `B`, with scalar `σ 0 = n`): `B` holds the reduced instance data `d` in L72's layout
(arrays `0..11` except `3`), with `p` odd, residues reduced, `size p + 4 <= 4 n`, `|tau| + 1 <= n`, `2 <= size p`. No `Good`. -/
def FrD (r n : ℕ) (B : ℕ → ℕ → ℕ) (d : FrData) : Prop :=
  0 < d.p ∧ d.p % 2 = 1 ∧ d.a < d.p ∧ d.b < d.p ∧ d.xR < d.p ∧ d.yR < d.p ∧ Nat.size d.p + 4 ≤ 4 * n ∧
    Reads72n (fun _ => n) B d.p d.a d.b (Bd d.p r) d.xR d.yR d.τ (ell d.p r) (ECDLP.L72.bWof (Nat.size d.p)) ∧
    d.τ.length + 1 ≤ n ∧ 2 ≤ Nat.size d.p

def Fr (r n : ℕ) (B : ℕ → ℕ → ℕ) : Prop := ∃ d, FrD r n B d

/-- the frame network of data `d` -/
abbrev fN (r : ℕ) (d : FrData) (m : ℕ) : WNet m := frameNet r d.p d.a d.b d.xR d.yR d.τ m

/-- **`FrameRep E gE`**: on every frame memory (array `3` clear), in every context `CtxM m n k`, the expressions `(E, gE)` represent the frame network
(`rep` and the `hgE` clause of `clh`). Proved for the real expressions in `L96_Real` (`frameRep_real`). -/
def FrameRep (r : ℕ) (E : NEx) (gE : Ex) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ) (σ₀ : ℕ → ℕ), 1 < m → (∀ j, B 3 j = 0) → FrD r n B d → CtxM m n k σ₀ →
    NRep m 10 13 σ₀ B (NVars.std 16) E (fN r d m).inner (fN r d m).κ ∧
      ∀ σ, Ag 13 σ₀ σ → Ex.eval σ B gE = (fN r d m).gI

/-- **`HbtE btE`**: the weight expression evaluates to `wtB` at every node (L94 `eval_btEx`). -/
def HbtE (r : ℕ) (btE : Ex) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ) (σ₀ : ℕ → ℕ), (∀ j, B 3 j = 0) → FrD r n B d → CtxM m n k σ₀ →
    ∀ σ, Ag 13 σ₀ σ → ∀ j : Fin (fN r d m).gI, σ 20 = j → Ex.eval σ B btE = (fN r d m).wt j

/-- **`WtBnd`**: the numeric weight bounds (`hmax`, `htot` of `EdgeCore`) for `wtB` of the real layout. -/
def WtBnd (r : ℕ) : Prop :=
  ∀ (d : FrData) (m n : ℕ), 0 < d.p → Nat.size d.p + 4 ≤ 4 * n →
    (∀ j, (fN r d m).wt j ≤ Wm r n) ∧ ∑ j, (fN r d m).wt j ≤ Ub r n

/-- **`FrameBnd`**: the value bounds (`bnd` of `EdgeCore`) on a frame memory. -/
def FrameBnd (r : ℕ) (E : NEx) (gE btE : Ex) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ), (∀ j, B 3 j = 0) → FrD r n B d → ∀ (V ℓ : ℕ),
    EdgeReq r V m Factoring.Aux.K0u ℓ n → k ≤ n → (∀ a j, B a j ≤ 1) → ∀ σ₀, CtxM m n k σ₀ →
      NBdd V 13 σ₀ B (NVars.std 16) E (fN r d m).gI ∧ (∀ σ, Ag 13 σ₀ σ → Bdd V σ B gE) ∧
        (∀ σ, Ag 13 σ₀ σ → ∀ j : Fin (fN r d m).gI, σ 20 = j → Bdd V σ B btE)

end
end ECDLP.L96
end
