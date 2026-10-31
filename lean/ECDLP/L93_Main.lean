import ECDLP.L93_Val
import ECDLP.L93_Count
import ECDLP.L88_Eng

/-!
# L93 / Main: `EdgeNetValue` for an `EdgeCore` whose expressions represent the real edge network

`RealRep r E gE`: the expressions `(E, gE)` of the core represent, in every layout-satisfying memory (`Good` instance, `FrameIn`
state) and every context `CtxM`, the REAL edge network `toGNetE (edgeNetM ..)` of the reduced instance `redInp x τ` (explicit
parameters of L59/L65) for SOME numbering `e` of the identities / gates `eg` and message / free codings `Em`, `EF`
(this is exactly the conclusion of L73 `edge_nrep` / L86 `edge_nrep3` for the real instance data), with `gE` evaluating
to its node count (the `hg` field of the `PEx`).
`edgeNetValue_of_core`: then `EdgeNetValue r C` (L88), for every `C : EdgeCore 200 r E gE btE`.
-/
noncomputable section
namespace ECDLP.L93
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L59 ECDLP.L64
  ECDLP.L44 ECDLP.L51 ECDLP.L65 ECDLP.L70 Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L80 ECDLP.L84 ECDLP.L85B ECDLP.L88 ECDLP.L61 ECDLP

/-- the forms of the real edge network (reduced instance `(p, a, b, xR, yR)`, prefix `τ`) -/
abbrev rF (r p : ℕ) (τ : List Bool) {K : ℕ} (e : Cn r ≃ Fin K) :=
  frF (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e

/-- the constraints of the real edge network -/
abbrev rOk (r p a b xR yR : ℕ) (τ : List Bool) {K : ℕ} (e : Cn r ≃ Fin K) :=
  okC (NParE (Nat.size p)) (Cl (instOf p a b xR yR r) ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
    (fun i : Fin (r + 1) => sgOf (ell p r) τ i) (fun i : Fin (r + 1) => xcOf (ell p r) τ i))

/-- the real edge network over `ZMod m` (explicit message coding `Em`) -/
abbrev rNet (r p a b xR yR : ℕ) (τ : List Bool) {K : ℕ} (e : Cn r ≃ Fin K) (m : ℕ) {g : ℕ}
    (eg : CG (Slot r) (UC (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e) (NParE (Nat.size p)).A ≃ Fin g)
    (Em : ∀ i, (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
      (rOk r p a b xR yR τ e) m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := fun _ : Fin K => wP (Nat.size p))
        (fun c => Subtype.val) (rF r p τ e) (rOk r p a b xR yR τ e) m).Msg i))) :=
  (toGNetE (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
    (rOk r p a b xR yR τ e) m) Em).toNet eg

/-- **The expressions of the core represent the real edge network.** -/
def RealRep (r : ℕ) (E : NEx) (gE : Ex) : Prop :=
  ∀ (p a b xR yR : ℕ) (π τ : List Bool), Good (r + 1) (p, a, b, xR, yR, π) τ → ∀ s : St,
    FrameIn r (redInp (p, a, b, xR, yR, π) τ) s → ∀ m, 1 < m → ∀ σ₀ : ℕ → ℕ,
    CtxM m (redInp (p, a, b, xR, yR, π) τ).len 0 σ₀ →
    ∃ (K : ℕ) (e : Cn r ≃ Fin K) (g : ℕ)
      (eg : CG (Slot r) (UC (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e) (NParE (Nat.size p)).A ≃ Fin g)
      (Em : ∀ i, (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
        (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m).Msg i ≃ Fin (Fintype.card
          ((edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
            (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m).Msg i)))
      (EF : ∀ i, (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
        (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m).Free i ≃ Fin (Fintype.card
          ((edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
            (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m).Free i))),
      haveI := edge_free_nonempty (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
        (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m
      NRep m 10 13 σ₀ s.ar (NVars.std 16) E (rNet r p (a % p) (b % p) (xR % p) (yR % p) τ e m eg Em)
        (pfCoding (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
          (rOk r p (a % p) (b % p) (xR % p) (yR % p) τ e) m) Em EF eg) ∧
      ∀ σ, Ag 13 σ₀ σ → Ex.eval σ s.ar gE = g

/-- the context used to instantiate `rep`: `σ 10 = m`, `σ 11 = sOf n`, `σ 0 = n`, `σ 2 = k`, everything else `0` -/
def ctx0 (m n k : ℕ) : ℕ → ℕ := fun y => if y = 10 then m else if y = 11 then sOf n else if y = 0 then n else if y = 2 then k else 0

theorem ctx0_ok (m n k : ℕ) : CtxM m n k (ctx0 m n k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ctx0]

/-- the value of the real edge network over `ZMod m` is the (cast) edge count -/
theorem rNet_value (r p a b xR yR : ℕ) (τ : List Bool) {K : ℕ} (e : Cn r ≃ Fin K) (m : ℕ) (hm : 1 < m) {g : ℕ}
    (eg : CG (Slot r) (UC (fun i : Fin (r + 1) => sgOf (ell p r) τ i) e) (NParE (Nat.size p)).A ≃ Fin g)
    (Em : ∀ i, (edgeNetM (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
      (rOk r p a b xR yR τ e) m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := fun _ : Fin K => wP (Nat.size p))
        (fun c => Subtype.val) (rF r p τ e) (rOk r p a b xR yR τ e) m).Msg i)))
    (hS : ∀ c, (NP (NParE (Nat.size p)) (fun _ : Fin K => wP (Nat.size p)) c).SizeOK (rF r p τ e c))
    (hb : 1 ≤ (NParE (Nat.size p)).b) :
    (rNet r p a b xR yR τ e m eg Em).value = ((edgeCount (fun c => Subtype.val) (rF r p τ e) (rOk r p a b xR yR τ e) : ℕ) : ZMod m) := by
  classical
  rw [value_toGNetE _ Em eg (edge_P01 (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
    (rOk r p a b xR yR τ e) m)]
  exact edge_value_zmod (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val) (rF r p τ e)
    (rOk r p a b xR yR τ e) m hm hS hb eg

/-- **`EdgeNetValue` for an `EdgeCore` whose expressions represent the real edge network** (`RealRep`). -/
theorem edgeNetValue_of_core (r : ℕ) (hr : 1 ≤ r) {E : NEx} {gE btE : Ex} (C : EdgeCore 200 r E gE btE)
    (H : RealRep r E gE) : EdgeNetValue r C := by
  classical
  intro x τ hG s hF m hm
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  set n := (redInp (p, a, b, xR, yR, π) τ).len with hn
  have hctx := ctx0_ok m n 0
  obtain ⟨K, e, g, eg, Em, EF, hrepR, hgR⟩ := H p a b xR yR π τ hG s hF m hm _ hctx
  have hrepC := C.rep m n 0 s.ar _ hm (Nat.zero_le _) hctx
  have hgC := (C.clh m n 0 s.ar _ hm (Nat.zero_le _) hctx).hgE _ (Ag.refl _ _)
  have hgg : (C.D m n 0 s.ar).gI = g := by rw [← hgC, ← hgR _ (Ag.refl _ _)]
  have hpar := parOK_explicit (K := K) p (a % p) (b % p) (xR % p) (yR % p) r (hG.1.pos)
    (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) τ e
  obtain ⟨hb1, -, -, hS⟩ := hpar
  have hval := rNet_value r p (a % p) (b % p) (xR % p) (yR % p) τ e m hm eg Em hS hb1
  have hcnt := edgeCount_real_eq_Zc r hr p a b xR yR π τ hG e
  rw [hcnt] at hval
  rw [← hval]
  generalize C.D m n 0 s.ar = D at hrepC hgg ⊢
  obtain ⟨gI, inner, κ, wt⟩ := D
  simp only at hgg hrepC ⊢
  subst hgg
  exact value_eq_of_nrep (VOk.std (by norm_num)) hrepC hrepR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`EngVal` for the real engine** with the value link discharged from `RealRep` (L88's `engVal_of_core` with
`hnet := edgeNetValue_of_core`); the remaining hypotheses are L88's `hlt` and `hA10`. -/
theorem engVal_of_realRep (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) (hr1 : 1 ≤ r) {E : NEx} {gE btE : Ex}
    (C : EdgeCore 200 r E gE btE) (H : RealRep r E gE)
    (hlt : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → Zc (r + 1) x τ < 2 ^ (redInp x τ).len)
    (hA10 : ∀ (i : EdgeInp) (s : St), FrameIn r i s → s.ar 1 0 = 0) :
    EngVal r (engCmd r E gE btE) :=
  engVal_of_core r hr C (edgeNetValue_of_core r hr1 C H) hlt hA10

end ECDLP.L93
end
