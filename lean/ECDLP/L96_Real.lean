import ECDLP.L96_Net
import ECDLP.L93_Main
import ECDLP.L90_Real
import ECDLP.L90_NoRd
import ECDLP.L89_Rep
import ECDLP.L91_Real

/-!
# L96 / Real: the real clamped dispatch, `RealRep r (Ereal r) (gEreal r)`

`realPEx`: the `PEx` (clamped, `pexEdgeC`) of the real network from L83's `instEx`/`phiExInst`, L90's `kindsReal'`, L81's `srcWtSlot`,
for explicit instance data `(p a b xR yR τ)` and a context `Ctx` in which `Reads72` holds.
`Ereal r`, `gEreal r`: its expressions at a dummy instance (they do not depend on the instance data: `Efields_irrel`, by `rfl`).
`realRep_real`: L93's `RealRep` for `(Ereal r, gEreal r)`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L90 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51

/-- `NRep` transfers between memories that agree outside the arrays the expressions do not read -/
theorem nrep_congr_arr {m vm B : ℕ} {σ₀ : ℕ → ℕ} {A A' : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ} {N : Net (ZMod m) g}
    {κ : Coding N} {a : ℕ → Prop} (hA : ∀ b, ¬ a b → A' b = A b)
    (h1 : NoRd a E.sz) (h2 : NoRd a E.W) (h3 : NoRd a E.c) (h4 : NoRd a E.l) (h5 : NoRd a E.r)
    (h : NRep m vm B σ₀ A v E N κ) : NRep m vm B σ₀ A' v E N κ where
  hm := h.hm
  sz σ hσ x hx := by rw [eval_congr_arr hA _ h1]; exact h.sz σ hσ x hx
  W σ hσ x z hx hz := by rw [eval_congr_arr hA _ h2]; exact h.W σ hσ x z hx hz
  c σ hσ x y hxy hx hy := by rw [eval_congr_arr hA _ h3]; exact h.c σ hσ x y hxy hx hy
  l σ hσ x y hxy z q hx hy hz hq := by rw [eval_congr_arr hA _ h4]; exact h.l σ hσ x y hxy z q hx hy hz hq
  r σ hσ x y hxy z q hx hy hz hq := by rw [eval_congr_arr hA _ h5]; exact h.r σ hσ x y hxy z q hx hy hz hq

theorem reads72n_congr0 {σ σ' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : Reads72n σ A p a b X xR yR π ℓ bW) (h0 : σ' 0 = σ 0) : Reads72n σ' A p a b X xR yR π ℓ bW where
  hp := by simpa [h0] using h.hp
  ha := by simpa [h0] using h.ha
  hb := by simpa [h0] using h.hb
  hxR := by simpa [h0] using h.hxR
  hyR := by simpa [h0] using h.hyR
  hOp := by simpa [h0] using h.hOp
  hX := by simpa [h0] using h.hX
  hlen := by simpa [h0] using h.hlen
  hl := by simpa [h0] using h.hl
  hbW := by simpa [h0] using h.hbW
  hpi := h.hpi

section
variable {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ}

variable (r p a b xR yR : ℕ) (τ : List Bool) (m : ℕ)

def rInst (hR : ReadsR Ctx A r p a b xR yR τ) :=
  instEx (n := r) (u := 16) (B := 13) (by norm_num) hR

def rPhi (hR : ReadsR Ctx A r p a b xR yR τ) :=
  phiExInst (n := r) (u := 16) (B := 13) (by norm_num) hR

def rKinds (hR : ReadsR Ctx A r p a b xR yR τ) :=
  kindsReal' (n := r) (u := 16) (B := 13) (by norm_num) hR (by norm_num) m (okR r p a b xR yR τ)

def rSrc (hm1 : 1 < m) (hR : ReadsR Ctx A r p a b xR yR τ) (hodd : p % 2 = 1) :=
  srcWtSlot (L := layOf (sgR r (ell p r) τ)) (φ := phiR r (ell p r) τ) (F := frF (sgR r (ell p r) τ) (cnEquiv r))
    (m := m) (u := 16) (B := 13) (N0 := NParE (Nat.size p)) (w := fun _ => wP (Nat.size p)) (mm := r) hm1 (by norm_num)
    (by norm_num) (bP_pos _) rfl (slotIdx_slotEquiv r) hR rfl hodd
    (pex0 (F := frF (sgR r (ell p r) τ) (cnEquiv r)) (ok := okR r p a b xR yR τ) (m := m) (rInst r p a b xR yR τ hR)
      (rPhi r p a b xR yR τ hR) (by norm_num))


variable (hm1 : 1 < m) (hR : ReadsR Ctx A r p a b xR yR τ) (hodd : p % 2 = 1)

/-- **the `PEx` of the clamped real network** -/
def realPEx :=
  haveI := edge_free_nonempty (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
    (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p a b xR yR τ) m
  pexEdgeC (rInst r p a b xR yR τ hR) (rPhi r p a b xR yR τ hR) (by norm_num) hm1 (rKinds r p a b xR yR τ m hR)
    (rSrc r p a b xR yR τ m hm1 hR hodd)


/-- the dummy `PEx` -/
def dummyPEx (r : ℕ) := realPEx (Ctx := fun _ => False) (A := fun _ _ => 0) r 3 0 0 0 0 [] 2 (by norm_num)
  (fun _ h => h.elim) (by norm_num)

/-- **the network expressions of the real engine** -/
def Ereal (r : ℕ) : NEx := Efields (dummyPEx r)
/-- **the node-count expression of the real engine** -/
def gEreal (r : ℕ) : Ex := gOf (dummyPEx r)

theorem Efields_irrel : Efields (realPEx r p a b xR yR τ m hm1 hR hodd) = Ereal r := rfl
theorem gE_irrel : gOf (realPEx r p a b xR yR τ m hm1 hR hodd) = gEreal r := rfl


/-- the fields of the clamped real `PEx` read no array `3` or `>= 12` -/
theorem realPNoRd : PNoRd (realPEx r p a b xR yR τ m hm1 hR hodd) Out := by
  unfold realPEx pexEdgeC
  refine pnoRd_clamp (by norm_num) ?_
  have hI : InstNoRd Out (rInst r p a b xR yR τ hR) := instNoRd_real (n := r) (by norm_num) hR
  have hP : NoRd Out (rPhi r p a b xR yR τ hR).phiE := NoRd_phiExInst (n := r) (B := 13) (by norm_num) hR
  have hS : NoRd Out (rSrc r p a b xR yR τ m hm1 hR hodd).srcE := NoRd_srcE 16 r
  have hd := NoRd_dispatchReal' (n := r) (by norm_num) hR (by norm_num : 13 ≤ 16) m (okR r p a b xR yR τ)
    (rSrc r p a b xR yR τ m hm1 hR hodd) hS
  exact ⟨NoRd_gEx hI, NoRd_nfEx hI, NoRd_nmEx hI, NoRd_wEx hI, NoRd_parEx hI hP, hd.1, hd.2⟩

end

/-- **`RealRep` for the real clamped dispatch.** -/
theorem realRep_real (r : ℕ) : ECDLP.L93.RealRep r (Ereal r) (gEreal r) := by
  intro p a b xR yR π τ hG s hF m hm σ₀ hC
  have hodd : p % 2 = 1 := odd_of_good r (p, a, b, xR, yR, π) τ hG
  obtain ⟨hF0, hF2, hRd⟩ := hF
  have hR : ReadsR (ECDLP.L85B.CtxM m (redInp (p, a, b, xR, yR, π) τ).len 0) (zero3 s.ar) r p (a % p) (b % p)
      (xR % p) (yR % p) τ := by
    intro σ₁ hC1
    exact reads72_zero3 (reads72n_congr0 hRd (by rw [hC1.2.2.1, hF0]))
  have hm1 : 1 < m := hm
  have hnr := edge_nrepC (rInst r p (a % p) (b % p) (xR % p) (yR % p) τ hR)
    (rPhi r p (a % p) (b % p) (xR % p) (yR % p) τ hR) (by norm_num : 13 ≤ 16)
    (rKinds r p (a % p) (b % p) (xR % p) (yR % p) τ m hR)
    (rSrc r p (a % p) (b % p) (xR % p) (yR % p) τ m hm1 hR hodd) hC hC.1 hm1
  have hN := realPNoRd r p (a % p) (b % p) (xR % p) (yR % p) τ m hm1 hR hodd
  have hA : ∀ b, ¬ Out b → s.ar b = zero3 s.ar b := fun b hb => (zero3_off s.ar b hb).symm
  obtain ⟨n1, n2, n3, n4, n5⟩ := NoRd_Efields hN
  have := edge_free_nonempty (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
    (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p (a % p) (b % p) (xR % p) (yR % p) τ) m
  refine ⟨18 * r + 12, cnEquiv r, _, (layOf (sgR r (ell p r) τ)).enum (NParE (Nat.size p)).A,
    ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size p)) (phiR r (ell p r) τ)
      (frF (sgR r (ell p r) τ) (cnEquiv r)) (okR r p (a % p) (b % p) (xR % p) (yR % p) τ) m,
    ECDLP.L68.edgeEFM (phiR r (ell p r) τ) (frF (sgR r (ell p r) τ) (cnEquiv r))
      (okR r p (a % p) (b % p) (xR % p) (yR % p) τ) m, ?_⟩
  refine ⟨nrep_congr_arr (E := Efields (realPEx r p (a % p) (b % p) (xR % p) (yR % p) τ m hm1 hR hodd)) hA
    n1 n2 n3 n4 n5 hnr, ?_⟩
  intro σ hσ
  have hg := NoRd_gOf hN
  rw [show gEreal r = gOf (realPEx r p (a % p) (b % p) (xR % p) (yR % p) τ m hm1 hR hodd) from rfl,
    eval_congr_arr hA _ hg σ]
  exact (realPEx r p (a % p) (b % p) (xR % p) (yR % p) τ m hm1 hR hodd).hg σ₀ hC σ hσ

theorem zero3_of_clear {B : ℕ → ℕ → ℕ} (hB3 : ∀ j, B 3 j = 0) : zero3 B = B := by
  funext b
  by_cases hb : b = 3
  · subst hb; funext j; simp [zero3, hB3 j]
  · simp [zero3, hb]

/-- **`FrameRep` for the real clamped dispatch** (frame-data form of `edge_nrepC`; array `3` clear). -/
theorem frameRep_real (r : ℕ) : FrameRep r (Ereal r) (gEreal r) := by
  intro d m n k B σ₀ hm hB3 hD hC
  obtain ⟨hp0, hodd, ha, hb, hx, hy, hn, hRd, -⟩ := hD
  have hR : ReadsR (ECDLP.L85B.CtxM m n k) B r d.p d.a d.b d.xR d.yR d.τ := by
    intro σ₁ hC1
    have h1 := reads72_zero3 (reads72n_congr0 hRd (show σ₁ 0 = (fun _ => n) 0 from hC1.2.2.1))
    rw [zero3_of_clear hB3] at h1
    exact h1
  have hnr := edge_nrepC (rInst r d.p d.a d.b d.xR d.yR d.τ hR)
    (rPhi r d.p d.a d.b d.xR d.yR d.τ hR) (by norm_num : 13 ≤ 16)
    (rKinds r d.p d.a d.b d.xR d.yR d.τ m hR)
    (rSrc r d.p d.a d.b d.xR d.yR d.τ m hm hR hodd) hC hC.1 hm
  have := edge_free_nonempty (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m
  refine ⟨hnr, ?_⟩
  intro σ hσ
  exact (realPEx r d.p d.a d.b d.xR d.yR d.τ m hm hR hodd).hg σ₀ hC σ hσ

end ECDLP.L96
end
