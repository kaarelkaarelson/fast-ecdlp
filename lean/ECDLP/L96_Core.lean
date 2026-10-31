import ECDLP.L96_Real
import ECDLP.L95_Dec

/-!
# L96 / Core: the frame network satisfies the `EdgeCore` fields (modulo named hypotheses), and the assembly `edgeCore200_real`

* `FieldsAt`: the `EdgeCore` fields (all but `syn`, `hcong`) for ONE weighted network `w` at ONE memory `A`.
* `frame_fields`: the frame network `fN r d m` satisfies `FieldsAt` on a frame memory, from `FrameRep`, `HbtE`, `WtBnd`, `FrameBnd`; the fields
  `hgI`, `hnodes` (L95 `gTot_le_nodes`), `hrow`, `hheld` (L57 `rowsum_le`, L75 `sN_le_wtH`) are PROVED here.
* `FieldsAt.of_zero3`: transfer from the memory `zero3 A` (array `3` cleared) to `A`, using `NoRd Out` of `E, gE, btE`.
* `edgeCore200_real`: `EdgeCore 200 r E gE btE` from the frame hypotheses and `OffFrame` (the network for non-frame memories).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51 ECDLP.L85B ECDLP.L57 ECDLP.L75

/-- the expressions read neither array `3` nor an array `>= 12` -/
structure NoRdAll (E : NEx) (gE btE : Ex) : Prop where
  sz : NoRd Out E.sz
  W : NoRd Out E.W
  c : NoRd Out E.c
  l : NoRd Out E.l
  r : NoRd Out E.r
  g : NoRd Out gE
  bt : NoRd Out btE

theorem nbdd_congr {V B : ℕ} {σ₀ : ℕ → ℕ} {A A' : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    (hA : ∀ b, ¬ Out b → A' b = A b) (n1 : NoRd Out E.sz) (n2 : NoRd Out E.W) (n3 : NoRd Out E.c)
    (n4 : NoRd Out E.l) (n5 : NoRd Out E.r) (h : NBdd V B σ₀ A v E g) : NBdd V B σ₀ A' v E g where
  sz σ hσ hx := (Bdd_congr_arr hA _ n1 σ).2 (h.sz σ hσ hx)
  W σ hσ hx hz := (Bdd_congr_arr hA _ n2 σ).2 (h.W σ hσ hx hz)
  c σ hσ hxy hy := (Bdd_congr_arr hA _ n3 σ).2 (h.c σ hσ hxy hy)
  l σ hσ hxy hy hz hq := (Bdd_congr_arr hA _ n4 σ).2 (h.l σ hσ hxy hy hz hq)
  r σ hσ hxy hy hz hq := (Bdd_congr_arr hA _ n5 σ).2 (h.r σ hσ hxy hy hz hq)

/-- **the `EdgeCore` fields (all but `syn`, `hcong`) for one network `w` at one memory `A`** -/
structure FieldsAt (r : ℕ) (E : NEx) (gE btE : Ex) (m n k : ℕ) (A : ℕ → ℕ → ℕ) (w : WNet m) : Prop where
  hgI : 0 < w.gI
  hnodes : w.gI ≤ ECDLP.L65.nodesE r n
  rep : ∀ σ₀, 1 < m → k ≤ n → CtxM m n k σ₀ → NRep m 10 13 σ₀ A (NVars.std 16) E w.inner w.κ
  clh : ∀ σ₀, 1 < m → k ≤ n → CtxM m n k σ₀ → ClusHyp 13 w.gI σ₀ A gE btE w.wt
  hrow : ∀ a : Fin w.gI, ∑ b, w.inner.cc a b ≤ w.wt a
  hheld : ∀ a : Fin w.gI, w.κ.s a ≤ 2 ^ w.wt a
  hmax : ∀ a : Fin w.gI, w.wt a ≤ ECDLP.L65.Wm r n
  htot : ∑ a, w.wt a ≤ ECDLP.L65.Ub r n
  bnd : ∀ V ℓ, EdgeReq r V m Factoring.Aux.K0u ℓ n → k ≤ n → (∀ a j, A a j ≤ 1) → ∀ σ₀, CtxM m n k σ₀ →
    NBdd V 13 σ₀ A (NVars.std 16) E w.gI ∧ (∀ σ, Ag 13 σ₀ σ → Bdd V σ A gE) ∧
      (∀ σ, Ag 13 σ₀ σ → ∀ j : Fin w.gI, σ 20 = j → Bdd V σ A btE)

theorem FieldsAt.of_zero3 {r : ℕ} {E : NEx} {gE btE : Ex} (N : NoRdAll E gE btE) {m n k : ℕ} {A : ℕ → ℕ → ℕ} {w : WNet m}
    (h : FieldsAt r E gE btE m n k (zero3 A) w) : FieldsAt r E gE btE m n k A w := by
  have hA : ∀ b, ¬ Out b → A b = zero3 A b := fun b hb => (zero3_off A b hb).symm
  refine ⟨h.hgI, h.hnodes, ?_, ?_, h.hrow, h.hheld, h.hmax, h.htot, ?_⟩
  · intro σ₀ hm hk hC
    exact nrep_congr_arr hA N.sz N.W N.c N.l N.r (h.rep σ₀ hm hk hC)
  · intro σ₀ hm hk hC
    have c := h.clh σ₀ hm hk hC
    exact ⟨c.hB, fun σ hσ => by rw [eval_congr_arr hA _ N.g σ]; exact c.hgE σ hσ,
      fun σ hσ j hj => by rw [eval_congr_arr hA _ N.bt σ]; exact c.hbt σ hσ j hj⟩
  · intro V ℓ hR hk hA1 σ₀ hC
    have hA1' : ∀ a j, zero3 A a j ≤ 1 := by
      intro a j
      by_cases ha : a = 3
      · subst ha; simp [zero3]
      · simpa [zero3, ha] using hA1 a j
    obtain ⟨b1, b2, b3⟩ := h.bnd V ℓ hR hk hA1' σ₀ hC
    exact ⟨nbdd_congr hA N.sz N.W N.c N.l N.r b1, fun σ hσ => (Bdd_congr_arr hA _ N.g σ).2 (b2 σ hσ),
      fun σ hσ j hj => (Bdd_congr_arr hA _ N.bt σ).2 (b3 σ hσ j hj)⟩


theorem gTot_pos (sg : Fin (r + 1) → Sg) : 0 < (layOf sg).gTot (NParE (Nat.size p)).A := by
  unfold ECDLP.L73.Lay.gTot
  have h1 : 0 < (layOf sg).nι := by simp [layOf]
  have h2 : 0 < (NParE (Nat.size p)).A := (NParE (Nat.size p)).toPar.A_pos
  exact Nat.add_pos_left (Nat.mul_pos h1 h2) _

section frame
variable (r : ℕ) (d : FrData) (m : ℕ)

theorem fN_hrow : ∀ a : Fin (fN r d m).gI, ∑ b, (fN r d m).inner.cc a b ≤ (fN r d m).wt a := by
  intro a
  have := edge_rowsum_Bw (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m
    (ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
      (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m)
    ((layOf (sgR r (ell d.p r) d.τ)).enum (NParE (Nat.size d.p)).A) a
  exact le_trans this (Nat.le_add_right _ _)

theorem fN_hheld : ∀ a : Fin (fN r d m).gI, (fN r d m).κ.s a ≤ 2 ^ (fN r d m).wt a := by
  intro a
  have h1 := sN_le_wtH (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m
    ((layOf (sgR r (ell d.p r) d.τ)).enum (NParE (Nat.size d.p)).A) a
  have h2 := rowsum_le_wtH (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ)
    ((layOf (sgR r (ell d.p r) d.τ)).enum (NParE (Nat.size d.p)).A) a
  have h3 := rowsum_le (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ)
    ((layOf (sgR r (ell d.p r) d.τ)).enum (NParE (Nat.size d.p)).A) a
  refine le_trans h1 (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold wtH
  show _ ≤ ECDLP.L94.wtB _ _ _ _
  unfold ECDLP.L94.wtB
  omega

/-- **the frame network satisfies the `EdgeCore` fields** (on a memory with array `3` clear) -/
theorem frame_fields {E : NEx} {gE btE : Ex} (hrep : FrameRep r E gE) (hbt : HbtE r btE) (hw : WtBnd r)
    (hb : FrameBnd r E gE btE) (n k : ℕ) (B : ℕ → ℕ → ℕ) (hB3 : ∀ j, B 3 j = 0) (hD : FrD r n B d) :
    FieldsAt r E gE btE m n k B (fN r d m) where
  hgI := gTot_pos (sgR r (ell d.p r) d.τ)
  hnodes := ECDLP.L95.gTot_le_nodes r d.p n hD.2.2.2.2.2.2.1 (sgR r (ell d.p r) d.τ)
  rep σ₀ hm hk hC := (hrep d m n k B σ₀ hm hB3 hD hC).1
  clh σ₀ hm hk hC := ⟨by norm_num, (hrep d m n k B σ₀ hm hB3 hD hC).2, hbt d m n k B σ₀ hB3 hD hC⟩
  hrow := fN_hrow r d m
  hheld := fN_hheld r d m
  hmax a := (hw d m n hD.1 hD.2.2.2.2.2.2.1).1 a
  htot := (hw d m n hD.1 hD.2.2.2.2.2.2.1).2
  bnd V ℓ hR hk hA1 σ₀ hC := hb d m n k B hB3 hD V ℓ hR hk hA1 σ₀ hC

end frame


theorem zero3_clear (A : ℕ → ℕ → ℕ) : ∀ j, zero3 A 3 j = 0 := by intro j; simp [zero3]

theorem zero3_eq_of_agree {A A' : ℕ → ℕ → ℕ} (h : ∀ a, a ≠ 3 → A' a = A a) : zero3 A' = zero3 A := by
  funext b
  by_cases hb : b = 3
  · subst hb; simp [zero3]
  · simp [zero3, hb, h b hb]

/-- **`OffFrame`**: for every non-frame memory (up to clearing array `3`) there is a weighted network satisfying all the fields.
This is the one hypothesis that is NOT a statement about the real network of an instance; see REPORT (memory-universality gap). -/
def OffFrame (r : ℕ) (E : NEx) (gE btE : Ex) : Prop :=
  ∀ (m n k : ℕ) (A : ℕ → ℕ → ℕ), ¬ Fr r n (zero3 A) → ∃ w : WNet m, FieldsAt r E gE btE m n k (zero3 A) w

open Classical in
/-- the network assigned to `(m, n, k, A)`: the frame network of the (chosen) instance data if `A` is a frame, else the off-frame network -/
def Dreal {r : ℕ} {E : NEx} {gE btE : Ex} (Hj : OffFrame r E gE btE) : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → WNet m :=
  fun m n k A => if h : Fr r n (zero3 A) then fN r (Classical.choose h) m else Classical.choose (Hj m n k A h)

open Classical in
theorem Dreal_fields {r : ℕ} {E : NEx} {gE btE : Ex} (hrep : FrameRep r E gE) (hbt : HbtE r btE) (hw : WtBnd r)
    (hb : FrameBnd r E gE btE) (N : NoRdAll E gE btE) (Hj : OffFrame r E gE btE) (m n k : ℕ) (A : ℕ → ℕ → ℕ) :
    FieldsAt r E gE btE m n k A (Dreal Hj m n k A) := by
  apply FieldsAt.of_zero3 N
  unfold Dreal
  by_cases h : Fr r n (zero3 A)
  · rw [dif_pos h]
    exact frame_fields r (Classical.choose h) m hrep hbt hw hb n k (zero3 A) (zero3_clear A) (Classical.choose_spec h)
  · rw [dif_neg h]
    exact Classical.choose_spec (Hj m n k A h)

open Classical in
/-- **`EdgeCore 200` for the real network**, from the syntactic conditions `ExSyn 200`, the read-set facts `NoRdAll`, the frame hypotheses
(`FrameRep` proved in `frameRep_real` for the real expressions; `HbtE`, `WtBnd`, `FrameBnd` pending) and `OffFrame`. -/
def edgeCore200_real {r : ℕ} {E : NEx} {gE btE : Ex} (hsyn : ECDLP.L85B.ExSyn 200 E gE btE) (N : NoRdAll E gE btE)
    (hrep : FrameRep r E gE) (hbt : HbtE r btE) (hw : WtBnd r) (hb : FrameBnd r E gE btE)
    (Hj : OffFrame r E gE btE) : EdgeCore 200 r E gE btE where
  syn := hsyn
  D := Dreal Hj
  hcong m n k A A' h := by
    have := zero3_eq_of_agree h
    show (if h : Fr r n (zero3 A') then _ else _) = (if h : Fr r n (zero3 A) then _ else _)
    simp only [this]
  hgI m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).hgI
  hnodes m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).hnodes
  rep m n k A σ₀ hm hk hC := (Dreal_fields hrep hbt hw hb N Hj m n k A).rep σ₀ hm hk hC
  clh m n k A σ₀ hm hk hC := (Dreal_fields hrep hbt hw hb N Hj m n k A).clh σ₀ hm hk hC
  hrow m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).hrow
  hheld m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).hheld
  hmax m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).hmax
  htot m n k A := (Dreal_fields hrep hbt hw hb N Hj m n k A).htot
  bnd V m ℓ n k A hR hk hA1 σ₀ hC := (Dreal_fields hrep hbt hw hb N Hj m n k A).bnd V ℓ hR hk hA1 σ₀ hC

end ECDLP.L96
end
