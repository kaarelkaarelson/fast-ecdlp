import ECDLP.L96_F
import ECDLP.L96_Bnd

/-!
# L104 / Real: the real network as `EdgeCoreF` with the invariant `P n A := Fr r n (zero3 A) /\ 4 (Uc r)^4 <= n` -- no `r + 1 <= 2^19000`
`hbnL_real`: `BN` needs `Ub r n <= V`, from `n >= 4 (Uc r)^4` (L92 `Ub_le_two_pow_large`) and `hset`, instead of `ok_U0 hr`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L104R
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51 ECDLP.L85B ECDLP.L57 ECDLP.L75 ECDLP.L96

/-- **`BddHyps`**: the five numeric / source-weight hypotheses of L95 `nbdd_real2C` on frame data. -/
def BddHypsL (r : ℕ) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ) (V ℓ : ℕ), (∀ j, B 3 j = 0) → FrD r n B d → 4 * Uc r ^ 4 ≤ n →
    EdgeReq r V m Factoring.Aux.K0u ℓ n → k ≤ n → (∀ a j, B a j ≤ 1) →
    ∀ (hm1 : 1 < m) (hR : ReadsR (CtxM m n k) B r d.p d.a d.b d.xR d.yR d.τ) (hodd : d.p % 2 = 1),
      (∀ σ₀, CtxM m n k σ₀ → BN V σ₀ B r) ∧
      (∀ a : ℕ, sN (dNet r d m) (dEnum r d) a ≤ V) ∧
      (∀ a b : Fin ((layOf (sgR r (ell d.p r) d.τ)).gTot (NParE (Nat.size d.p)).A),
        2 ^ (toGNetE (dNet r d m) (ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
          (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m)).c
          ((dEnum r d).symm a) ((dEnum r d).symm b) ≤ V) ∧
      (∀ i, (dNet r d m).w i + 1 ≤ V) ∧
      (∀ σ₀, CtxM m n k σ₀ → ∀ σ : ℕ → ℕ, Ag 13 σ₀ σ →
        ∀ (a : Fin ((layOf (sgR r (ell d.p r) d.τ)).gTot (NParE (Nat.size d.p)).A)) (i : Slot r) (s : Fin (NParE (Nat.size d.p)).A),
          (dEnum r d).symm a = CG.src i s → σ (16 + 4) = a → σ (16 + 7) ≤ V →
          σ (16 + 10) = 2 ^ (NParE (Nat.size d.p)).b → σ (16 + 12) = (NParE (Nat.size d.p)).A →
          σ (16 + 13) = (NParE (Nat.size d.p)).h → σ (16 + 14) = (NParE (Nat.size d.p)).b →
          σ (16 + 16) = (layOf (sgR r (ell d.p r) d.τ)).eι i → σ (16 + 17) = s →
          Bdd V σ B (rSrc2 r d.p d.a d.b d.xR d.yR d.τ m hm1 hR hodd).srcE)

/-- `FrameBnd` restricted to frames with `4 (Uc r)^4 <= n` -/
def FrameBndL (r : ℕ) (E : NEx) (gE btE : Ex) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ), (∀ j, B 3 j = 0) → FrD r n B d → 4 * Uc r ^ 4 ≤ n → ∀ (V ℓ : ℕ),
    EdgeReq r V m Factoring.Aux.K0u ℓ n → k ≤ n → (∀ a j, B a j ≤ 1) → ∀ σ₀, CtxM m n k σ₀ →
      NBdd V 13 σ₀ B (NVars.std 16) E (fN r d m).gI ∧ (∀ σ, Ag 13 σ₀ σ → Bdd V σ B gE) ∧
        (∀ σ, Ag 13 σ₀ σ → ∀ j : Fin (fN r d m).gI, σ 20 = j → Bdd V σ B btE)

/-- `BN` on frame data (needs `Ub r n <= V`, i.e. `hr : r + 1 <= 2^19000` through `ok_U0`) -/
theorem hbnL_real {r V m k ℓ n : ℕ} (hL : 4 * Uc r ^ 4 ≤ n) (d : FrData) {B : ℕ → ℕ → ℕ} (hD : FrD r n B d)
    (hE : EdgeReq r V m Factoring.Aux.K0u ℓ n) (hA1 : ∀ a j, B a j ≤ 1) :
    ∀ σ₀, CtxM m n k σ₀ → BN V σ₀ B r := by
  intro σ₀ hC
  obtain ⟨hp0, hodd, ha, hb, hx, hy, hnS, hRd, hlen, h2s⟩ := hD
  have h0 : σ₀ 0 = n := hC.2.2.1
  have hn16 := hE.hn
  have hN := nodes_le_V hE (show 2 ≤ Factoring.Aux.K0u by decide)
  have hq := ECDLP.L95.hn_r_of_nodes r n hN
  have hUb : Ub r n ≤ V := le_trans (Ub_le_two_pow_large r n hL) hE.hset
  have hUg := Ub_ge r n (Nat.size d.p) hnS
  have hell : ell d.p r ≤ Nat.size d.p := Nat.size_le_size (Bd_le hp0 r)
  have hbW := bWof_le (Nat.size d.p) h2s
  have e9 : numCells (B 9) 1 n = d.τ.length := hRd.hlen
  have e10 : numCells (B 10) 1 n = ell d.p r := hRd.hl
  have e11 : numCells (B 11) 1 n = ECDLP.L72.bWof (Nat.size d.p) := hRd.hbW
  refine ⟨by omega, hA1, by rw [h0]; omega, by rw [h0, e9]; omega, by rw [h0, e10]; omega,
    by rw [h0, e11]; omega, ?_, by omega⟩
  rw [h0, e10]
  have : (r + 2) * (ell d.p r + 2) ≤ 96552 * (r + 1) * (Nat.size d.p + 4) := by
    calc (r + 2) * (ell d.p r + 2) ≤ (2 * (r + 1)) * (Nat.size d.p + 4) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 96552 * (r + 1) * (Nat.size d.p + 4) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **`BddHyps` on frame data, from `r + 1 <= 2^19000`** -/
theorem bddHypsL_real (r : ℕ) : BddHypsL r := by
  intro d m n k B V ℓ hB3 hD hL hE hk hA1 hm1 hR hodd
  have hnS : Nat.size d.p + 4 ≤ 4 * n := hD.2.2.2.2.2.2.1
  have hbn := hbnL_real (k := k) hL d hD hE hA1
  exact ⟨hbn, hsN_real d hD.1 hnS hE, hcV_real d hnS hE.hset, hwV_real d hnS hE.hset,
    hsrc_real d hnS hE hbn hm1 hR hodd⟩

/-- **`FrameBnd` for the real clamped network of the repaired instance**, from `BddHyps` -/
theorem frameBndL_real2 (r : ℕ) (H : BddHypsL r) : FrameBndL r (Ereal2 r) (gEreal2 r) (btReal2 r) := by
  intro d m n k B hB3 hD hL V ℓ hE hk hA1 σ₀ hC
  have hm1 : 1 < m := hE.hm
  have hR := readsR_of_frD (m := m) (k := k) hB3 hD
  have hodd : d.p % 2 = 1 := hD.2.1
  have hnS : Nat.size d.p + 4 ≤ 4 * n := hD.2.2.2.2.2.2.1
  obtain ⟨hbn, hsN, hcV, hwV, hsrc⟩ := H d m n k B V ℓ hB3 hD hL hE hk hA1 hm1 hR hodd
  have hset := hE.hset
  have h16 : 16 * n + 4 ≤ V := hE.hn
  have hN := nodes_le_V hE (show 2 ≤ Factoring.Aux.K0u by decide)
  have hn' := ECDLP.L95.hn_r_of_nodes r n hN
  have N := ECDLP.L95.lnum2_edge (Nat.size d.p) n hnS hset h16
  have IB := ECDLP.L95.instBdd_real2 (n := r) (ℓ := ell d.p r) (π := d.τ) (u := 16) (V := V) (by norm_num : 0 < 13) hR hbn hn' N
  have DN := ECDLP.L95.decNum_real r d.p n hnS hset hN (sgR r (ell d.p r) d.τ)
  have hphiB := ECDLP.L95.phiBdd_real2 (n := r) (ℓ := ell d.p r) (π := d.τ) (u := 16) (V := V) (by norm_num : 0 < 13) hR hbn hn' N
  obtain ⟨Fa, Mid, hw5, NN, hAAv, h8, hMV⟩ := edge_num (K := 18 * r + 12) (Nat.size d.p) n hnS hset
  have hWm : ECDLP.L65.Wm r n ≤ V :=
    le_trans (le_trans (Pb_ge r (Gs Factoring.Aux.K0u ℓ) n) (Nat.lt_two_pow_self).le) hE.hWc
  have hS : (NParE (Nat.size d.p)).b * (NParE (Nat.size d.p)).h + 1 ≤ V := by
    have h1 := (ECDLP.L89.parB (Nat.size d.p) n hnS).hbh
    have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ (Xs_pos n)
    refine ECDLP.L89.le_V hset ?_
    have := ECDLP.L89.Sb_ge n
    show bP (Nat.size d.p) * hP (Nat.size d.p) + 1 ≤ Sb n
    omega
  refine ⟨?_, ?_, ?_⟩
  · have h := ECDLP.L95.nbdd_real2C (n := r) (B := 13) (by norm_num) hR (u := 16) (V := V) (by norm_num) (m := m)
      (okR r d.p d.a d.b d.xR d.yR d.τ) n hnS hset h16 hN hbn (rSrc2 r d.p d.a d.b d.xR d.yR d.τ m hm1 hR hodd)
      hsN hcV hwV hsrc hm1 hC
    have := edge_free_nonempty (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
      (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m
    have e : netEx (pexEdgeC (ECDLP.L95.instEx2 (n := r) 16 (by norm_num : 0 < 13) hR)
        (phiExInst 16 (by norm_num : 0 < 13) hR) (by norm_num : 13 ≤ 16) hm1
        (ECDLP.L95.kindsReal2' (by norm_num : 0 < 13) hR (by norm_num : 13 ≤ 16) m (okR r d.p d.a d.b d.xR d.yR d.τ))
        (rSrc2 r d.p d.a d.b d.xR d.yR d.τ m hm1 hR hodd)) =
        Efields (realPEx2 r d.p d.a d.b d.xR d.yR d.τ m hm1 hR hodd) := rfl
    rw [e, Efields_irrel2] at h
    exact h
  · intro σ hσ
    exact bdd_gEx (rInst2 r d.p d.a d.b d.xR d.yR d.τ hR) IB DN (by norm_num) hC hσ
  · intro σ hσ j hj
    exact ECDLP.L94.bdd_btEx (rInst2 r d.p d.a d.b d.xR d.yR d.τ hR) (rPhi2 r d.p d.a d.b d.xR d.yR d.τ hR)
      (by norm_num : 13 ≤ 16) hC hσ IB DN h8 hphiB
      (fun q => (ECDLP.L94.wtB_le_Wm (K := 18 * r + 12) (Nat.size d.p) n (sgR r (ell d.p r) d.τ) (cnEquiv r) hnS q).trans hWm)
      (bP_pos _) Nat.one_le_two_pow hS (xs := 20) (by norm_num) hj

/-- the frame network satisfies the `EdgeCore` fields (frame memory with array `3` clear, `n` large) -/
theorem frame_fieldsL (r : ℕ) (d : FrData) (m : ℕ) {E : NEx} {gE btE : Ex} (hrep : FrameRep r E gE) (hbt : HbtE r btE) (hw : WtBnd r)
    (hb : FrameBndL r E gE btE) (n k : ℕ) (B : ℕ → ℕ → ℕ) (hB3 : ∀ j, B 3 j = 0) (hD : FrD r n B d) (hL : 4 * Uc r ^ 4 ≤ n) :
    FieldsAt r E gE btE m n k B (fN r d m) where
  hgI := gTot_pos (sgR r (ell d.p r) d.τ)
  hnodes := ECDLP.L95.gTot_le_nodes r d.p n hD.2.2.2.2.2.2.1 (sgR r (ell d.p r) d.τ)
  rep σ₀ hm hk hC := (hrep d m n k B σ₀ hm hB3 hD hC).1
  clh σ₀ hm hk hC := ⟨by norm_num, (hrep d m n k B σ₀ hm hB3 hD hC).2, hbt d m n k B σ₀ hB3 hD hC⟩
  hrow := fN_hrow r d m
  hheld := fN_hheld r d m
  hmax a := (hw d m n hD.1 hD.2.2.2.2.2.2.1).1 a
  htot := (hw d m n hD.1 hD.2.2.2.2.2.2.1).2
  bnd V ℓ hR hk hA1 σ₀ hC := hb d m n k B hB3 hD hL V ℓ hR hk hA1 σ₀ hC


open Classical in
/-- the network assigned to `(m, n, k, A)`: the frame network if `A` is a frame, else a default -/
def DrealL (r : ℕ) : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → WNet m :=
  fun m n k A => if h : Fr r n (zero3 A) then fN r (Classical.choose h) m else fN r ⟨1, 0, 0, 0, 0, []⟩ m

/-- the frame invariant -/
def PL (r : ℕ) : ℕ → (ℕ → ℕ → ℕ) → Prop := fun n A => Fr r n (zero3 A) ∧ 4 * Uc r ^ 4 ≤ n

theorem PL_cong (r : ℕ) : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → PL r n A → PL r n A' := by
  intro n A A' h hP
  have := zero3_eq_of_agree h
  unfold PL; rw [this]; exact hP

open Classical in
/-- **The real network as a frame-restricted `EdgeCore 200`, for every `r`** (repaired instance, clamped dispatch). -/
def edgeCoreFL_real2 (r : ℕ) : EdgeCoreF (PL r) 200 r (Ereal2 r) (gEreal2 r) (btReal2 r) where
  syn := exSyn_real2 r
  D := DrealL r
  hcong m n k A A' h := by
    have := zero3_eq_of_agree h
    show (if h : Fr r n (zero3 A') then _ else _) = (if h : Fr r n (zero3 A) then _ else _)
    simp only [this]
  fields m n k A hA := by
    apply FieldsAt.of_zero3 (noRdAll_real2 r)
    unfold DrealL
    rw [dif_pos hA.1]
    exact frame_fieldsL r (Classical.choose hA.1) m (frameRep_real2 r) (hbtE_real2 r) (wtBnd_real r)
      (frameBndL_real2 r (bddHypsL_real r)) n k (zero3 A) (zero3_clear A) (Classical.choose_spec hA.1) hA.2

end ECDLP.L104R
end
