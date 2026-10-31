import ECDLP.L96_Final
import ECDLP.L95_Edge
import ECDLP.L94_Final

/-!
# L96 / Bnd: `FrameBnd` for the real clamped network of the repaired instance, from L95's `nbdd_real2C`, L84's `bdd_gEx`, L94's `bdd_btEx`

Remaining named hypotheses: `BddHyps r` = (`hbn`, `hsN`, `hcV`, `hwV`, `hsrc`) on frame data (the five open hypotheses of L95 `nbdd_real2C`).
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

abbrev dNet (r : ℕ) (d : FrData) (m : ℕ) :=
  edgeNetM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m

abbrev dEnum (r : ℕ) (d : FrData) := (layOf (sgR r (ell d.p r) d.τ)).enum (NParE (Nat.size d.p)).A

/-- **`BddHyps`**: the five numeric / source-weight hypotheses of L95 `nbdd_real2C` on frame data. -/
def BddHyps (r : ℕ) : Prop :=
  ∀ (d : FrData) (m n k : ℕ) (B : ℕ → ℕ → ℕ) (V ℓ : ℕ), (∀ j, B 3 j = 0) → FrD r n B d →
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

theorem nodes_le_V {r V m K0 ℓ n : ℕ} (h : EdgeReq r V m K0 ℓ n) (hK0 : 2 ≤ K0) : ECDLP.L65.nodesE r n ≤ V := by
  have hg : 1 ≤ Gs K0 ℓ := by
    show 1 ≤ 3 * Kb K0 ℓ ^ 8
    have := Nat.pow_pos (n := 8) (show 0 < Kb K0 ℓ by have := Kb_ge K0 hK0 ℓ; omega)
    omega
  exact le_trans (Nat.le_mul_of_pos_left _ hg) h.hgN


/-- **`FrameBnd` for the real clamped network of the repaired instance**, from `BddHyps` -/
theorem frameBnd_real2 (r : ℕ) (H : BddHyps r) : FrameBnd r (Ereal2 r) (gEreal2 r) (btReal2 r) := by
  intro d m n k B hB3 hD V ℓ hE hk hA1 σ₀ hC
  have hm1 : 1 < m := hE.hm
  have hR := readsR_of_frD (m := m) (k := k) hB3 hD
  have hodd : d.p % 2 = 1 := hD.2.1
  have hnS : Nat.size d.p + 4 ≤ 4 * n := hD.2.2.2.2.2.2.1
  obtain ⟨hbn, hsN, hcV, hwV, hsrc⟩ := H d m n k B V ℓ hB3 hD hE hk hA1 hm1 hR hodd
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

/-- **Capstone (conditional)**: `subexponentialRate (r+1)` for `r >= 1` from `BddHyps r` and `OffFrame` only. -/
theorem subexp_real2' (r : ℕ) (hr1 : 1 ≤ r) (H : BddHyps r) (Hj : OffFrame r (Ereal2 r) (gEreal2 r) (btReal2 r)) :
    (ECDLP.SubexponentialRateStmt (r + 1)) :=
  subexp_real2 r hr1 (frameBnd_real2 r H) Hj

end ECDLP.L96
end
