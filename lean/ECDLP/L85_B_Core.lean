import ECDLP.L85_B_Syn

/-!
# L72 / Core: `ShapeData` for the edge family from a gate-network core (assembly of items 1-6)

`edgeShape r E gE btE`: the `TopShape` of the edge family with network expressions `E` (the five fields), `gE`
(node count) and `btE` (node weight; the cluster map is `clusM`).  `EdgeCore DB r E gE btE` lists what remains to be
supplied by the gate-level layer (L68): for every modulus / length / position / memory a weighted coded network with
the expression-level representation (`NRep`), the weights (`rowsum <= wt`, `s a <= 2^wt a`, `wt <= Wm`, `Sum wt <= Ub`,
gate count), the value bounds of the expressions, and the syntactic conditions `ExSyn`.
`shapeData_edge`: then `ShapeData DB (edgeFamily r) (edgeShape ..) (searchMv ..) (tabMv ..)` (for `r+1 <= 2^19000`).
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A

/-- the top shape of the edge family -/
def edgeShape (r : ℕ) (E : NEx) (gE btE : Ex) : TopShape where
  sF := sOf
  sE := Ex.sE
  eval_sE := fun _ _ => eval_sE
  U0 s := Uc r * (2 ^ s) ^ 4
  P0 s g := Uc r * (2 ^ s) ^ 4 / g + Wcn r * (2 ^ s) ^ 3
  L0E := edgeL0 r
  eval_L0E := fun K g s σ A h => by rw [eval_edgeL0, h]
  E := E
  gE := gE
  χE g := clusM (.lit g) gE btE

theorem edgeShape_cp (r : ℕ) (E : NEx) (gE btE : Ex) (g : ℕ) : (edgeShape r E gE btE).cp g = cpM E gE btE g := rfl
theorem edgeShape_gs (r : ℕ) (E : NEx) (gE btE : Ex) (K g : ℕ) :
    (edgeShape r E gE btE).gs K g = gsM E gE btE K g := rfl

/-- a weighted coded network -/
structure WNet (m : ℕ) where
  gI : ℕ
  inner : Net (ZMod m) gI
  κ : Coding inner
  wt : Fin gI → ℕ

def WNet.toRep {m : ℕ} (w : WNet m) : RepNet m := ⟨w.gI, w.inner, w.κ, fun g hg => clus w.wt g hg⟩

/-- the context in which the engine evaluates the network expressions -/
def CtxM (m n k : ℕ) (σ₀ : ℕ → ℕ) : Prop := σ₀ 10 = m ∧ σ₀ 11 = sOf n ∧ σ₀ 0 = n ∧ σ₀ 2 = k

/-- **What the gate-level layer (L68) must supply.** -/
structure EdgeCore (DB : ℕ) (r : ℕ) (E : NEx) (gE btE : Ex) where
  syn : ExSyn DB E gE btE
  D : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → WNet m
  /-- the network does not depend on array `3` (the engine's table) -/
  hcong : ∀ m n k A A', (∀ a, a ≠ 3 → A' a = A a) → D m n k A' = D m n k A
  hgI : ∀ m n k A, 0 < (D m n k A).gI
  hnodes : ∀ m n k A, (D m n k A).gI ≤ ECDLP.L65.nodesE r n
  rep : ∀ m n k A σ₀, 1 < m → k ≤ n → CtxM m n k σ₀ →
    NRep m 10 13 σ₀ A (NVars.std 16) E (D m n k A).inner (D m n k A).κ
  clh : ∀ m n k A σ₀, 1 < m → k ≤ n → CtxM m n k σ₀ →
    ClusHyp 13 (D m n k A).gI σ₀ A gE btE (D m n k A).wt
  hrow : ∀ m n k A (a : Fin (D m n k A).gI), ∑ b, (D m n k A).inner.cc a b ≤ (D m n k A).wt a
  hheld : ∀ m n k A (a : Fin (D m n k A).gI), (D m n k A).κ.s a ≤ 2 ^ (D m n k A).wt a
  hmax : ∀ m n k A (a : Fin (D m n k A).gI), (D m n k A).wt a ≤ Wm r n
  htot : ∀ m n k A, ∑ a, (D m n k A).wt a ≤ Ub r n
  /-- value bounds of the expressions (from `PExB`/`nbdd_netEx` in the real net) -/
  bnd : ∀ V m ℓ n k A, EdgeReq r V m K0u ℓ n → k ≤ n → (∀ a j, A a j ≤ 1) → ∀ σ₀, CtxM m n k σ₀ →
    NBdd V 13 σ₀ A (NVars.std 16) E (D m n k A).gI ∧ (∀ σ, Ag 13 σ₀ σ → Bdd V σ A gE) ∧
      (∀ σ, Ag 13 σ₀ σ → ∀ j : Fin (D m n k A).gI, σ 20 = j → Bdd V σ A btE)

/-! ### arithmetic -/

theorem sq_le_two_pow : ∀ w : ℕ, 4 ≤ w → w * w ≤ 2 ^ w := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have : (w + 1) * (w + 1) ≤ 2 * (w * w) := by nlinarith
    rw [pow_succ]; omega

theorem nodes_le_Wm (r n : ℕ) : ECDLP.L65.nodesE r n ≤ Wm r n := by
  unfold ECDLP.L65.nodesE Wm Wcn
  have h1 : Xs n ^ 2 ≤ Xs n ^ 3 := Nat.pow_le_pow_right (Xs_pos n) (by norm_num)
  have : 828 * (r + 1) * Xs n ^ 2 ≤ 20532 * (r + 1) * Xs n ^ 3 := by
    calc 828 * (r + 1) * Xs n ^ 2 ≤ 20532 * (r + 1) * Xs n ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 20532 * (r + 1) * Xs n ^ 3 := Nat.mul_le_mul_left _ h1
  exact this

theorem Wm_ge (r n : ℕ) : 20532 ≤ Wm r n := by
  unfold Wm Wcn
  have : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ (Xs_pos n)
  nlinarith

theorem Pb_ge (r g n : ℕ) : Wm r n ≤ Pb r g n := Nat.le_add_left _ _

theorem gI_sq_le {r g n gI : ℕ} (h : gI ≤ ECDLP.L65.nodesE r n) : gI * gI ≤ 2 ^ Pb r g n := by
  have h1 : gI ≤ Wm r n := le_trans h (nodes_le_Wm r n)
  have h2 := sq_le_two_pow (Wm r n) (by have := Wm_ge r n; omega)
  exact le_trans (Nat.mul_le_mul h1 h1) (le_trans h2 (Nat.pow_le_pow_right (by norm_num) (Pb_ge r g n)))

theorem Ub_le_gP (r g n : ℕ) (hg : 0 < g) : Ub r n ≤ g * Pb r g n := by
  have h1 : Ub r n < g * (Ub r n / g + 1) := by
    have := Nat.div_add_mod (Ub r n) g
    have := Nat.mod_lt (Ub r n) hg
    rw [mul_add, mul_one]; omega
  have h2 : Ub r n / g + 1 ≤ Pb r g n := by
    have := Wm_ge r n; unfold Pb; omega
  exact le_trans h1.le (Nat.mul_le_mul_left _ h2)

/-- `g * Ub <= 2^(Pb * (2g/K))` for `g = 3 K^8` -/
theorem gUb_le {r n K : ℕ} (hK : 2 ≤ K) : 3 * K ^ 8 * Ub r n ≤ 2 ^ (Pb r (3 * K ^ 8) n * (2 * (3 * K ^ 8) / K)) := by
  set g := 3 * K ^ 8 with hg
  have hg0 : 0 < g := by have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  set P := Pb r g n with hP
  have hP1 : 1 ≤ P := by have := Wm_ge r n; have := Pb_ge r g n; omega
  have hdiv : 2 * g / K = 6 * K ^ 7 := by
    rw [hg, show 2 * (3 * K ^ 8) = K * (6 * K ^ 7) by ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv]
  have h1 : g * Ub r n ≤ g * g * P := by
    calc g * Ub r n ≤ g * (g * P) := Nat.mul_le_mul_left g (Ub_le_gP r g n hg0)
      _ = g * g * P := by ring
  have hPle : P ≤ 2 ^ P := Nat.lt_two_pow_self.le
  have hKlt : K < 2 ^ K := Nat.lt_two_pow_self
  have h2 : g * g ≤ 2 ^ (6 * K ^ 7 - 1) := by
    have hKK : 16 * K + 4 ≤ 6 * K ^ 7 - 1 := by
      have : 64 * K ≤ K ^ 7 := by
        have h6 : 2 ^ 6 ≤ K ^ 6 := Nat.pow_le_pow_left hK 6
        calc 64 * K ≤ K ^ 6 * K := Nat.mul_le_mul_right _ (by simpa using h6)
          _ = K ^ 7 := by ring
      omega
    have e1 : g * g = 9 * K ^ 16 := by rw [hg]; ring
    have e2 : K ^ 16 ≤ (2 ^ K) ^ 16 := Nat.pow_le_pow_left hKlt.le 16
    have e3 : (2 ^ K) ^ 16 = 2 ^ (16 * K) := by rw [← pow_mul]; ring_nf
    have e4 : 9 * K ^ 16 ≤ 2 ^ 4 * 2 ^ (16 * K) := by rw [← e3]; exact Nat.mul_le_mul (by norm_num) e2
    rw [e1]
    refine le_trans e4 ?_
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc g * Ub r n ≤ g * g * P := h1
    _ ≤ 2 ^ (6 * K ^ 7 - 1) * 2 ^ P := Nat.mul_le_mul h2 hPle
    _ = 2 ^ (6 * K ^ 7 - 1 + P) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (P * (6 * K ^ 7)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h1c : 1 ≤ 6 * K ^ 7 := by have := Nat.pow_pos (n := 7) (show 0 < K by omega); omega
        generalize 6 * K ^ 7 = c at h1c ⊢
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        obtain ⟨P', hP'⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
        rw [hP']
        simp only [Nat.add_sub_cancel]
        nlinarith

end ECDLP.L85B

namespace ECDLP.L85B
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A

theorem Gs_le_V {r V m K0 ℓ n : ℕ} (hK : 2 ≤ K0) (R : EdgeReq r V m K0 ℓ n) : Gs K0 ℓ ≤ V :=
  le_trans (Nat.le_mul_of_pos_left _ (by have := Kb_ge K0 hK ℓ; omega)) R.hKG

/-- **`ShapeData` for the edge family** from the gate-network core (the side condition `r + 1 <= 2^19000` is for
`ok_U0`). -/
def shapeData_edge (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) {E : NEx} {gE btE : Ex} (C : EdgeCore DB r E gE btE) :
    ShapeData DB (edgeFamily r) (edgeShape r E gE btE) (searchMv E gE btE) (tabMv E gE btE) where
  hsF n := rfl
  hLtop K g n := rfl
  hSX K := searchM_LS C.syn K (3 * K ^ 8)
  hTX K := tabM_LS C.syn K (3 * K ^ 8)
  hRd g := cpM_rd C.syn g
  dpS K g := searchM_dp C.syn K g 13 14
  dpT K g := tabM_dp C.syn K g
  D m n k A := (C.D m n k A).toRep
  hcong m n k A A' h := by rw [C.hcong m n k A A' h]
  hyp m n k A g hg σ₀ hm hkn h10 h11 h0 h2 :=
    coarsenHyp_of_cluster (C.rep m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) (C.hgI m n k A) hg
      (C.clh m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hm
  fits m n k A g hg := by
    have hf := (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg (C.hrow m n k A) (Wm r n)
      (C.hmax m n k A)).1
    intro γ
    refine le_trans (hf γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _
  total m n k A g hg :=
    le_trans (cluster_fits_total (N := (C.D m n k A).inner) (wt := (C.D m n k A).wt) hg (C.hrow m n k A) (Wm r n)
      (C.hmax m n k A)).2 (C.htot m n k A)
  Wc n g := Pb r g n
  csz m n k A g hg γ := by
    refine le_trans (coarsen_s_le (C.D m n k A).κ (clus (C.D m n k A).wt g hg) γ (C.D m n k A).wt
      (fun a _ => C.hheld m n k A a)) (Nat.pow_le_pow_right (by norm_num) ?_)
    refine le_trans (clus_wt_sum_le (C.D m n k A).wt (Wm r n) (C.hmax m n k A) g hg γ) ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _
  bdd V m ℓ n k A R hm hkn hA σ₀ h10 h11 h0 h2 hg := by
    have hK2 : 2 ≤ Kb K0u ℓ := Kb_ge K0u (by norm_num) ℓ
    obtain ⟨hEb, hgb, hbb⟩ := C.bnd V m ℓ n k A R hkn hA σ₀ ⟨h10, h11, h0, h2⟩
    have hmm : m * m ≤ V := R.mm
    have hV1 : 1 ≤ V := by have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity); omega
    have hW : ∑ a, (C.D m n k A).wt a ≤ V := le_trans (C.htot m n k A) (ok_U0 hr R)
    have hgW : Gs K0u ℓ * ∑ a, (C.D m n k A).wt a ≤ V := by
      refine le_trans (Nat.mul_le_mul_left _ (C.htot m n k A)) (le_trans (gUb_le hK2) R.hgrp)
    exact coarsenBdd_of_cluster hg (C.clh m n k A σ₀ hm hkn ⟨h10, h11, h0, h2⟩) hEb hgb hbb hmm
      (Gs_le_V (by norm_num) R) (le_trans (gI_sq_le (g := Gs K0u ℓ) (C.hnodes m n k A)) R.hWc) hV1 hW hgW
      (C.hrow m n k A) (C.hheld m n k A) (Wm r n) (C.hmax m n k A) (Pb r (Gs K0u ℓ) n)
      (Nat.add_le_add_right (Nat.div_le_div_right (C.htot m n k A)) _) R.hWc
  ok_mm R := R.mm
  ok_Kg R := R.hKg
  ok_gg R := R.hgg
  ok_KG R := R.hKG
  ok_g1 R := R.hg1
  ok_U0 R := ok_U0 hr R
  ok_P0 R := R.hWc
  ok_grp R := R.hgrp
  ok_LK R := R.hLK
  ok_m1 R := R.hm
  ok_hn R := R.hn
  ok_deep R := R.deep
  vS := searchMv_vb C.syn
  vT := tabMv_vb C.syn

end ECDLP.L85B
