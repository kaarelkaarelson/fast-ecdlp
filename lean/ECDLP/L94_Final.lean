import ECDLP.L94_Inst
import ECDLP.L90_BddD
import ECDLP.L94_Wts
import ECDLP.L89_Num
import ECDLP.L85_B_Core

/-!
# L94 / Final: `btE_real` and everything `EdgeCore 200` asks for the `btE` field

* `exSyn_btReal`: `Sy` and `dp <= 40` (the `bb vb db rdb` fields of `ExSyn 200`), and `noRd_btReal` (array 3 unread).
* `clusHyp_btEx`: `ClusHyp 13 gTot sigma0 A gE btE wt` for `wt k = wtB (enum.symm k)` (the field `clh`).
* `bdd_btReal`: `Bdd V sigma A btReal` for `sigma 20 = j` (third conjunct of `bnd`).
* `wt_hrow, wt_hheld, wt_hmax, wt_htot`: the weight fields `hrow hheld hmax htot` for `wt = wtB`.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 ECDLP.L64
  ECDLP.L83 ECDLP.L84 ECDLP.L91 ECDLP.L90 ECDLP.L65 Slot Cst

section generic
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u)

/-- `ClusHyp` for the weight expression: the cluster map `clusM` of L85 is the cumulative-weight map of `wtB`. -/
theorem clusHyp_btEx {σ₀ : ℕ → ℕ} (hu : B ≤ u) (hB20 : B ≤ 20) (hu20 : 20 < u + 10) (hC : Ctx σ₀) :
    ECDLP.L85B.ClusHyp B (L.gTot N0.A) σ₀ A (gEx I) (btEx I Ph 20)
      (fun k => wtB φ N0 w ((L.enum N0.A).symm k)) where
  hB := hB20
  hgE σ hσ := eval_gEx I hu hC hσ
  hbt σ hσ k hk := eval_btEx I Ph hu hC hσ N0.toPar.A_pos (by omega) hk

end generic

section real
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW)

/-- the real weights -/
abbrev wtReal (n ℓ : ℕ) (π : List Bool) (p : ℕ) : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A) → ℕ :=
  fun k => wtB (phiR n ℓ π) (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm k)

theorem clusHyp_btReal {σ₀ : ℕ → ℕ} (hB16 : B ≤ 16) (hB20 : B ≤ 20) (hC : Ctx σ₀) :
    ECDLP.L85B.ClusHyp B ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A) σ₀ A (gEx (instEx (n := n) 16 hB hR))
      (btReal n hB hR) (wtReal n ℓ π p) :=
  clusHyp_btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hB16 hB20 (by norm_num) hC

section bdd
variable {V : ℕ} (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (hs : ∀ σ₀, Ctx σ₀ → 2 ^ σ₀ 0 ≤ V)
  (N : LNum V (Nat.size p))
include hbn hn hs N

/-- **value bound of the real weight expression**: `Bdd V sigma A btReal` for every state with `sigma 20 = j` (a node).
Numeric hypotheses: those of L90 `instBdd_real` (`hbn hn hs N`), the decode numerics `DN`, `8 <= V`, `Wm <= V` (the weight bound; from
`Ub <= V`) and `b h + 1 <= V`. -/
theorem bdd_btReal (len : ℕ) (hlen : Nat.size p + 4 ≤ 4 * len) (hu : B ≤ 16)
    (DN : DecNum V (layOf (sgR n ℓ π)) (NParE (Nat.size p)) (fun _ => wP (Nat.size p))) (h8 : 8 ≤ V)
    (hWm : Wm n len ≤ V) (hS : (NParE (Nat.size p)).b * (NParE (Nat.size p)).h + 1 ≤ V) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ j : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A), σ 20 = j →
      Bdd V σ A (btReal n hB hR) := by
  intro σ₀ hC σ hσ j hj
  refine bdd_btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu hC hσ (instBdd_real hB hR hbn hn hs N) DN h8
    (fun σ₀ hC τ hτ c j h22 h23 => phiBdd_real hB hR hbn hn hs N σ₀ hC τ hτ c j h22 h23)
    (fun q => (wtB_le_Wm (K := 18 * n + 12) (Nat.size p) len (sgR n ℓ π) (cnEquiv n) hlen q).trans hWm)
    (bP_pos _) (Nat.one_le_two_pow) hS (xs := 20) (by norm_num) hj

end bdd

/-- weight fields of `EdgeCore` for `wt = wtB` (real network family) -/
theorem wt_hmax (len : ℕ) (hlen : Nat.size p + 4 ≤ 4 * len) {g : ℕ} (eg : CG (Slot n) (UC (sgR n ℓ π) (cnEquiv n)) (NParE (Nat.size p)).A ≃ Fin g)
    (a : Fin g) : wtB (phiR n ℓ π) (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) (eg.symm a) ≤ Wm n len :=
  wtB_le_Wm (K := 18 * n + 12) (Nat.size p) len (sgR n ℓ π) (cnEquiv n) hlen _

theorem wt_htot (len : ℕ) (hlen : Nat.size p + 4 ≤ 4 * len) {g : ℕ} (eg : CG (Slot n) (UC (sgR n ℓ π) (cnEquiv n)) (NParE (Nat.size p)).A ≃ Fin g) :
    ∑ a : Fin g, wtB (phiR n ℓ π) (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) (eg.symm a) ≤ Ub n len :=
  sum_wtB_le_Ub (K := 18 * n + 12) (Nat.size p) len (sgR n ℓ π) (cnEquiv n) hlen eg

theorem eval_btReal {σ₀ σ : ℕ → ℕ} (hu : B ≤ 16) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
    (j : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A)) (hj : σ 20 = j) :
    Ex.eval σ A (btReal n hB hR) = wtReal n ℓ π p j :=
  eval_btEx (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu hC hσ (NParE (Nat.size p)).toPar.A_pos (by norm_num) hj

variable {m : ℕ} (hm1 : 1 < m) (hu16 : B ≤ 16) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)

/-- **`ExSyn 200` for the REAL network with the REAL `btE`** (L91's `exSyn200_real` with its only open hypothesis `btE` discharged). -/
theorem exSyn200_btReal
    (Kd : Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu16))
    (hfa : Kd.fa.outE = ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39))))
    (hmid : Kd.mid.outE = ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx n 31 59 16) (lEx n 31 59) (rEx n 31 59)))
    (hib : Kd.ib.outE = ECDLP.L79.ibOutIC (u := 16))
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu16))
    (hSw : Sw.srcE = srcE 16 (badE 16 n)) :
    haveI := edge_free_nonempty (w := fun _ => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m
    let P := pexEdge (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu16 hm1 Kd Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE (btReal n hB hR) :=
  exSyn200_real hB hR hu16 hm1 ok Kd hfa hmid hib Sw hSw (btReal n hB hR) (sy_btReal hB hR) (dp_btReal hB hR)

end real
end ECDLP.L94
end
