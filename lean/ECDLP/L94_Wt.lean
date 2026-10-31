import ECDLP.L73_Disp1
import ECDLP.L75_Held

/-!
# L94 / Wt: the node weight `btE` as a closed form by node kind, and its semantics

`btEx I Ph xs` evaluates, in a state with `σ xs = j` (node index), to
`Bw φ q + freeBits N0 q` with `q = enum.symm j`:
* source `(i,s)`: `occ φ i * (b h + 1) + b h` (exact out-degree `occ`, by a double count of `phi`);
* fa `(b h + 1) + A (M+4)`; mid `nc A (M+4) + A (M+4)`; ib `2 A (M+4)`; car `3 (M+4)`.
Depth: the source branch sits OUTSIDE `decodeE` (so only the gate branch pays the 15 decode lets).
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L59 ECDLP.L64 ECDLP.L68
  ECDLP.L73

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι}

/-- the out-degree of the slot in variable `u+16`: `#{(c,k) : k < nc c, phi c k = slot}` -/
def occE (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) : Ex :=
  nsum (u + 91) I.KE (.lett (u + 22) (.var (u + 91)) (nsum (u + 23) I.ncE (ECDLP.L73.eqE Ph.phiE (.var (u + 16)))))

/-- the source branch (index `xs`) -/
def srcBt (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (xs : ℕ) : Ex :=
  .lett (u + 16) (.div (.var xs) I.AE) <| .lett (u + 14) I.bE <| .lett (u + 13) I.hE <|
    .add (.mul (occE I Ph) (.add (.mul (.var (u + 14)) (.var (u + 13))) (.lit 1)))
      (.mul (.var (u + 14)) (.var (u + 13)))

/-- the gate branch, run after `decodeE` -/
def gateBt (u : ℕ) : Ex :=
  .ifLt (.var (u + 21)) (.lit 2)
    (.add (.add (.mul (.var (u + 14)) (.var (u + 13))) (.lit 1)) (.mul (.var (u + 12)) (.add (.var (u + 27)) (.lit 4))))
    (.ifLt (.var (u + 21)) (.lit 3)
      (.add (.mul (.mul (.var (u + 19)) (.var (u + 12))) (.add (.var (u + 27)) (.lit 4)))
        (.mul (.var (u + 12)) (.add (.var (u + 27)) (.lit 4))))
      (.ifLt (.var (u + 21)) (.lit 4)
        (.add (.mul (.var (u + 12)) (.add (.var (u + 27)) (.lit 4))) (.mul (.var (u + 12)) (.add (.var (u + 27)) (.lit 4))))
        (.mul (.lit 3) (.add (.var (u + 27)) (.lit 4)))))

/-- **the weight expression** -/
def btEx (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (xs : ℕ) : Ex :=
  .ifLt (.var xs) (.mul I.nIE I.AE) (srcBt I Ph xs) (decodeE I xs (gateBt u))

/-- the intended weight: shared bits bound + free bits -/
def wtB (φ : ∀ c, ιc c → ι) (N0 : NPar) (w : Fin K → ℕ) (q : CG ι ιc N0.A) : ℕ :=
  Bw (w := w) φ q + freeBits N0 q

variable (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u)
variable {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)

/-- the double count -/
theorem occ_fin (i : ι) :
    occ (ιc := ιc) φ i = ∑ c : Fin K, ∑ k : Fin (L.nc c),
      (if L.eι (φ c ((L.ecc c).symm k)) = L.eι i then 1 else 0) := by
  unfold occ
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Equiv.sum_comp (L.ecc c).symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [L.eι.injective.eq_iff]

include hu hC hσ in
theorem eval_occE (hi : σ (u + 16) = L.eι i₀) :
    Ex.eval σ A (occE I Ph) = occ (ιc := ιc) φ i₀ := by
  rw [occ_fin (L := L)]
  simp only [occE, Ex.eval_nsum, I.hK σ₀ hC σ hσ]
  rw [← Fin.sum_univ_eq_sum_range (fun t => Ex.eval (Function.update σ (u + 91) t) A
    (.lett (u + 22) (.var (u + 91)) (nsum (u + 23) I.ncE (ECDLP.L73.eqE Ph.phiE (.var (u + 16)))))) K]
  refine Finset.sum_congr rfl fun c _ => ?_
  have g1 : Ag B σ₀ (Function.update σ (u + 91) c.val) := hσ.upd (by omega) _
  simp only [Ex.eval]
  set σ1 := Function.update (Function.update σ (u + 91) c.val) (u + 22) c.val with h1
  have g2 : Ag B σ₀ σ1 := g1.upd (by omega) _
  have hc : σ1 (u + 22) = c.val := by simp [h1]
  have hn := I.hnc σ₀ hC σ1 g2 c hc
  rw [Function.update_self]
  rw [Ex.eval_nsum, hn, ← Fin.sum_univ_eq_sum_range (fun k => Ex.eval (Function.update σ1 (u + 23) k) A
    (ECDLP.L73.eqE Ph.phiE (.var (u + 16)))) (L.nc c)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have g3 : Ag B σ₀ (Function.update σ1 (u + 23) k.val) := g2.upd (by omega) _
  rw [ECDLP.L73.eval_eqE]
  have hph := Ph.hphi σ₀ hC _ g3 c ((L.ecc c).symm k) (by simp [Function.update_apply, hc]) (by simp)
  simp only [Ex.eval]
  rw [hph]
  simp [Function.update_apply, h1, hi]
  simp only [Fin.val_inj, L.eι.injective.eq_iff]

include hu hC hσ in
theorem eval_btEx (hAp : 0 < N0.A) {xs : ℕ} (hxs : xs < u + 10) {a : Fin (L.gTot N0.A)} (ha : σ xs = a) :
    Ex.eval σ A (btEx I Ph xs) = wtB φ N0 w ((L.enum N0.A).symm a) := by
  obtain ⟨q, hq, hqa, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ hxs ha (gateBt u)
  rw [hq]
  have hnI := I.hnI σ₀ hC σ hσ
  have hAA := I.hA σ₀ hC σ hσ
  cases q with
  | src i s =>
    have hxq : σ xs = L.eι i * N0.A + s := by rw [ha, ← hqa, Lay.enum_src]
    have hlt : L.eι i * N0.A + s < L.nι * N0.A := by
      have := (L.eι i).2
      have := s.2
      nlinarith
    have hdiv : σ xs / N0.A = L.eι i := by
      rw [hxq, Nat.add_comm, Nat.add_mul_div_right _ _ hAp, Nat.div_eq_of_lt s.2, zero_add]
    have hcond : Ex.eval σ A (.ifLt (.var xs) (.mul I.nIE I.AE) (srcBt I Ph xs) (decodeE I xs (gateBt u))) =
        Ex.eval σ A (srcBt I Ph xs) := by
      simp only [Ex.eval, hnI, hAA, hxq, if_pos hlt]
    unfold btEx
    rw [hcond]
    unfold srcBt
    rw [eval_lett']
    have e0 : Ex.eval σ A (.div (.var xs) I.AE) = L.eι i := by simp only [Ex.eval, hAA]; exact hdiv
    rw [e0]
    set σ1 := Function.update σ (u + 16) (L.eι i) with h1
    have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
    rw [eval_lett', I.hbv σ₀ hC σ1 g1]
    set σ2 := Function.update σ1 (u + 14) N0.b with h2
    have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
    rw [eval_lett', show Ex.eval σ2 A I.hE = N0.h from I.hh σ₀ hC σ2 g2]
    set σ3 := Function.update σ2 (u + 13) N0.h with h3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have e16 : σ3 (u + 16) = L.eι i := by simp [h3, h2, h1, Function.update_apply]
    have e14 : σ3 (u + 14) = N0.b := by simp [h3, h2, h1, Function.update_apply]
    have e13 : σ3 (u + 13) = N0.h := by simp [h3]
    simp only [Ex.eval]
    rw [eval_occE I Ph hu hC g3 e16, e14, e13]
    simp [wtB, Bw, freeBits, eS]
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    have hxq : σ xs = L.nι * N0.A + (L.off N0.A c + (L.gateE N0.A c g' : ℕ)) := by rw [ha, ← hqa, Lay.enum_gt]
    have hge : ¬ σ xs < L.nι * N0.A := by rw [hxq]; omega
    have hcard : Fintype.card (ιc c) = L.nc c := by
      rw [Fintype.card_congr (L.ecc c), Fintype.card_fin]
    have hcond : Ex.eval σ A (btEx I Ph xs) = Ex.eval σ A (decodeE I xs (gateBt u)) := by
      simp only [btEx, Ex.eval, hnI, hAA, if_neg hge]
    rw [hcond, h]
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      simp only [gateBt, Ex.eval, k1, p12, p13, p14, p27]
      simp [wtB, Bw, freeBits, eS, eM]
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      simp only [gateBt, Ex.eval, k1, p12, p13, p14, p27, p19]
      simp [wtB, Bw, freeBits, eS, eM, hcard]
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      simp only [gateBt, Ex.eval, k1, p12, p13, p14, p27]
      simp [wtB, Bw, freeBits, eS, eM]
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      simp only [gateBt, Ex.eval, k1, p12, p13, p14, p27]
      simp [wtB, Bw, freeBits, eS, eM]
      ring

end
end ECDLP.L94
end
