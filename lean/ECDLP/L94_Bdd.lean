import ECDLP.L94_Wt
import ECDLP.L84_BddNode

/-!
# L94 / Bdd: value bounds of the weight expression `btEx` (`Bdd V σ A btE`, the third conjunct of `EdgeCore.bnd`)

Hypotheses (all generic, discharged by the callers): `InstBdd V I`, `DecNum V L N0 w`, the bound of `phiE` at states holding an
identity and a rank, and `wtB <= V` for every node (the weight itself is below `Wm r n <= V`).
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L59 ECDLP.L64 ECDLP.L68
  ECDLP.L73 ECDLP.L84

theorem bdd_eqE {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {a b : Ex} (hV1 : 1 ≤ V) (ha : Bdd V σ A a) (hb : Bdd V σ A b) :
    Bdd V σ A (ECDLP.L73.eqE a b) := by
  simp only [ECDLP.L73.eqE, Bdd]
  refine ⟨ha, hb, ?_⟩
  by_cases h : eval σ A a < eval σ A b
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]
    refine ⟨hb, ha, ?_⟩
    by_cases h2 : eval σ A b < eval σ A a
    · rw [if_pos h2]; exact Nat.zero_le _
    · rw [if_neg h2]; exact hV1

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι} {V : ℕ}
variable (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u)

variable {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)

include hu hC hσ in
theorem bdd_occE (IB : InstBdd V I)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ : ℕ → ℕ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c → τ (u + 23) = L.ecc c j →
      Bdd V τ A Ph.phiE)
    (hV1 : 1 ≤ V) (hK : K ≤ V) {i₀ : ι} (hi : σ (u + 16) = L.eι i₀) (hiV : σ (u + 16) ≤ V)
    (hocc : occ (ιc := ιc) φ i₀ ≤ V) : Bdd V σ A (occE I Ph) := by
  have htot := eval_occE I Ph hu hC hσ hi
  have hKe := I.hK σ₀ hC σ hσ
  unfold occE
  refine B_nsum (IB.K' σ₀ hC σ hσ) (fun j hj => ?_) ?_
  · rw [hKe] at hj
    have g1 : Ag B σ₀ (Function.update σ (u + 91) j) := hσ.upd (by omega) _
    refine ⟨?_, ?_⟩
    · show (Function.update σ (u + 91) j) (u + 91) ≤ V
      simp; omega
    · set σ1 := Function.update (Function.update σ (u + 91) j) (u + 22)
        (Ex.eval (Function.update σ (u + 91) j) A (.var (u + 91))) with h1
      have g2 : Ag B σ₀ σ1 := g1.upd (by omega) _
      have hc : σ1 (u + 22) = (⟨j, hj⟩ : Fin K) := by simp [h1, Ex.eval]
      have hn := I.hnc σ₀ hC σ1 g2 ⟨j, hj⟩ hc
      have hnB := IB.nc σ₀ hC σ1 g2 ⟨j, hj⟩ hc
      refine B_nsum hnB (fun k hk => ?_) ?_
      · rw [hn] at hk
        have g3 : Ag B σ₀ (Function.update σ1 (u + 23) k) := g2.upd (by omega) _
        have hph := hphiB σ₀ hC _ g3 ⟨j, hj⟩ ((L.ecc ⟨j, hj⟩).symm ⟨k, hk⟩) (by simp [Function.update_apply, hc])
          (by simp)
        refine bdd_eqE hV1 hph ?_
        show (Function.update σ1 (u + 23) k) (u + 16) ≤ V
        have : (Function.update σ1 (u + 23) k) (u + 16) = σ (u + 16) := by
          simp [Function.update_apply, h1]
        rw [this]; exact hiV
      · have hle : ∑ k ∈ range (Ex.eval σ1 A I.ncE), Ex.eval (Function.update σ1 (u + 23) k) A
            (ECDLP.L73.eqE Ph.phiE (.var (u + 16))) ≤ Ex.eval σ1 A I.ncE := by
          calc _ ≤ ∑ k ∈ range (Ex.eval σ1 A I.ncE), 1 := by
                refine sum_le_sum fun k _ => ?_
                rw [ECDLP.L73.eval_eqE]; split_ifs <;> omega
            _ = _ := by simp
        exact le_trans hle (le_of_B hnB)
  · rw [← Ex.eval_nsum]
    show Ex.eval σ A (occE I Ph) ≤ V
    rw [htot]; exact hocc

include hu hC hσ in
theorem bdd_srcBt (IB : InstBdd V I) (DN : DecNum V L N0 w)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ : ℕ → ℕ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c → τ (u + 23) = L.ecc c j →
      Bdd V τ A Ph.phiE)
    (hW : ∀ q, wtB φ N0 w q ≤ V) (hb1 : 1 ≤ N0.b) (hh1 : 1 ≤ N0.h) (hS : N0.b * N0.h + 1 ≤ V) {xs : ℕ} (hxsV : σ xs ≤ V) {i : ι} {s : Fin N0.A} (hxq : σ xs = L.eι i * N0.A + s) :
    Bdd V σ A (srcBt I Ph xs) := by
  have hAp : 0 < N0.A := N0.toPar.A_pos
  have hAA := I.hA σ₀ hC σ hσ
  have hdiv : σ xs / N0.A = L.eι i := by
    rw [hxq, Nat.add_comm, Nat.add_mul_div_right _ _ hAp, Nat.div_eq_of_lt s.2, zero_add]
  have e0 : Ex.eval σ A (.div (.var xs) I.AE) = L.eι i := by simp only [Ex.eval, hAA]; exact hdiv
  have hw := hW (CG.src i s)
  simp only [wtB, Bw, freeBits, eS] at hw
  have hocc : occ (ιc := ιc) φ i ≤ V := le_trans (by nlinarith [Nat.zero_le (N0.b * N0.h)]) hw
  have hbh : N0.b * N0.h ≤ V := by omega
  unfold srcBt
  refine ⟨⟨B_var hxsV, IB.A' σ₀ hC σ hσ⟩, ?_⟩
  rw [e0]
  set σ1 := Function.update σ (u + 16) (L.eι i) with h1
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  refine ⟨IB.b' σ₀ hC σ1 g1, ?_⟩
  rw [I.hbv σ₀ hC σ1 g1]
  set σ2 := Function.update σ1 (u + 14) N0.b with h2
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  refine ⟨IB.h' σ₀ hC σ2 g2, ?_⟩
  rw [I.hh σ₀ hC σ2 g2]
  set σ3 := Function.update σ2 (u + 13) N0.h with h3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have e16 : σ3 (u + 16) = L.eι i := by simp [h3, h2, h1, Function.update_apply]
  have e14 : σ3 (u + 14) = N0.b := by simp [h3, h2, h1, Function.update_apply]
  have e13 : σ3 (u + 13) = N0.h := by simp [h3]
  have hoccB := bdd_occE I Ph hu hC g3 IB hphiB DN.hV DN.hK e16 (by rw [e16]; have := (L.eι i).2; have := DN.hG; unfold Lay.gTot at this; nlinarith [hAp]) hocc
  have hoccE := eval_occE I Ph hu hC g3 e16
  have hb : σ3 (u + 14) ≤ V := by rw [e14]; exact le_trans (Nat.le_mul_of_pos_right _ hh1) hbh
  have hh : σ3 (u + 13) ≤ V := by rw [e13]; exact le_trans (Nat.le_mul_of_pos_left _ hb1) hbh
  have hbhB : Bdd V σ3 A (.mul (.var (u + 14)) (.var (u + 13))) := by
    refine ⟨hb, hh, ?_⟩
    simp only [Ex.eval, e14, e13]; exact hbh
  have hbh1B : Bdd V σ3 A (.add (.mul (.var (u + 14)) (.var (u + 13))) (.lit 1)) := by
    refine ⟨hbhB, DN.hV, ?_⟩
    simp only [Ex.eval, e14, e13]; omega
  refine ⟨⟨hoccB, hbh1B, ?_⟩, hbhB, ?_⟩
  · simp only [Ex.eval, e14, e13]; rw [hoccE]; omega
  · simp only [Ex.eval, e14, e13]; rw [hoccE]; omega

include hu hC hσ in
theorem bdd_btEx (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ : ℕ → ℕ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c → τ (u + 23) = L.ecc c j →
      Bdd V τ A Ph.phiE)
    (hW : ∀ q, wtB φ N0 w q ≤ V) (hb1 : 1 ≤ N0.b) (hh1 : 1 ≤ N0.h) (hS : N0.b * N0.h + 1 ≤ V)
    {xs : ℕ} (hxs : xs < u + 10) {a : Fin (L.gTot N0.A)} (ha : σ xs = a) :
    Bdd V σ A (btEx I Ph xs) := by
  have hAp : 0 < N0.A := N0.toPar.A_pos
  have hxsV : σ xs ≤ V := by rw [ha]; exact le_trans a.2.le DN.hG
  have hnI := I.hnI σ₀ hC σ hσ
  have hAA := I.hA σ₀ hC σ hσ
  have hAV : N0.A ≤ V := by rw [← hAA]; exact le_of_B (IB.A' σ₀ hC σ hσ)
  have hnIA : L.nι * N0.A ≤ V := by have := DN.hG; unfold Lay.gTot at this; omega
  obtain ⟨q, hq, hqa⟩ : ∃ q, (L.enum N0.A).symm a = q ∧ L.enum N0.A q = a := ⟨_, rfl, by simp⟩
  have hB1 : Bdd V σ A (.mul I.nIE I.AE) := ⟨IB.nI σ₀ hC σ hσ, IB.A' σ₀ hC σ hσ, by rw [hnI, hAA]; exact hnIA⟩
  unfold btEx
  refine ⟨B_var hxsV, hB1, ?_⟩
  cases q with
  | src i s =>
    have hxq : σ xs = L.eι i * N0.A + s := by rw [ha, ← hqa, Lay.enum_src]
    have hlt : L.eι i * N0.A + s < L.nι * N0.A := by
      have := (L.eι i).2
      have := s.2
      nlinarith
    have hc : Ex.eval σ A (.var xs) < Ex.eval σ A (.mul I.nIE I.AE) := by
      simp only [Ex.eval, hnI, hAA, hxq]; exact hlt
    rw [if_pos hc]
    exact bdd_srcBt I Ph hu hC hσ IB DN hphiB hW hb1 hh1 hS hxsV hxq
  | gt c g' =>
    have hxq : σ xs = L.nι * N0.A + (L.off N0.A c + (L.gateE N0.A c g' : ℕ)) := by rw [ha, ← hqa, Lay.enum_gt]
    have hc : ¬ Ex.eval σ A (.var xs) < Ex.eval σ A (.mul I.nIE I.AE) := by
      simp only [Ex.eval, hnI, hAA, hxq]; omega
    rw [if_neg hc]
    refine bdd_decodeE I IB DN h8 hu hC hσ hxs (.gt c g') (by rw [ha, ← hqa]) hxsV (fun σ' hD => ?_)
    obtain ⟨gA, agr, k21, j16, s17, hp, hg⟩ := hD
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    have hw := hW (CG.gt c g')
    have hcard : Fintype.card (ιc c) = L.nc c := by
      rw [Fintype.card_congr (L.ecc c), Fintype.card_fin]
    have hbh1 : N0.b ≤ N0.b * N0.h := Nat.le_mul_of_pos_right _ hh1
    have hbh2 : N0.h ≤ N0.b * N0.h := Nat.le_mul_of_pos_left _ hb1
    have hP1 : (NP N0 w c).M + 4 ≤ N0.A * ((NP N0 w c).M + 4) := Nat.le_mul_of_pos_left _ hAp
    have hP2 : N0.A ≤ N0.A * ((NP N0 w c).M + 4) := Nat.le_mul_of_pos_right _ (by omega)
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      simp only [wtB, Bw, freeBits, eS, eM] at hw
      simp only [gateBt, Bdd, Ex.eval, k1, p12, p13, p14, p27]
      generalize N0.A * ((NP N0 w c).M + 4) = P at *
      generalize N0.b * N0.h = Z at *
      simp
      omega
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      simp only [wtB, Bw, freeBits, eS, eM, hcard] at hw
      simp only [gateBt, Bdd, Ex.eval, k1, p12, p13, p14, p27, p19]
      have hq1 : L.nc c ≤ L.nc c * N0.A := Nat.le_mul_of_pos_right _ hAp
      have hq3 : L.nc c * N0.A ≤ L.nc c * N0.A * ((NP N0 w c).M + 4) := Nat.le_mul_of_pos_right _ (by omega)
      generalize N0.A * ((NP N0 w c).M + 4) = P at *
      generalize L.nc c * N0.A * ((NP N0 w c).M + 4) = Q at *
      generalize L.nc c * N0.A = R at *
      simp
      omega
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      simp only [wtB, Bw, freeBits, eS, eM] at hw
      simp only [gateBt, Bdd, Ex.eval, k1, p12, p13, p14, p27]
      generalize N0.A * ((NP N0 w c).M + 4) = P at *
      simp
      omega
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      simp only [wtB, Bw, freeBits, eS, eM] at hw
      simp only [gateBt, Bdd, Ex.eval, k1, p12, p13, p14, p27]
      simp
      omega

end
end ECDLP.L94
end
