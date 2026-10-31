import ECDLP.L73_Asm
import ECDLP.L69_Bdd

/-!
# L84 / BddDec: value bounds of the gate-index decode (`decodeE`) and of the offset sums

`InstBdd V I`: the instance expressions are bounded by `V` (in every `Ag`-state; `ncE`, `MeE` when slot `u+22` holds an identity).
`DecNum`: the numeric requirements (`gTot <= V`, `K <= V`, `2^M_c <= V`).
`bdd_offE`: `offE I t` is bounded when `t <= K`.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L84
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ}

/-- the instance expressions are bounded by `V` -/
structure InstBdd (V : ℕ) (I : InstEx L N0 w B Ctx A u) : Prop where
  nI : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.nIE
  K' : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.KE
  A' : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.AE
  h' : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.hE
  pb : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.pbE
  b' : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A I.bE
  nc : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ c : Fin K, σ (u + 22) = c → Bdd V σ A I.ncE
  Me : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ c : Fin K, σ (u + 22) = c → Bdd V σ A I.MeE

/-- numeric requirements of the decode -/
structure DecNum (V : ℕ) (L : Lay ι ιc) (N0 : NPar) (w : Fin K → ℕ) : Prop where
  hV : 1 ≤ V
  hG : L.gTot N0.A ≤ V
  hK : K ≤ V
  hK0 : 0 < K
  hM : ∀ c : Fin K, 2 ^ (NP N0 w c).M ≤ V

theorem blkN_le_off (j : ℕ) (hj : j < K) : L.blkN N0.A j ≤ L.off N0.A K := by
  unfold Lay.off
  exact Finset.single_le_sum (f := L.blkN N0.A) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)

theorem off_le_V {V : ℕ} (DN : DecNum V L N0 w) (n : ℕ) (hn : n ≤ K) : L.off N0.A n ≤ V := by
  have := L.off_mono N0.A hn
  have h2 := DN.hG
  unfold Lay.gTot at h2
  omega

theorem blkN_le_V {V : ℕ} (DN : DecNum V L N0 w) (j : ℕ) (hj : j < K) : L.blkN N0.A j ≤ V :=
  le_trans (blkN_le_off j hj) (off_le_V DN K le_rfl)

theorem bdd_blkLoop {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {j : ℕ} (hj : j < K) (hA : σ (u + 12) = N0.A) :
    Bdd V (Function.update σ (u + 91) j) A (blkLoop I) := by
  have g1 : Ag B σ₀ (Function.update σ (u + 91) j) := hσ.upd (by omega) _
  have g2 : Ag B σ₀ (Function.update (Function.update σ (u + 91) j) (u + 22) j) := g1.upd (by omega) _
  have hb := IB.nc σ₀ hC _ g2 ⟨j, hj⟩ (by simp)
  have hnc := I.hnc σ₀ hC _ g2 ⟨j, hj⟩ (by simp)
  have hbl := blkN_le_V DN j hj
  have hA12 : (Function.update σ (u + 91) j) (u + 12) = N0.A := by rw [Function.update_of_ne (by omega)]; exact hA
  have hA22 : (Function.update (Function.update σ (u + 91) j) (u + 22) j) (u + 12) = N0.A := by
    rw [Function.update_of_ne (by omega)]; exact hA12
  have hj91 : (Function.update σ (u + 91) j) (u + 91) = j := by simp
  have hjV : j ≤ V := by have := DN.hK; omega
  unfold Lay.blkN Lay.ncN at hbl
  simp only [hj, dite_true] at hbl
  simp only [blkLoop, Bdd, Ex.eval, hnc, hA12, hj91]
  refine ⟨⟨⟨hjV, hb⟩, ?_, ?_⟩, ⟨?_, ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩, ?_⟩ <;> omega


theorem bdd_offE {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {t : Ex} (ht : Bdd V σ A t) {n : ℕ}
    (hn : Ex.eval σ A t = n) (hnK : n ≤ K) (hA : σ (u + 12) = N0.A) : Bdd V σ A (offE I t) := by
  refine B_nsum ht (fun j hj => bdd_blkLoop I IB DN hu hC hσ (by omega) hA) ?_
  rw [hn]
  have : ∑ i ∈ range n, Ex.eval (Function.update σ (u + 91) i) A (blkLoop I) = L.off N0.A n := by
    unfold Lay.off
    exact sum_congr rfl fun i hi => eval_blkLoop I hu hC hσ (by have := mem_range.1 hi; omega) hA
  rw [this]
  exact off_le_V DN n hnK

theorem cnt_pos_blk (y : ℕ) (hA : 0 < N0.A) (t : ℕ) : 0 < L.off N0.A (t + 1) := by
  rw [Lay.off_succ]
  have : 0 < L.blkN N0.A t := by unfold Lay.blkN; have := Nat.mul_pos hA hA; omega
  omega

theorem cnt_zero (hA : 0 < N0.A) : L.cnt N0.A 0 = 0 := by
  unfold Lay.cnt
  exact Finset.sum_eq_zero fun t _ => by rw [if_pos (cnt_pos_blk (L := L) 0 hA t)]

theorem cnt_lt_K (hA : 0 < N0.A) (hK0 : 0 < K) (q : CG ι ιc N0.A) :
    L.cnt N0.A ((L.enum N0.A q : ℕ) - L.nι * N0.A) < K := by
  cases q with
  | src i s =>
    rw [Lay.enum_src]
    have hlt : L.eι i * N0.A + s < L.nι * N0.A := by
      have := (L.eι i).2
      have := s.2
      nlinarith
    rw [Nat.sub_eq_zero_of_le hlt.le, cnt_zero hA]; exact hK0
  | gt c g =>
    rw [Lay.enum_gt]
    have hge := (L.gateE N0.A c g).2
    have h : L.nι * N0.A + (L.off N0.A c + (L.gateE N0.A c g : ℕ)) - L.nι * N0.A = L.off N0.A c + (L.gateE N0.A c g : ℕ) := by
      omega
    rw [h, L.cnt_eq N0.A c.2 (by omega) ?_]
    · exact c.2
    · rw [Lay.off_lt_succ]; unfold Lay.blk at hge ⊢; omega

/-- the information `eval_decodeE` gives about the final decode state -/
def DInfo (σ₀ : ℕ → ℕ) (q : CG ι ιc N0.A) (σ σ' : ℕ → ℕ) : Prop :=
  Ag B σ₀ σ' ∧ (∀ y, (y < u + 10 ∨ u + 28 ≤ y) → σ' y = σ y) ∧
  σ' (u + 21) = kc (kindOf q) ∧ σ' (u + 16) = (coordOf L q).1 ∧ σ' (u + 17) = (coordOf L q).2 ∧
  (∀ c, idOf q = some c → σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ' (u + 12) = N0.A ∧
        σ' (u + 13) = N0.h ∧ σ' (u + 15) = c.val ∧ σ' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
        σ' (u + 19) = L.nc c ∧ σ' (u + 27) = (NP N0 w c).M ∧ σ' (u + 14) = N0.b) ∧
  (σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 12) = N0.A ∧ σ' (u + 13) = N0.h ∧ σ' (u + 14) = N0.b)

theorem bdd_kcodeE {V : ℕ} (I : InstEx L N0 w B Ctx A u) {σ : ℕ → ℕ} {xs n0 : ℕ} (hx : σ xs ≤ V) (h25 : σ (u + 25) ≤ V)
    (h12 : σ (u + 12) = N0.A) (hn0 : n0 ≤ V) (h19 : σ (u + 19) = n0) (hnI : Bdd V σ A I.nIE) (hnIv : Ex.eval σ A I.nIE = L.nι)
    (h1 : L.nι * N0.A ≤ V) (h2 : n0 * N0.A + (N0.A + N0.A) ≤ V) (hAV : N0.A ≤ V) (h8 : 8 ≤ V) :
    Bdd V σ A (kcodeE I xs) := by
  simp only [kcodeE, Bdd, Ex.eval, h12, h19, hnIv, hnI]
  split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega

theorem bdd_djE {V : ℕ} (I : InstEx L N0 w B Ctx A u) {σ : ℕ → ℕ} {xs n0 : ℕ} (hx : σ xs ≤ V) (h25 : σ (u + 25) ≤ V)
    (h12 : σ (u + 12) = N0.A) (hn0 : n0 ≤ V) (h19 : σ (u + 19) = n0) (hnI : Bdd V σ A I.nIE) (hnIv : Ex.eval σ A I.nIE = L.nι)
    (h1 : L.nι * N0.A ≤ V) (h2 : n0 * N0.A + (N0.A + N0.A) ≤ V) (hAV : N0.A ≤ V) (h8 : 8 ≤ V) :
    Bdd V σ A (djE I xs) := by
  simp only [djE, Bdd, Ex.eval, h12, h19, hnIv, hnI]
  split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega

theorem bdd_dsE {V : ℕ} (I : InstEx L N0 w B Ctx A u) {σ : ℕ → ℕ} {xs n0 : ℕ} (hx : σ xs ≤ V) (h25 : σ (u + 25) ≤ V)
    (h12 : σ (u + 12) = N0.A) (hn0 : n0 ≤ V) (h19 : σ (u + 19) = n0) (hnI : Bdd V σ A I.nIE) (hnIv : Ex.eval σ A I.nIE = L.nι)
    (h1 : L.nι * N0.A ≤ V) (h2 : n0 * N0.A + (N0.A + N0.A) ≤ V) (hAV : N0.A ≤ V) (h8 : 8 ≤ V) :
    Bdd V σ A (dsE I xs) := by
  simp only [dsE, Bdd, Ex.eval, h12, h19, hnIv, hnI]
  split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega

set_option maxHeartbeats 3200000 in
/-- **Value bounds of the gate-index decode.**  If the body is bounded in every state satisfying the decode information
`DInfo`, then `decodeE I xs body` is bounded by `V`. -/
theorem bdd_decodeE {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {xs : ℕ} (hxs : xs < u + 10) (q : CG ι ιc N0.A)
    (hq : σ xs = L.enum N0.A q) (hxsV : σ xs ≤ V) {body : Ex}
    (hbody : ∀ σ', DInfo (B := B) (L := L) (N0 := N0) (w := w) (u := u) σ₀ q σ σ' → Bdd V σ' A body) :
    Bdd V σ A (decodeE I xs body) := by
  have key : ∀ y, ∃ σ', DInfo (B := B) (L := L) (N0 := N0) (w := w) (u := u) σ₀ q σ σ' ∧
      Ex.eval σ A (decodeE I xs (.var y)) = σ' y := fun y => by
    obtain ⟨σ', h, g, pres, k21, j16, s17, hp, hg⟩ := eval_decodeE I hu hC hσ hxs (.var y) q hq
    exact ⟨σ', ⟨g, pres, k21, j16, s17, hp, hg⟩, by rw [h]; rfl⟩
  have hA := I.hA σ₀ hC σ hσ
  have hAV : N0.A ≤ V := by rw [← hA]; exact le_of_B (IB.A' σ₀ hC σ hσ)
  have hA1 : 0 < N0.A := N0.toPar.A_pos
  have hnι : L.nι * N0.A ≤ V := by
    have := DN.hG; unfold Lay.gTot at this; omega
  unfold decodeE
  refine ⟨IB.A' σ₀ hC σ hσ, ?_⟩
  obtain ⟨σ1, h1⟩ : ∃ σ1 : ℕ → ℕ, σ1 = Function.update σ (u + 12) (Ex.eval σ A I.AE) := ⟨_, rfl⟩
  rw [← h1]
  have g1 : Ag B σ₀ σ1 := by rw [h1]; exact hσ.upd (by omega) _
  refine ⟨IB.h' σ₀ hC σ1 g1, ?_⟩
  obtain ⟨σ2, h2⟩ : ∃ σ2 : ℕ → ℕ, σ2 = Function.update σ1 (u + 13) (Ex.eval σ1 A I.hE) := ⟨_, rfl⟩
  rw [← h2]
  have g2 : Ag B σ₀ σ2 := by rw [h2]; exact g1.upd (by omega) _
  refine ⟨IB.pb σ₀ hC σ2 g2, ?_⟩
  obtain ⟨σ3, h3⟩ : ∃ σ3 : ℕ → ℕ, σ3 = Function.update σ2 (u + 10) (Ex.eval σ2 A I.pbE) := ⟨_, rfl⟩
  rw [← h3]
  have g3 : Ag B σ₀ σ3 := by rw [h3]; exact g2.upd (by omega) _
  have a3 : σ3 (u + 12) = N0.A := by simp [h3, h2, h1, Function.update_apply, hA]
  have x3 : σ3 xs = σ xs := by simp [h3, h2, h1, Function.update_apply, show xs ≠ u + 10 by omega,
    show xs ≠ u + 12 by omega, show xs ≠ u + 13 by omega]
  have nI3 := I.hnI σ₀ hC σ3 g3
  have e4 : Ex.eval σ3 A (.sub (.var xs) (.mul I.nIE (.var (u + 12)))) = σ xs - L.nι * N0.A := by
    simp only [Ex.eval, nI3, a3, x3]
  refine ⟨⟨by show σ3 xs ≤ V; rw [x3]; exact hxsV, IB.nI σ₀ hC σ3 g3, by show σ3 (u + 12) ≤ V; rw [a3]; exact hAV,
    by simp only [nI3, Ex.eval, a3]; exact hnι⟩, ?_⟩
  obtain ⟨σ4, h4⟩ : ∃ σ4 : ℕ → ℕ, σ4 = Function.update σ3 (u + 24) (Ex.eval σ3 A (.sub (.var xs) (.mul I.nIE (.var (u + 12))))) := ⟨_, rfl⟩
  rw [← h4]
  have g4 : Ag B σ₀ σ4 := by rw [h4]; exact g3.upd (by omega) _
  have a4 : σ4 (u + 12) = N0.A := by simp [h4, a3, Function.update_apply]
  have y4 : σ4 (u + 24) = σ xs - L.nι * N0.A := by simp [h4, e4]
  have hK4 := I.hK σ₀ hC σ4 g4
  have hc0K : L.cnt N0.A (σ xs - L.nι * N0.A) < K := by rw [hq]; exact cnt_lt_K hA1 DN.hK0 q
  have e5 : Ex.eval σ4 A (nsum (u + 91) I.KE (.ifLt (.var (u + 24)) (offE I (.add (.var (u + 91)) (.lit 1))) (.lit 0) (.lit 1)))
      = L.cnt N0.A (σ xs - L.nι * N0.A) := by
    rw [eval_nsum, hK4, Lay.cnt]
    refine sum_congr rfl fun t ht => ?_
    have ht' := mem_range.1 ht
    have gt4 : Ag B σ₀ (Function.update σ4 (u + 91) t) := g4.upd (by omega) _
    simp only [Ex.eval]
    rw [eval_offE I hu hC gt4 (n := t + 1) (by simp [Ex.eval]) (by omega) (by simp [Function.update_apply, a4])]
    simp [Function.update_apply, y4]
  refine ⟨?_, ?_⟩
  · refine B_nsum' (c := 1) (IB.K' σ₀ hC σ4 g4) (fun j hj => ?_) (by rw [hK4]; have := DN.hK; omega)
    have gj : Ag B σ₀ (Function.update σ4 (u + 91) j) := g4.upd (by omega) _
    rw [hK4] at hj
    have hjV : j + 1 ≤ V := by have := DN.hK; omega
    have bt : Bdd V (Function.update σ4 (u + 91) j) A (Ex.add (.var (u + 91)) (.lit 1)) := by
      refine ⟨?_, ?_, ?_⟩
      · show (Function.update σ4 (u + 91) j) (u + 91) ≤ V
        simp; omega
      · show 1 ≤ V; exact DN.hV
      · simp only [Ex.eval]; simp; omega
    have bo := bdd_offE I IB DN hu hC gj bt (n := j + 1) (by simp [Ex.eval]) (by omega)
      (by simp [Function.update_apply, a4])
    refine ⟨⟨?_, bo, ?_⟩, ?_⟩
    · show (Function.update σ4 (u + 91) j) (u + 24) ≤ V
      simp [Function.update_apply, y4]
      have := Nat.sub_le (σ xs) (L.nι * N0.A); omega
    · split_ifs
      · exact Nat.zero_le V
      · exact DN.hV
    · exact SB.ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])
  · set c0 := L.cnt N0.A (σ xs - L.nι * N0.A) with hc0
    obtain ⟨σ5, h5⟩ : ∃ σ5 : ℕ → ℕ, σ5 = Function.update σ4 (u + 15) (Ex.eval σ4 A (nsum (u + 91) I.KE (.ifLt (.var (u + 24)) (offE I (.add (.var (u + 91)) (.lit 1))) (.lit 0) (.lit 1)))) := ⟨_, rfl⟩
    rw [← h5]
    have g5 : Ag B σ₀ σ5 := by rw [h5]; exact g4.upd (by omega) _
    have c5 : σ5 (u + 15) = c0 := by simp [h5, e5]
    have hc0V : c0 ≤ V := by have := DN.hK; omega
    refine ⟨show σ5 (u + 15) ≤ V by rw [c5]; exact hc0V, ?_⟩
    obtain ⟨σ6, h6⟩ : ∃ σ6 : ℕ → ℕ, σ6 = Function.update σ5 (u + 22) (Ex.eval σ5 A (.var (u + 15))) := ⟨_, rfl⟩
    rw [← h6]
    have g6 : Ag B σ₀ σ6 := by rw [h6]; exact g5.upd (by omega) _
    have c6 : σ6 (u + 22) = c0 := by simp [h6, Ex.eval, c5]
    have a6 : σ6 (u + 12) = N0.A := by simp [h6, h5, a4, Function.update_apply]
    have hcc : (⟨c0, hc0K⟩ : Fin K).val = c0 := rfl
    refine ⟨IB.nc σ₀ hC σ6 g6 ⟨c0, hc0K⟩ c6, ?_⟩
    have hnc := I.hnc σ₀ hC σ6 g6 ⟨c0, hc0K⟩ c6
    set nc0 := Ex.eval σ6 A I.ncE with hnc0
    obtain ⟨σ7, h7⟩ : ∃ σ7 : ℕ → ℕ, σ7 = Function.update σ6 (u + 19) nc0 := ⟨_, rfl⟩
    rw [← h7]
    have g7 : Ag B σ₀ σ7 := by rw [h7]; exact g6.upd (by omega) _
    have c7 : σ7 (u + 22) = c0 := by simp [h7, h6, Ex.eval, c5]
    have a7 : σ7 (u + 12) = N0.A := by simp [h7, a6, Function.update_apply]
    refine ⟨IB.Me σ₀ hC σ7 g7 ⟨c0, hc0K⟩ c7, ?_⟩
    have hMe := I.hMe σ₀ hC σ7 g7 ⟨c0, hc0K⟩ c7
    set Me0 := Ex.eval σ7 A I.MeE with hMe0
    obtain ⟨σ8, h8'⟩ : ∃ σ8 : ℕ → ℕ, σ8 = Function.update σ7 (u + 27) Me0 := ⟨_, rfl⟩
    rw [← h8']
    have g8 : Ag B σ₀ σ8 := by rw [h8']; exact g7.upd (by omega) _
    have m8 : σ8 (u + 27) = Me0 := by simp [h8']
    have hMeV : Me0 ≤ V := le_of_B (IB.Me σ₀ hC σ7 g7 ⟨c0, hc0K⟩ c7)
    have hpowV := DN.hM ⟨c0, hc0K⟩
    have e9 : Ex.eval σ8 A (nprod (u + 91) (.var (u + 27)) (.lit 2)) = 2 ^ Me0 := by
      rw [eval_nprod]
      simp only [Ex.eval]
      rw [m8, pp_congr (f' := fun _ => 2) (fun i _ => by simp [Function.update_apply]), pp_const]
    refine ⟨?_, ?_⟩
    · refine B_nprodV (show Bdd V σ8 A (Ex.var (u + 27)) by show σ8 (u + 27) ≤ V; rw [m8]; exact hMeV)
        (fun j hj => show (2 : ℕ) ≤ V by omega) (fun j hj => ?_)
      have hj' : j ≤ Me0 := by
        have : Ex.eval σ8 A (Ex.var (u + 27)) = Me0 := m8
        omega
      show pp (fun _ => 2) j ≤ V
      rw [pp_const]
      rw [hMe] at hj'
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hj') hpowV
    · obtain ⟨σ9, h9⟩ : ∃ σ9 : ℕ → ℕ, σ9 = Function.update σ8 (u + 11) (Ex.eval σ8 A (nprod (u + 91) (.var (u + 27)) (.lit 2))) := ⟨_, rfl⟩
      rw [← h9]
      have g9 : Ag B σ₀ σ9 := by rw [h9]; exact g8.upd (by omega) _
      have a9 : σ9 (u + 12) = N0.A := by simp [h9, h8', a7, Function.update_apply]
      have c9 : σ9 (u + 15) = c0 := by simp [h9, h8', h7, h6, Function.update_apply, Ex.eval, c5]
      have hoff : L.nι * N0.A + L.off N0.A c0 ≤ V := by
        have := DN.hG; unfold Lay.gTot at this
        have := L.off_mono N0.A (show c0 ≤ K by omega); omega
      have hvc : Bdd V σ9 A (Ex.var (u + 15)) := by show σ9 (u + 15) ≤ V; rw [c9]; exact hc0V
      have e10 : Ex.eval σ9 A (.add (.mul I.nIE (.var (u + 12))) (offE I (.var (u + 15)))) =
          L.nι * N0.A + L.off N0.A c0 := by
        simp only [Ex.eval, I.hnI σ₀ hC σ9 g9, a9]
        rw [eval_offE I hu hC g9 (n := c0) (by simp [Ex.eval, c9]) (by omega) a9]
      refine ⟨⟨⟨IB.nI σ₀ hC σ9 g9, by show σ9 (u + 12) ≤ V; rw [a9]; exact hAV,
        by simp only [I.hnI σ₀ hC σ9 g9, Ex.eval, a9]; exact hnι⟩,
        bdd_offE I IB DN hu hC g9 hvc (n := c0) (by simp [Ex.eval, c9]) (by omega) a9, ?_⟩, ?_⟩
      · rw [show Ex.eval σ9 A (.mul I.nIE (.var (u + 12))) = L.nι * N0.A by simp only [I.hnI σ₀ hC σ9 g9, Ex.eval, a9],
          eval_offE I hu hC g9 (n := c0) (by simp [Ex.eval, c9]) (by omega) a9]
        exact hoff
      obtain ⟨σ10, h10⟩ : ∃ σ10 : ℕ → ℕ, σ10 = Function.update σ9 (u + 18) (Ex.eval σ9 A (.add (.mul I.nIE (.var (u + 12))) (offE I (.var (u + 15))))) := ⟨_, rfl⟩
      rw [← h10]
      have g10 : Ag B σ₀ σ10 := by rw [h10]; exact g9.upd (by omega) _
      have c10 : σ10 (u + 18) = L.nι * N0.A + L.off N0.A c0 := by simp [h10, e10]
      have hne : ∀ z, z ≠ u + 18 → z ≠ u + 11 → z ≠ u + 27 → z ≠ u + 19 → z ≠ u + 22 → z ≠ u + 15 → z ≠ u + 24 →
          z ≠ u + 10 → z ≠ u + 13 → z ≠ u + 12 → σ10 z = σ z := fun z h1' h2' h3' h4' h5' h6' h7' h8'' h9' h10' => by
        simp [h10, h9, h8', h7, h6, h5, h4, h3, h2, h1, Function.update_apply, h1', h2', h3', h4', h5', h6', h7', h8'',
          h9', h10']
      have x10 : σ10 xs = σ xs := hne xs (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨⟨show σ10 xs ≤ V by rw [x10]; exact hxsV, show σ10 (u + 18) ≤ V by rw [c10]; exact hoff⟩, ?_⟩
      have e11 : Ex.eval σ10 A (.sub (.var xs) (.var (u + 18))) = σ xs - (L.nι * N0.A + L.off N0.A c0) := by
        simp only [Ex.eval, x10, c10]
      set r0 := σ xs - (L.nι * N0.A + L.off N0.A c0) with hr0
      obtain ⟨σ11, h11⟩ : ∃ σ11 : ℕ → ℕ, σ11 = Function.update σ10 (u + 25) (Ex.eval σ10 A (.sub (.var xs) (.var (u + 18)))) := ⟨_, rfl⟩
      rw [← h11]
      have g11 : Ag B σ₀ σ11 := by rw [h11]; exact g10.upd (by omega) _
      have a11 : σ11 (u + 12) = N0.A := by simp [h11, h10, h9, h8', h7, h6, h5, h4, h3, h2, h1, hA, Function.update_apply]
      have n11 : σ11 (u + 19) = nc0 := by simp [h11, h10, h9, h8', h7, Function.update_apply]
      have r11 : σ11 (u + 25) = r0 := by simp [h11, e11]
      have x11 : σ11 xs = σ xs := by rw [h11, Function.update_of_ne (by omega)]; exact x10
      have hr0V : r0 ≤ V := by have := Nat.sub_le (σ xs) (L.nι * N0.A + L.off N0.A c0); omega
      have hnc0V : nc0 * N0.A + (N0.A + N0.A) ≤ V := by
        have hb := blkN_le_V DN c0 hc0K
        unfold Lay.blkN Lay.ncN at hb
        simp only [hc0K, dite_true] at hb
        rw [hnc]; omega
      have hnc0V' : nc0 ≤ V := by
        rcases Nat.eq_zero_or_pos nc0 with h0 | h0
        · omega
        · have : nc0 ≤ nc0 * N0.A := Nat.le_mul_of_pos_right _ hA1
          omega
      have nI11 := I.hnI σ₀ hC σ11 g11
      have hxV11 : σ11 xs ≤ V := by rw [x11]; exact hxsV
      have h25V : σ11 (u + 25) ≤ V := by rw [r11]; exact hr0V
      have hnI11 := IB.nI σ₀ hC σ11 g11
      refine ⟨bdd_kcodeE I hxV11 h25V a11 hnc0V' n11 hnI11 nI11 hnι hnc0V hAV h8, ?_⟩
      obtain ⟨σ12, h12⟩ : ∃ σ12 : ℕ → ℕ, σ12 = Function.update σ11 (u + 21) (Ex.eval σ11 A (kcodeE I xs)) := ⟨_, rfl⟩
      rw [← h12]
      have g12 : Ag B σ₀ σ12 := by rw [h12]; exact g11.upd (by omega) _
      have s12 : ∀ z, z ≠ u + 21 → σ12 z = σ11 z := fun z hz => by simp [h12, Function.update_apply, hz]
      have a12 : σ12 (u + 12) = N0.A := by rw [s12 _ (by omega)]; exact a11
      have n12 : σ12 (u + 19) = nc0 := by rw [s12 _ (by omega)]; exact n11
      have x12 : σ12 xs = σ xs := by rw [s12 _ (by omega)]; exact x11
      have r12 : σ12 (u + 25) = r0 := by rw [s12 _ (by omega)]; exact r11
      have nI12 := I.hnI σ₀ hC σ12 g12
      refine ⟨bdd_djE I (by rw [x12]; exact hxsV) (by rw [r12]; exact hr0V) a12 hnc0V' n12 (IB.nI σ₀ hC σ12 g12) nI12
        hnι hnc0V hAV h8, ?_⟩
      obtain ⟨σ13, h13⟩ : ∃ σ13 : ℕ → ℕ, σ13 = Function.update σ12 (u + 16) (Ex.eval σ12 A (djE I xs)) := ⟨_, rfl⟩
      rw [← h13]
      have g13 : Ag B σ₀ σ13 := by rw [h13]; exact g12.upd (by omega) _
      have s13 : ∀ z, z ≠ u + 16 → σ13 z = σ12 z := fun z hz => by simp [h13, Function.update_apply, hz]
      have a13 : σ13 (u + 12) = N0.A := by rw [s13 _ (by omega)]; exact a12
      have n13 : σ13 (u + 19) = nc0 := by rw [s13 _ (by omega)]; exact n12
      have x13 : σ13 xs = σ xs := by rw [s13 _ (by omega)]; exact x12
      have r13 : σ13 (u + 25) = r0 := by rw [s13 _ (by omega)]; exact r12
      have nI13 := I.hnI σ₀ hC σ13 g13
      refine ⟨bdd_dsE I (by rw [x13]; exact hxsV) (by rw [r13]; exact hr0V) a13 hnc0V' n13 (IB.nI σ₀ hC σ13 g13) nI13
        hnι hnc0V hAV h8, ?_⟩
      obtain ⟨σ14, h14⟩ : ∃ σ14 : ℕ → ℕ, σ14 = Function.update σ13 (u + 17) (Ex.eval σ13 A (dsE I xs)) := ⟨_, rfl⟩
      rw [← h14]
      have g14 : Ag B σ₀ σ14 := by rw [h14]; exact g13.upd (by omega) _
      refine ⟨IB.b' σ₀ hC σ14 g14, ?_⟩
      obtain ⟨σ15, h15⟩ : ∃ σ15 : ℕ → ℕ, σ15 = Function.update σ14 (u + 14) (Ex.eval σ14 A I.bE) := ⟨_, rfl⟩
      rw [← h15]
      have g15 : Ag B σ₀ σ15 := by rw [h15]; exact g14.upd (by omega) _
      have probe : ∀ y, σ15 y = Ex.eval σ A (decodeE I xs (.var y)) := by
        intro y; unfold decodeE; simp only [eval_lett']
        simp only [Ex.eval, h15, h14, h13, h12, h11, h10, h9, h8', h7, h6, h5, h4, h3, h2, h1, hnc0, hMe0]
      have viaKey : ∀ y v, (∀ σ', DInfo (B := B) (L := L) (N0 := N0) (w := w) (u := u) σ₀ q σ σ' → σ' y = v) →
          σ15 y = v := fun y v h => by
        obtain ⟨σ', hd, he⟩ := key y
        rw [probe, he]; exact h σ' hd
      have P9 : ∀ σ', DInfo (B := B) (L := L) (N0 := N0) (w := w) (u := u) σ₀ q σ σ' → ∀ c, idOf q = some c →
          σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ' (u + 12) = N0.A ∧
          σ' (u + 13) = N0.h ∧ σ' (u + 15) = c.val ∧ σ' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
          σ' (u + 19) = L.nc c ∧ σ' (u + 27) = (NP N0 w c).M ∧ σ' (u + 14) = N0.b :=
        fun σ' hd c hc => hd.2.2.2.2.2.1 c hc
      exact hbody σ15 ⟨g15, fun y hy => viaKey y (σ y) (fun σ' hd => hd.2.1 y hy),
        viaKey _ _ (fun σ' hd => hd.2.2.1), viaKey _ _ (fun σ' hd => hd.2.2.2.1),
        viaKey _ _ (fun σ' hd => hd.2.2.2.2.1),
        fun c hc => ⟨viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).1), viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.1),
          viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.1), viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.1),
          viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.2.1), viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.2.2.1),
          viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.2.2.2.1),
          viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.2.2.2.2.1),
          viaKey _ _ (fun σ' hd => (P9 σ' hd c hc).2.2.2.2.2.2.2.2)⟩,
        ⟨viaKey _ _ (fun σ' hd => hd.2.2.2.2.2.2.1), viaKey _ _ (fun σ' hd => hd.2.2.2.2.2.2.2.1),
          viaKey _ _ (fun σ' hd => hd.2.2.2.2.2.2.2.2.1), viaKey _ _ (fun σ' hd => hd.2.2.2.2.2.2.2.2.2)⟩⟩

end
end ECDLP.L84
end
