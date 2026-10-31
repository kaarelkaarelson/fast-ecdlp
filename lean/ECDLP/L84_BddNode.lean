import ECDLP.L84_BddDec
import ECDLP.L73_Asm

/-!
# L84 / BddNode: value bounds of the structural expressions `gEx`, `nfEx`, `nmEx`, `wEx` of the edge network
(the `bg`, `bnf`, `bnm`, `bw` fields of L69's `PExB` and of L75's `PExB0`)
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
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι}

/-- numeric requirements of the node-size expressions -/
structure NodeNum (V : ℕ) (N0 : NPar) (w : Fin K → ℕ) : Prop where
  hh : N0.h ≤ V
  hb : N0.b ≤ V
  hpb : 2 ^ N0.b ≤ V
  hBh : (2 ^ N0.b) ^ N0.h ≤ V
  hbh : N0.b * N0.h ≤ V
  hMM : ∀ c : Fin K, 8 * 2 ^ (NP N0 w c).M + 1 ≤ V
  hM3 : ∀ c : Fin K, (NP N0 w c).M + 3 ≤ V

theorem bdd_gEx {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) : Bdd V σ A (gEx I) := by
  have hA := I.hA σ₀ hC σ hσ
  have hAV : N0.A ≤ V := by rw [← hA]; exact le_of_B (IB.A' σ₀ hC σ hσ)
  have g1 : Ag B σ₀ (Function.update σ (u + 12) (Ex.eval σ A I.AE)) := hσ.upd (by omega) _
  have hnι : L.nι * N0.A ≤ V := by
    have := DN.hG; unfold Lay.gTot at this; omega
  have hnI := I.hnI σ₀ hC _ g1
  have hK := I.hK σ₀ hC _ g1
  have a1 : (Function.update σ (u + 12) (Ex.eval σ A I.AE)) (u + 12) = N0.A := by simp [hA]
  refine ⟨IB.A' σ₀ hC σ hσ, ?_⟩
  refine ⟨⟨IB.nI σ₀ hC _ g1, by show (Function.update σ (u + 12) (Ex.eval σ A I.AE)) (u + 12) ≤ V; rw [a1]; exact hAV,
    by simp only [Ex.eval, hnI, a1]; exact hnι⟩,
    bdd_offE I IB DN hu hC g1 (IB.K' σ₀ hC _ g1) (n := K) hK le_rfl a1, ?_⟩
  simp only [Ex.eval, hnI, a1]
  rw [eval_offE I hu hC g1 (n := K) hK le_rfl a1]
  have := DN.hG; unfold Lay.gTot at this; exact this


theorem bdd_nprod_bh {V : ℕ} (NN : NodeNum V N0 w) {σ' : ℕ → ℕ} (h13 : σ' (u + 13) = N0.h) (h10 : σ' (u + 10) = 2 ^ N0.b) :
    Bdd V σ' A (nprod (u + 91) (.var (u + 13)) (.var (u + 10))) := by
  refine B_nprodV (show Bdd V σ' A (Ex.var (u + 13)) by show σ' (u + 13) ≤ V; rw [h13]; exact NN.hh)
    (fun j hj => show (Function.update σ' (u + 91) j) (u + 10) ≤ V by
      rw [Function.update_of_ne (by omega), h10]; exact NN.hpb) (fun j hj => ?_)
  have hj' : j ≤ N0.h := by
    have : Ex.eval σ' A (Ex.var (u + 13)) = N0.h := h13
    omega
  have hc : pp (fun i => Ex.eval (Function.update σ' (u + 91) i) A (Ex.var (u + 10))) j = pp (fun _ => 2 ^ N0.b) j :=
    pp_congr (fun i _ => by
      show (Function.update σ' (u + 91) i) (u + 10) = 2 ^ N0.b
      rw [Function.update_of_ne (by omega), h10])
  rw [hc, pp_const]
  exact le_trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) hj') NN.hBh


/-- generic wrapper: a body bounded in every decode state gives a bound for the node expression at the node of slot `u+4` -/
theorem bdd_node4 {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) (k : Fin (L.gTot N0.A)) (hk : σ (u + 4) = k)
    {body : Ex}
    (hbody : ∀ σ', DInfo (B := B) (L := L) (N0 := N0) (w := w) (u := u) σ₀ ((L.enum N0.A).symm k) σ σ' → Bdd V σ' A body) :
    Bdd V σ A (decodeE I (u + 4) body) :=
  bdd_decodeE I IB DN h8 hu hC hσ (xs := u + 4) (by omega) ((L.enum N0.A).symm k) (by rw [hk]; simp)
    (by rw [hk]; exact le_trans k.2.le DN.hG) hbody

theorem kc_le_four (q : CG ι ιc N0.A) : kc (kindOf q) ≤ 4 := by
  cases q with
  | src i s => simp [kindOf, kc]
  | gt c g => cases g <;> simp [kindOf, kc]

theorem bdd_nfEx {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (h8 : 8 ≤ V) {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) (k : Fin (L.gTot N0.A)) (hk : σ (u + 4) = k) :
    Bdd V σ A (nfEx I) := by
  refine bdd_node4 I IB DN h8 hu hC hσ k hk (fun σ' hd => ?_)
  obtain ⟨g', pres, k21, j16, s17, hp, hg⟩ := hd
  have hk4 := kc_le_four ((L.enum N0.A).symm k)
  refine ⟨show σ' (u + 21) ≤ V by omega, show 1 ≤ V by omega, ?_⟩
  by_cases hs : σ' (u + 21) < 1
  · simp only [Ex.eval, hs, if_true]
    exact bdd_nprod_bh NN hg.2.2.1 hg.1
  · simp only [Ex.eval, hs, if_false]; show 1 ≤ V; omega

theorem bdd_nmEx {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (h8 : 8 ≤ V) {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) (k : Fin (L.gTot N0.A)) (hk : σ (u + 4) = k) :
    Bdd V σ A (nmEx I) := by
  refine bdd_node4 I IB DN h8 hu hC hσ k hk (fun σ' hd => ?_)
  obtain ⟨g', pres, k21, j16, s17, hp, hg⟩ := hd
  have hk4 := kc_le_four ((L.enum N0.A).symm k)
  refine ⟨show σ' (u + 21) ≤ V by omega, show 1 ≤ V by omega, ?_⟩
  by_cases hs : σ' (u + 21) < 1
  · simp only [Ex.eval, hs, if_true]
    exact bdd_nprod_bh NN hg.2.2.1 hg.1
  · simp only [Ex.eval, hs, if_false]
    obtain ⟨c, hc⟩ : ∃ c, idOf ((L.enum N0.A).symm k) = some c := by
      cases h : (L.enum N0.A).symm k with
      | src i s => rw [h] at k21; simp [kindOf, kc] at k21; omega
      | gt c g => exact ⟨c, rfl⟩
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c hc
    have hMM := NN.hMM c
    refine ⟨show σ' (u + 21) ≤ V by omega, show 4 ≤ V by omega, ?_⟩
    by_cases h4 : σ' (u + 21) < 4
    · simp only [Ex.eval, h4, if_true]
      refine ⟨show σ' (u + 11) ≤ V by rw [p11]; omega, show 1 ≤ V by omega, ?_⟩
      simp only [Ex.eval, p11]; omega
    · simp only [Ex.eval, h4, if_false]
      refine ⟨show 8 ≤ V by omega, show σ' (u + 11) ≤ V by rw [p11]; omega, ?_⟩
      simp only [Ex.eval, p11]; omega

theorem bdd_wEx {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (h8 : 8 ≤ V) {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) (k : Fin (L.gTot N0.A)) (hk : σ (u + 4) = k) :
    Bdd V σ A (wEx I) := by
  refine bdd_node4 I IB DN h8 hu hC hσ k hk (fun σ' hd => ?_)
  obtain ⟨g', pres, k21, j16, s17, hp, hg⟩ := hd
  have hk4 := kc_le_four ((L.enum N0.A).symm k)
  refine ⟨show σ' (u + 21) ≤ V by omega, show 1 ≤ V by omega, ?_⟩
  by_cases hs : σ' (u + 21) < 1
  · simp only [Ex.eval, hs, if_true]
    refine ⟨show σ' (u + 14) ≤ V by rw [hg.2.2.2]; exact NN.hb, show σ' (u + 13) ≤ V by rw [hg.2.2.1]; exact NN.hh, ?_⟩
    simp only [Ex.eval, hg.2.2.1, hg.2.2.2]; exact NN.hbh
  · simp only [Ex.eval, hs, if_false]
    obtain ⟨c, hc⟩ : ∃ c, idOf ((L.enum N0.A).symm k) = some c := by
      cases h : (L.enum N0.A).symm k with
      | src i s => rw [h] at k21; simp [kindOf, kc] at k21; omega
      | gt c g => exact ⟨c, rfl⟩
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c hc
    have hM3 := NN.hM3 c
    refine ⟨show σ' (u + 21) ≤ V by omega, show 4 ≤ V by omega, ?_⟩
    by_cases h4 : σ' (u + 21) < 4
    · simp only [Ex.eval, h4, if_true]
      refine ⟨show σ' (u + 27) ≤ V by rw [p27]; omega, show 1 ≤ V by omega, ?_⟩
      simp only [Ex.eval, p27]; omega
    · simp only [Ex.eval, h4, if_false]
      refine ⟨show σ' (u + 27) ≤ V by rw [p27]; omega, show 3 ≤ V by omega, ?_⟩
      simp only [Ex.eval, p27]; omega


theorem blk_end_le {V : ℕ} (DN : DecNum V L N0 w) (c : Fin K) :
    L.nι * N0.A + L.off N0.A c + (L.nc c * N0.A + (N0.A + (N0.A + N0.A * N0.A))) ≤ V := by
  have h1 := L.off_succ N0.A c.val
  have h2 := L.off_mono N0.A (show c.val + 1 ≤ K from c.2)
  have h3 := DN.hG
  unfold Lay.gTot at h3
  have h4 : L.blkN N0.A c.val = L.nc c * N0.A + (N0.A + (N0.A + N0.A * N0.A)) := by
    unfold Lay.blkN Lay.ncN; simp [c.2]
  omega

theorem bdd_parFa {V : ℕ} (Ph : PhiEx L φ B Ctx A u) (DN : DecNum V L N0 w) (h8 : 8 ≤ V)
    {σ₀ σ' : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (g' : Ag B σ₀ σ') (c : Fin K) (j : ιc c) (s : Fin N0.A)
    (h15 : σ' (u + 15) = c.val) (h12 : σ' (u + 12) = N0.A) (h16 : σ' (u + 16) = (L.ecc c j : ℕ)) (h17 : σ' (u + 17) = s.val)
    (h5 : σ' (u + 5) ≤ V) (hAV : N0.A ≤ V)
    (hphiB : ∀ τ, Ag B σ₀ τ → τ (u + 22) = c.val → τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE) :
    Bdd V σ' A (.lett (u + 22) (.var (u + 15)) (.lett (u + 23) (.var (u + 16))
        (ECDLP.L73.eqE (.var (u + 5)) (.add (.mul Ph.phiE (.var (u + 12))) (.var (u + 17)))))) := by
  have hcV : c.val ≤ V := by have := c.2; have := DN.hK; omega
  have hec : (L.ecc c j : ℕ) ≤ V := by
    have h1 := (L.ecc c j).2
    have h2 := blk_end_le (L := L) (N0 := N0) DN c
    have : N0.A ≥ 1 := N0.toPar.A_pos
    have : L.nc c ≤ L.nc c * N0.A := Nat.le_mul_of_pos_right _ this
    omega
  have g1 : Ag B σ₀ (Function.update σ' (u + 22) (Ex.eval σ' A (Ex.var (u + 15)))) := g'.upd (by omega) _
  refine ⟨show σ' (u + 15) ≤ V by rw [h15]; exact hcV, ?_⟩
  set τ1 := Function.update σ' (u + 22) (Ex.eval σ' A (Ex.var (u + 15))) with hτ1
  have g2 : Ag B σ₀ (Function.update τ1 (u + 23) (Ex.eval τ1 A (Ex.var (u + 16)))) := g1.upd (by omega) _
  have t16 : τ1 (u + 16) = (L.ecc c j : ℕ) := by rw [hτ1, Function.update_of_ne (by omega)]; exact h16
  refine ⟨show τ1 (u + 16) ≤ V by rw [t16]; exact hec, ?_⟩
  set τ2 := Function.update τ1 (u + 23) (Ex.eval τ1 A (Ex.var (u + 16))) with hτ2
  have t22 : τ2 (u + 22) = c.val := by
    rw [hτ2, Function.update_of_ne (by omega), hτ1]; simp [Ex.eval, h15]
  have t23 : τ2 (u + 23) = (L.ecc c j : ℕ) := by rw [hτ2]; simp [Ex.eval, t16]
  have t5 : τ2 (u + 5) = σ' (u + 5) := by
    rw [hτ2, Function.update_of_ne (by omega), hτ1, Function.update_of_ne (by omega)]
  have t12 : τ2 (u + 12) = N0.A := by
    rw [hτ2, Function.update_of_ne (by omega), hτ1, Function.update_of_ne (by omega)]; exact h12
  have t17 : τ2 (u + 17) = s.val := by
    rw [hτ2, Function.update_of_ne (by omega), hτ1, Function.update_of_ne (by omega)]; exact h17
  have hph := Ph.hphi σ₀ hC τ2 g2 c j t22 t23
  have hbp := hphiB τ2 g2 t22 t23
  have hphiLt : Ex.eval τ2 A Ph.phiE < L.nι := by rw [hph]; exact (L.eι (φ c j)).2
  have hsA := s.2
  have hlt : Ex.eval τ2 A Ph.phiE * N0.A + s.val ≤ L.nι * N0.A := by
    have : (Ex.eval τ2 A Ph.phiE + 1) * N0.A ≤ L.nι * N0.A := Nat.mul_le_mul_right _ hphiLt
    nlinarith
  have hG : L.nι * N0.A ≤ V := by have := DN.hG; unfold Lay.gTot at this; omega
  simp only [ECDLP.L73.eqE, Bdd, Ex.eval, t5, t12, t17]
  have hmul : Ex.eval τ2 A Ph.phiE * N0.A ≤ V := by omega
  split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega


theorem bdd_parEx {V : ℕ} (I : InstEx L N0 w B Ctx A u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (Ph : PhiEx L φ B Ctx A u)
    (h8 : 8 ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE)
    {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) (p c' : Fin (L.gTot N0.A)) (hp : σ (u + 5) = p)
    (hc : σ (u + 6) = c') : Bdd V σ A (parEx I φ Ph) := by
  have hpV : (p : ℕ) + 1 ≤ V := by have := p.2; have := DN.hG; omega
  have hAV : N0.A ≤ V := by
    have := I.hA σ₀ hC σ hσ
    rw [← this]; exact le_of_B (IB.A' σ₀ hC σ hσ)
  have hA1 : 0 < N0.A := N0.toPar.A_pos
  refine bdd_decodeE I IB DN h8 hu hC hσ (xs := u + 6) (by omega) ((L.enum N0.A).symm c') (by rw [hc]; simp)
    (by rw [hc]; exact le_trans c'.2.le DN.hG) (fun σ' hd => ?_)
  obtain ⟨g', pres, k21, j16, s17, hp9, hg⟩ := hd
  have h5 : σ' (u + 5) = p := by rw [pres _ (Or.inl (by omega))]; exact hp
  cases hq : (L.enum N0.A).symm c' with
  | src i s =>
    rw [hq] at k21
    simp only [kindOf, kc] at k21
    simp only [Bdd, Ex.eval, k21]
    split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega
  | gt c g =>
    rw [hq] at k21 j16 s17
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp9 c (by simp [idOf, hq])
    have hblk := blk_end_le (L := L) (N0 := N0) DN c
    have hAA : N0.A ≤ N0.A * N0.A := Nat.le_mul_self _
    have hmod : σ' (u + 16) % N0.A < N0.A := Nat.mod_lt _ hA1
    have hncA : L.nc c ≤ L.nc c * N0.A := Nat.le_mul_of_pos_right _ hA1
    cases g with
    | fa j s =>
      simp only [kindOf, kc, coordOf] at k21 j16 s17
      have hph : ∀ τ, Ag B σ₀ τ → τ (u + 22) = c.val → τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE :=
        fun τ gτ h1 h2 => hphiB σ₀ hC τ gτ c j h1 h2
      have hf := bdd_parFa Ph DN h8 hu hC g' c j s p15 p12 j16 s17 (by rw [h5]; omega) hAV hph
      refine ⟨by show σ' (u + 21) ≤ V; omega, by show 1 ≤ V; omega, ?_⟩
      rw [if_neg (by simp [Ex.eval, k21])]
      refine ⟨by show σ' (u + 21) ≤ V; omega, by show 2 ≤ V; omega, ?_⟩
      rw [if_pos (by simp [Ex.eval, k21])]
      exact hf
    | mid k =>
      simp only [kindOf, kc] at k21
      simp only [Bdd, Ex.eval, k21, p18, p19, p12, h5]
      split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega
    | ib j =>
      simp only [kindOf, kc] at k21
      simp only [Bdd, Ex.eval, k21, p18, p19, p12, h5]
      split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega
    | car j =>
      simp only [kindOf, kc, coordOf] at k21 j16
      have hj := j.2
      simp only [Bdd, Ex.eval, ECDLP.L73.eqE, k21, p18, p19, p12, h5, j16]
      have hmod' : (j : ℕ) % N0.A < N0.A := Nat.mod_lt _ hA1
      split_ifs <;> (repeat' apply And.intro) <;> first | assumption | trivial | omega

end
end ECDLP.L84
end
