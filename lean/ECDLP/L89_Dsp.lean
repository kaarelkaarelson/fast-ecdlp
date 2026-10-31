import ECDLP.L84_PExB0
import ECDLP.L89_Clamp

/-!
# L89 / Dsp: dispatch-level value bound of the message code `outEx` (edges only)

`bdd_outEx`: for every edge `a -> b` (parent `a`, child `b`) and every state with slot `u+7 <= V`, the L73 dispatch `outEx` is bounded
by `V` (`Bdd V`), assuming the per-kind bounds in the `KSt` form (fa, mid, ib: exactly the conclusions of `faKindC_bout`,
`midKindC_bout`, `ibKindC_bout`) and a bound of the car expression.  For a non-edge pair the per-kind lemmas do not apply
(`KSt.hq` fails); `PExBw.bout` (L89_Bw) quantifies over edges only, which is all L69's `bdd_mMsg` uses.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L89
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L84

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ}

theorem bdd_dqE {σ' : ℕ → ℕ} (h8 : 8 ≤ V) (h21 : σ' (u + 21) ≤ 4) (h6 : σ' (u + 6) ≤ V)
    (hk : 1 ≤ σ' (u + 21) → σ' (u + 21) ≤ 3 → σ' (u + 12) ≤ V ∧ σ' (u + 18) ≤ V ∧ σ' (u + 19) ≤ V)
    (hb1 : σ' (u + 21) = 1 → σ' (u + 18) + σ' (u + 19) * σ' (u + 12) ≤ σ' (u + 6))
    (hb2 : σ' (u + 21) = 2 → σ' (u + 18) + σ' (u + 19) * σ' (u + 12) + σ' (u + 12) ≤ σ' (u + 6))
    (hb3 : σ' (u + 21) = 3 → σ' (u + 18) + σ' (u + 19) * σ' (u + 12) + (σ' (u + 12) + σ' (u + 12)) ≤ σ' (u + 6)) :
    Bdd V σ' A (dqE (u := u)) := by
  have hc : σ' (u + 21) = 0 ∨ σ' (u + 21) = 1 ∨ σ' (u + 21) = 2 ∨ σ' (u + 21) = 3 ∨ σ' (u + 21) = 4 := by omega
  simp only [dqE, Bdd, Ex.eval]
  rcases hc with h | h | h | h | h
  · simp [h]; omega
  · have := hb1 h; have := hk (by omega) (by omega); simp [h]; omega
  · have := hb2 h; have := hk (by omega) (by omega); simp [h]; omega
  · have := hb3 h; have := hk (by omega) (by omega); simp [h]; omega
  · simp [h]; omega

variable (Kd : Kinds (w := w) (m := m) X)

theorem bdd_outChain {σ2 : ℕ → ℕ} (h8 : 8 ≤ V) (h21 : σ2 (u + 21) ≤ 4)
    (h0 : σ2 (u + 21) = 0 → σ2 (u + 7) ≤ V) (h1 : σ2 (u + 21) = 1 → Bdd V σ2 A Kd.fa.outE)
    (h2 : σ2 (u + 21) = 2 → Bdd V σ2 A Kd.mid.outE) (h3 : σ2 (u + 21) = 3 → Bdd V σ2 A Kd.ib.outE)
    (h4 : σ2 (u + 21) = 4 → Bdd V σ2 A (carOutX I X)) : Bdd V σ2 A (outChain I X Kd) := by
  have hc : σ2 (u + 21) = 0 ∨ σ2 (u + 21) = 1 ∨ σ2 (u + 21) = 2 ∨ σ2 (u + 21) = 3 ∨ σ2 (u + 21) = 4 := by omega
  simp only [outChain, Bdd, Ex.eval]
  rcases hc with h | h | h | h | h
  · have := h0 h; simp [h]; omega
  · have := h1 h; generalize Bdd V σ2 A Kd.fa.outE = P at this ⊢; simp [h]; (repeat' apply And.intro) <;> first | assumption | omega
  · have := h2 h; generalize Bdd V σ2 A Kd.mid.outE = P at this ⊢; simp [h]; (repeat' apply And.intro) <;> first | assumption | omega
  · have := h3 h; generalize Bdd V σ2 A Kd.ib.outE = P at this ⊢; simp [h]; (repeat' apply And.intro) <;> first | assumption | omega
  · have := h4 h; generalize Bdd V σ2 A (carOutX I X) = P at this ⊢; simp [h]; (repeat' apply And.intro) <;> first | assumption | omega


theorem bdd_outEx (hu : B ≤ u) (IB : InstBdd V I) (DN : DecNum V L N0 w) (h8 : 8 ≤ V)
    (hfa : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.fa →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.fa.outE)
    (hmid : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.mid →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.mid.outE)
    (hib : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.ib →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.ib.outE)
    (hcar : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 5) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 7) ≤ V → Bdd V σ A (carOutX I X)) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A),
      (L.enum N0.A).symm a ∈ (edgeNetM (w := w) φ F ok m).pa ((L.enum N0.A).symm b) →
      σ (u + 5) = a → σ (u + 6) = b → σ (u + 7) ≤ V → Bdd V σ A (outEx I X Kd) := by
  intro σ₀ hC σ hσ a b hAB ha hb hz
  have hA := I.hA σ₀ hC σ hσ
  have hAV : N0.A ≤ V := by have := le_of_B (IB.A' σ₀ hC σ hσ); rwa [hA] at this
  have hA1 : 0 < N0.A := N0.toPar.A_pos
  have hbV : (b : ℕ) ≤ V := le_trans b.2.le DN.hG
  obtain ⟨q, hq⟩ : ∃ q, (L.enum N0.A).symm a = q := ⟨_, rfl⟩
  unfold outEx
  refine bdd_decodeE I IB DN h8 hu hC hσ (xs := u + 5) (by omega) q (by rw [ha, ← hq]; simp)
    (by rw [ha]; exact le_trans a.2.le DN.hG) (fun σ' hD => ?_)
  obtain ⟨g', agr, k21, j16, s17, hp, hg⟩ := hD
  have hb6 : σ' (u + 6) = b := by rw [agr _ (Or.inl (by omega))]; exact hb
  have hz' : σ' (u + 7) ≤ V := by rw [agr _ (Or.inl (by omega))]; exact hz
  have s5' : σ' (u + 5) = a := by rw [agr _ (Or.inl (by omega))]; exact ha
  have k4 := kc_le_four q
  show Bdd V σ' A (.lett (u + 20) (dqE (u := u)) (outChain I X Kd))
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    have hdqB : Bdd V σ' A (dqE (u := u)) := bdd_dqE (A := A) h8 (by omega) (by rw [hb6]; exact hbV)
      (fun h1 _ => by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega)
    refine ⟨hdqB, ?_⟩
    have hdqv : Ex.eval σ' A (dqE (u := u)) = 0 := by simp [dqE, Ex.eval, k21]
    rw [hdqv]
    have g2 : Ag B σ₀ (Function.update σ' (u + 20) 0) := g'.upd (by omega) _
    have e2 : ∀ y, y ≠ u + 20 → Function.update σ' (u + 20) 0 y = σ' y := fun y hy => Function.update_of_ne hy _ _
    refine bdd_outChain I X Kd h8 (by rw [e2 _ (by omega)]; omega) (fun _ => by rw [e2 _ (by omega)]; exact hz')
      (fun h => by rw [e2 _ (by omega)] at h; omega) (fun h => by rw [e2 _ (by omega)] at h; omega)
      (fun h => by rw [e2 _ (by omega)] at h; omega) (fun h => by rw [e2 _ (by omega)] at h; omega)
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.fa j s') := hq
      have hAB' := hAB
      rw [hka] at hAB'
      obtain ⟨k, hk⟩ := child_fa (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + k)) := by
        have : L.enum N0.A (CG.gt c (Gate.mid k)) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_mid]
      have hdqv : Ex.eval σ' A (dqE (u := u)) = k.val := by
        simp only [dqE, Ex.eval, k1, hb6, p18, p19, p12, hbe]
        simp
        omega
      have hdqB : Bdd V σ' A (dqE (u := u)) := bdd_dqE (A := A) h8 (by omega) (by rw [hb6]; exact hbV)
        (fun _ _ => ⟨by rw [p12]; exact hAV, by rw [p18]; omega, by
          rw [p19]; have := Nat.le_mul_of_pos_right (L.nc c) hA1; omega⟩)
        (fun _ => by rw [p18, p19, p12, hb6, hbe]; omega) (fun h => by omega) (fun h => by omega)
      refine ⟨hdqB, ?_⟩
      rw [hdqv]
      set σ2 := Function.update σ' (u + 20) k.val with h2
      have g2 : Ag B σ₀ σ2 := g'.upd (by omega) _
      have e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y := fun y hy => by simp [h2, Function.update_apply, hy]
      have s5 : σ2 (u + 5) = a := by rw [e2 _ (by omega)]; exact s5'
      have s6 : σ2 (u + 6) = b := by rw [e2 _ (by omega)]; exact hb6
      have s21 : σ2 (u + 21) = 1 := by rw [e2 _ (by omega)]; exact k1
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk]; simp [h2, childCoord])
      refine bdd_outChain I X Kd h8 (by omega) (fun h => by omega)
        (fun _ => hfa σ₀ hC σ2 g2 a b (by rw [hka]; rfl) hkst (by rw [e2 _ (by omega)]; exact hz'))
        (fun h => by omega) (fun h => by omega) (fun h => by omega)
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.mid k) := hq
      have hAB' := hAB
      rw [hka] at hAB'
      obtain ⟨j1, hk⟩ := child_mid (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + (N0.A + j1))) := by
        have : L.enum N0.A (CG.gt c (Gate.ib j1)) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_ib]
      have hdqv : Ex.eval σ' A (dqE (u := u)) = j1.val := by
        simp only [dqE, Ex.eval, k1, hb6, p18, p19, p12, hbe]
        simp
        omega
      have hdqB : Bdd V σ' A (dqE (u := u)) := bdd_dqE (A := A) h8 (by omega) (by rw [hb6]; exact hbV)
        (fun _ _ => ⟨by rw [p12]; exact hAV, by rw [p18]; omega, by
          rw [p19]; have := Nat.le_mul_of_pos_right (L.nc c) hA1; omega⟩)
        (fun h => by omega) (fun _ => by rw [p18, p19, p12, hb6, hbe]; omega) (fun h => by omega)
      refine ⟨hdqB, ?_⟩
      rw [hdqv]
      set σ2 := Function.update σ' (u + 20) j1.val with h2
      have g2 : Ag B σ₀ σ2 := g'.upd (by omega) _
      have e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y := fun y hy => by simp [h2, Function.update_apply, hy]
      have s5 : σ2 (u + 5) = a := by rw [e2 _ (by omega)]; exact s5'
      have s6 : σ2 (u + 6) = b := by rw [e2 _ (by omega)]; exact hb6
      have s21 : σ2 (u + 21) = 2 := by rw [e2 _ (by omega)]; exact k1
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk]; simp [h2, childCoord])
      refine bdd_outChain I X Kd h8 (by omega) (fun h => by omega) (fun h => by omega)
        (fun _ => hmid σ₀ hC σ2 g2 a b (by rw [hka]; rfl) hkst (by rw [e2 _ (by omega)]; exact hz'))
        (fun h => by omega) (fun h => by omega)
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.ib j) := hq
      have hAB' := hAB
      rw [hka] at hAB'
      obtain ⟨j', hk⟩ := child_ib (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + (N0.A + (N0.A + j')))) := by
        have : L.enum N0.A (CG.gt c (Gate.car j')) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_car]
      have hdqv : Ex.eval σ' A (dqE (u := u)) = j'.val := by
        simp only [dqE, Ex.eval, k1, hb6, p18, p19, p12, hbe]
        simp
        omega
      have hdqB : Bdd V σ' A (dqE (u := u)) := bdd_dqE (A := A) h8 (by omega) (by rw [hb6]; exact hbV)
        (fun _ _ => ⟨by rw [p12]; exact hAV, by rw [p18]; omega, by
          rw [p19]; have := Nat.le_mul_of_pos_right (L.nc c) hA1; omega⟩)
        (fun h => by omega) (fun h => by omega) (fun _ => by rw [p18, p19, p12, hb6, hbe]; omega)
      refine ⟨hdqB, ?_⟩
      rw [hdqv]
      set σ2 := Function.update σ' (u + 20) j'.val with h2
      have g2 : Ag B σ₀ σ2 := g'.upd (by omega) _
      have e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y := fun y hy => by simp [h2, Function.update_apply, hy]
      have s5 : σ2 (u + 5) = a := by rw [e2 _ (by omega)]; exact s5'
      have s6 : σ2 (u + 6) = b := by rw [e2 _ (by omega)]; exact hb6
      have s21 : σ2 (u + 21) = 3 := by rw [e2 _ (by omega)]; exact k1
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk]; simp [h2, childCoord])
      refine bdd_outChain I X Kd h8 (by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega)
        (fun _ => hib σ₀ hC σ2 g2 a b (by rw [hka]; rfl) hkst (by rw [e2 _ (by omega)]; exact hz'))
        (fun h => by omega)
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      have hdqv : Ex.eval σ' A (dqE (u := u)) = 0 := by simp [dqE, Ex.eval, k1]
      have hdqB : Bdd V σ' A (dqE (u := u)) := bdd_dqE (A := A) h8 (by omega) (by rw [hb6]; exact hbV)
        (fun h1 h2 => by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega)
      refine ⟨hdqB, ?_⟩
      rw [hdqv]
      set σ2 := Function.update σ' (u + 20) 0 with h2
      have g2 : Ag B σ₀ σ2 := g'.upd (by omega) _
      have e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y := fun y hy => by simp [h2, Function.update_apply, hy]
      have s21 : σ2 (u + 21) = 4 := by rw [e2 _ (by omega)]; exact k1
      refine bdd_outChain I X Kd h8 (by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega)
        (fun h => by omega) (fun _ => hcar σ₀ hC σ2 g2 a c j hka (by rw [e2 _ (by omega)]; exact s5')
          (by rw [e2 _ (by omega)]; exact p10) (by rw [e2 _ (by omega)]; exact p11) (by rw [e2 _ (by omega)]; exact hz'))


/-- **NEGATIVE (LEAN): L73's `outEx` returns the setting code on a source node**, for any state (no edge hypothesis). -/
theorem eval_outEx_src (hu : B ≤ u) {σ₀ σ : ℕ → ℕ} (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {a : Fin (L.gTot N0.A)} {i : ι} {s : Fin N0.A}
    (hs : (L.enum N0.A).symm a = CG.src i s) (ha : σ (u + 5) = a) :
    Ex.eval σ A (outEx I X Kd) = σ (u + 7) := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 5) (by omega) ha (outBody I X Kd)
  unfold outEx
  rw [h]
  have hq' : q = CG.src i s := hq.symm.trans hs
  subst hq'
  simp only [kindOf, kc] at k21
  have e7 : σ' (u + 7) = σ (u + 7) := agr _ (Or.inl (by omega))
  simp only [outBody, outChain, Ex.eval, Function.update_apply, k21]
  simp [e7]

/-- the real dispatch violates `PExB.bout`'s `eval + 1 <= V` on a source with setting code `V` -/
theorem not_bout_outEx (hu : B ≤ u) {σ₀ σ : ℕ → ℕ} (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {a : Fin (L.gTot N0.A)} {i : ι} {s : Fin N0.A}
    (hs : (L.enum N0.A).symm a = CG.src i s) (ha : σ (u + 5) = a) (h7 : σ (u + 7) = V) :
    ¬ (Ex.eval σ A (outEx I X Kd) + 1 ≤ V) := by
  rw [eval_outEx_src I X Kd hu hC hσ hs ha, h7]; omega

end
end ECDLP.L89
end
