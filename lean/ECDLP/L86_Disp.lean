import ECDLP.L86_Hout
import ECDLP.L82_Out

/-!
# L86 / Disp: the repaired dispatch `outEx3` / `wtEx3` (car without `digE`, L82's balanced dispatch) and their `hout` / `hwt`

`outEx3 I X Em Kd` = `decodeE I (u+5) (lett (u+20) dqE (disp2 u (var (u+7)) fa Em ib carOutXD))` where `Kd.mid.outE = guardE u Em`
(the form produced by L79's `midKindC`).  `hout_ex3` / `hwt_ex3` are the statements of L73's `hout_ex` / `hwt_ex` for the new expressions.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L86
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L79 ECDLP.L82

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- the repaired message-code expression -/
def outBody3 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) : Ex :=
  .lett (u + 20) (dqE (u := u)) (disp2 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u))

def outEx3 (Em : Ex) (Kd : Kinds (w := w) (m := m) X) : Ex := decodeE I (u + 5) (outBody3 X Em Kd)

/-- the repaired weight dispatch -/
def wtChain3 (Sw : SrcWt (w := w) X) : Ex :=
  .ifLt (.var (u + 21)) (.lit 1) Sw.srcE
    (.ifLt (.var (u + 21)) (.lit 4) (.lit 1)
      (.lett (u + 28) (.mul (.var (u + 12)) (.var (u + 12))) (carWXD u)))

def wtEx3 (Sw : SrcWt (w := w) X) : Ex := decodeE I (u + 4) (wtChain3 X Sw)

section oracles
variable {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ
variable (Kd : Kinds (w := w) (m := m) X)

theorem hout_ex3 (Em : Ex) (hmid : Kd.mid.outE = guardE u Em) (a b : Fin (L.gTot N0.A)) (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hAB : (L.enum N0.A).symm a ∈ (edgeNetM (w := w) φ F ok m).pa ((L.enum N0.A).symm b))
    (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) (hz : σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z) :
    Ex.eval σ A (outEx3 I X Em Kd) =
      ec (ι := ι) (ιc := ιc) (w := w) ((L.enum N0.A).symm a)
        ((edgeNetM (w := w) φ F ok m).out ((L.enum N0.A).symm a) z ((L.enum N0.A).symm b)) := by
  obtain ⟨q, hq, hqa, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := ECDLP.L73.node_dec I hu hC hσ (xs := u + 5) (by omega) ha
    (outBody3 X Em Kd)
  unfold outEx3
  rw [h]
  set dqv := Ex.eval σ' A (dqE (u := u)) with hdq
  set σ2 := Function.update σ' (u + 20) dqv with h2
  have g2 : Ag B σ₀ σ2 := g'.upd (by omega) _
  have e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y := fun y hy => by simp [h2, Function.update_apply, hy]
  have s5 : σ2 (u + 5) = a := by rw [e2 _ (by omega), agr _ (Or.inl (by omega))]; exact ha
  have s6 : σ2 (u + 6) = b := by rw [e2 _ (by omega), agr _ (Or.inl (by omega))]; exact hb
  have s7 : σ2 (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z := by
    rw [e2 _ (by omega), agr _ (Or.inl (by omega))]; exact hz
  have s21 : σ2 (u + 21) = σ' (u + 21) := e2 _ (by omega)
  have hdq' : σ2 (u + 20) = dqv := by simp [h2]
  have hAB' := hAB
  have e0 : Ex.eval σ' A (outBody3 X Em Kd) = Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) := by
    simp only [outBody3, Ex.eval]
    rw [eval_disp2]
  rw [e0]
  have hb6' : σ' (u + 6) = b := by rw [agr _ (Or.inl (by omega))]; exact hb
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    have hs : (L.enum N0.A).symm a = CG.src i s' := hq
    have hL : Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) = σ2 (u + 7) := by
      simp only [chain0, Ex.eval, s21, k21, Nat.zero_lt_one, if_true]
    rw [hL, s7, out_src_q φ F ok m i s' _ hs z]
    exact zcode_noparent φ F ok m (L.enum N0.A) a (by show paC φ _ = ∅; rw [hs]; simp [paC]) z
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.fa j s') := hq
      rw [hka] at hAB'
      obtain ⟨k, hk⟩ := child_fa (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + k)) := by
        have : L.enum N0.A (CG.gt c (Gate.mid k)) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_mid]
      have hdqv : dqv = k.val := by
        rw [hdq]
        simp only [dqE, Ex.eval, k1, hb6', p18, p19, p12, hbe]
        simp
        omega
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk, hdq', hdqv]; rfl)
      have hL : Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) = Ex.eval σ2 A Kd.fa.outE := by
        simp only [chain0, Ex.eval, s21, k1]
        simp
      rw [hL]
      exact Kd.fa.hout σ₀ hC σ2 g2 a b z (by rw [hka]; rfl) hAB hkst s7
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.mid k) := hq
      rw [hka] at hAB'
      obtain ⟨j1, hk⟩ := child_mid (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + (N0.A + j1))) := by
        have : L.enum N0.A (CG.gt c (Gate.ib j1)) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_ib]
      have hdqv : dqv = j1.val := by
        rw [hdq]
        simp only [dqE, Ex.eval, k1, hb6', p18, p19, p12, hbe]
        simp
        omega
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk, hdq', hdqv]; rfl)
      have hL : Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) = Ex.eval σ2 A Kd.mid.outE := by
        rw [hmid]
        simp only [chain0, Ex.eval, s21, k1]
        simp
      rw [hL]
      exact Kd.mid.hout σ₀ hC σ2 g2 a b z (by rw [hka]; rfl) hAB hkst s7
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.ib j) := hq
      rw [hka] at hAB'
      obtain ⟨j', hk⟩ := child_ib (w := w) φ hAB'
      have hbe : (b : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + (N0.A + (N0.A + j')))) := by
        have : L.enum N0.A (CG.gt c (Gate.car j')) = b := by rw [← hk]; simp
        rw [← this, Lay.enum_gt, Lay.gateE_car]
      have hdqv : dqv = j'.val := by
        rw [hdq]
        simp only [dqE, Ex.eval, k1, hb6', p18, p19, p12, hbe]
        simp
        omega
      have hkst := kst_of (w := w) hu hC hσ (b := b) hq e2 s5 s6 (fun c' hc' => by
          have : c' = c := by simpa [idOf] using hc'.symm
          subst this; exact ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩) p14 j16 s17
        (by rw [hk, hdq', hdqv]; rfl)
      have hL : Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) = Ex.eval σ2 A Kd.ib.outE := by
        simp only [chain0, Ex.eval, s21, k1]
        simp
      rw [hL]
      exact Kd.ib.hout σ₀ hC σ2 g2 a b z (by rw [hka]; rfl) hAB hkst s7
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      have hL : Ex.eval σ2 A (chain0 u (.var (u + 7)) Kd.fa.outE Em Kd.ib.outE (carOutXD u)) = Ex.eval σ2 A (carOutXD u) := by
        simp only [chain0, Ex.eval, s21, k1]
        simp
      rw [hL]
      have q10 : σ2 (u + 10) = 2 ^ (NP N0 w c).b := by rw [e2 _ (by omega)]; exact p10
      have q11 : σ2 (u + 11) = 2 ^ (NP N0 w c).M := by rw [e2 _ (by omega)]; exact p11
      have q16 : σ2 (u + 16) = j.val := by rw [e2 _ (by omega), j16]; simp [coordOf]
      exact car_houtD L X hu hC g2 (b := b) hka q10 q11 q16 z s7


variable (Sw : SrcWt (w := w) X)

theorem hwt_ex3 (hm1 : 1 < m) (a : Fin (L.gTot N0.A)) (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (ha : σ (u + 4) = a) (hz : σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z) :
    Ex.eval σ A (wtEx3 I X Sw) =
      if (edgeNetM (w := w) φ F ok m).W ((L.enum N0.A).symm a) z = 1 then 1 else 0 := by
  obtain ⟨q, hq, hqa, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := ECDLP.L73.node_dec I hu hC hσ (xs := u + 4) (by omega) ha
    (wtChain3 X Sw)
  unfold wtEx3
  rw [h]
  have z' : σ' (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z := by
    rw [agr _ (Or.inl (by omega))]; exact hz
  have a' : σ' (u + 4) = a := by rw [agr _ (Or.inl (by omega))]; exact ha
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    have hs : (L.enum N0.A).symm a = CG.src i s' := hq
    have hL : Ex.eval σ' A (wtChain3 X Sw) = Ex.eval σ' A Sw.srcE := by
      simp only [wtChain3, Ex.eval, k21, Nat.zero_lt_one, if_true]
    rw [hL]
    simp only [coordOf] at j16 s17
    exact Sw.hsrc σ₀ hC σ' g' a i s' z hs a' z' hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 j16 s17
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain3 X Sw) = 1 := by
        simp only [wtChain3, Ex.eval, k1]; simp
      rw [hL, W_fa_q hu hC hσ c j s' _ hq z]; simp
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain3 X Sw) = 1 := by
        simp only [wtChain3, Ex.eval, k1]; simp
      rw [hL, W_mid_q hu hC hσ c k _ hq z]; simp
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain3 X Sw) = 1 := by
        simp only [wtChain3, Ex.eval, k1]; simp
      rw [hL, W_ib_q hu hC hσ c j _ hq z]; simp
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      set σ3 := Function.update σ' (u + 28) (σ' (u + 12) * σ' (u + 12)) with h3
      have g3 : Ag B σ₀ σ3 := g'.upd (by omega) _
      have e3 : ∀ y, y ≠ u + 28 → σ3 y = σ' y := fun y hy => by simp [h3, Function.update_apply, hy]
      have hL : Ex.eval σ' A (wtChain3 X Sw) = Ex.eval σ3 A (carWXD u) := by
        simp only [wtChain3, Ex.eval, k1]
        simp
        rfl
      rw [hL]
      have q10 : σ3 (u + 10) = 2 ^ (NP N0 w c).b := by rw [e3 _ (by omega)]; exact p10
      have q11 : σ3 (u + 11) = 2 ^ (NP N0 w c).M := by rw [e3 _ (by omega)]; exact p11
      have q16 : σ3 (u + 16) = j.val := by rw [e3 _ (by omega), j16]; simp [coordOf]
      have q28 : σ3 (u + 28) = (NP N0 w c).A * (NP N0 w c).A := by
        simp [h3, p12]; rfl
      exact car_hwtD L X hu hC g3 hm1 hka q10 q11 q16 q28 z (by rw [e3 _ (by omega)]; exact z')



end oracles
end
end ECDLP.L86
end
