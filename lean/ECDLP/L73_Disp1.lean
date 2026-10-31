import ECDLP.L73_Par
import ECDLP.L73_Card

/-!
# L73 / Disp1: node count, free count, message count, width, parent test (expressions over the decode)
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  (φ : ∀ c, ιc c → ι) (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop) (m : ℕ)

/-- `x = y` as 0/1 -/
def eqE (a b : Ex) : Ex := .ifLt a b (.lit 0) (.ifLt b a (.lit 0) (.lit 1))

theorem eval_eqE (σ : ℕ → ℕ) (a b : Ex) :
    Ex.eval σ A (eqE a b) = if Ex.eval σ A a = Ex.eval σ A b then 1 else 0 := by
  simp only [eqE, Ex.eval]
  by_cases h : Ex.eval σ A a < Ex.eval σ A b
  · simp [h, Nat.ne_of_lt h]
  · by_cases h2 : Ex.eval σ A b < Ex.eval σ A a
    · simp [h, h2, Nat.ne_of_gt h2]
    · have : Ex.eval σ A a = Ex.eval σ A b := by omega
      simp [h, h2, this]

theorem eval_pw {σ : ℕ → ℕ} {x vb vh : ℕ} (hx : x ≠ vb) :
    Ex.eval σ A (nprod x (.var vh) (.var vb)) = σ vb ^ σ vh := by
  rw [eval_nprod]
  simp only [Ex.eval]
  rw [pp_congr (f' := fun _ => σ vb) (fun i _ => by simp [Function.update_apply, hx.symm]), pp_const]

/-- the number of gates -/
def gEx : Ex := .lett (u + 12) I.AE (.add (.mul I.nIE (.var (u + 12))) (offE I I.KE))

theorem eval_gEx {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) :
    Ex.eval σ A (gEx I) = L.gTot N0.A := by
  have g1 : Ag B σ₀ (Function.update σ (u + 12) N0.A) := hσ.upd (by omega) _
  simp only [gEx, eval_lett', I.hA σ₀ hC σ hσ, Ex.eval, I.hnI σ₀ hC _ g1]
  rw [eval_offE I hu hC g1 (n := K) (by simp [Ex.eval, I.hK σ₀ hC _ g1]) le_rfl (by simp)]
  simp [Lay.gTot]


/-- the slot map `φ` as an expression: reads `u+22 = c`, `u+23 = ecc c j`, returns `eι (φ c j)` -/
structure PhiEx (L : Lay ι ιc) (φ : ∀ c, ιc c → ι) (B : ℕ) (Ctx : (ℕ → ℕ) → Prop) (A : ℕ → ℕ → ℕ) (u : ℕ) where
  phiE : Ex
  hphi : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ (c : Fin K) (j : ιc c), σ (u + 22) = c → σ (u + 23) = L.ecc c j →
    Ex.eval σ A phiE = L.eι (φ c j)

variable (Ph : PhiEx L φ B Ctx A u)

theorem ite_range (pp D X : ℕ) :
    (if pp < D then 0 else if pp < D + X then 1 else 0 : ℕ) = if D ≤ pp ∧ pp < D + X then 1 else 0 := by
  split_ifs <;> first | rfl | omega

theorem ite_car (pp X Y j : ℕ) :
    (if 0 < (if pp = X then 1 else 0 : ℕ) then 1 else if 0 < j then (if pp + 1 = Y then 1 else 0) else 0 : ℕ) =
      if pp = X ∨ (0 < j ∧ pp + 1 = Y) then 1 else 0 := by
  split_ifs <;> first | rfl | omega

/-- the parent test of the child in slot `u+6` against the node in slot `u+5` -/
def parEx : Ex := decodeE I (u + 6)
  (.ifLt (.var (u + 21)) (.lit 1) (.lit 0)
    (.ifLt (.var (u + 21)) (.lit 2)
      (.lett (u + 22) (.var (u + 15)) (.lett (u + 23) (.var (u + 16))
        (eqE (.var (u + 5)) (.add (.mul Ph.phiE (.var (u + 12))) (.var (u + 17))))))
      (.ifLt (.var (u + 21)) (.lit 3)
        (.ifLt (.var (u + 5)) (.var (u + 18)) (.lit 0)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 1) (.lit 0)))
        (.ifLt (.var (u + 21)) (.lit 4)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 0)
            (.ifLt (.var (u + 5)) (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.lit 1) (.lit 0)))
          (.ifLt (.lit 0)
            (eqE (.var (u + 5)) (.add (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.mod (.var (u + 16)) (.var (u + 12)))))
            (.lit 1)
            (.ifLt (.lit 0) (.var (u + 16))
              (eqE (.add (.var (u + 5)) (.lit 1)) (.add (.add (.add (.add (.var (u + 18))
                (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12))) (.var (u + 12))) (.var (u + 16))))
              (.lit 0)))))))

variable {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem node_dec {xs : ℕ} (hxs : xs < u + 10) {a : Fin (L.gTot N0.A)} (ha : σ xs = a) (body : Ex) :
    ∃ q : CG ι ιc N0.A, (L.enum N0.A).symm a = q ∧ L.enum N0.A q = a ∧
      ∃ σ' : ℕ → ℕ, Ex.eval σ A (decodeE I xs body) = Ex.eval σ' A body ∧ Ag B σ₀ σ' ∧
      (∀ y, (y < u + 10 ∨ u + 28 ≤ y) → σ' y = σ y) ∧
      σ' (u + 21) = kc (kindOf q) ∧ σ' (u + 16) = (coordOf L q).1 ∧ σ' (u + 17) = (coordOf L q).2 ∧
      (∀ c, idOf q = some c → σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ' (u + 12) = N0.A ∧
        σ' (u + 13) = N0.h ∧ σ' (u + 15) = c.val ∧ σ' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
        σ' (u + 19) = L.nc c ∧ σ' (u + 27) = (NP N0 w c).M ∧ σ' (u + 14) = N0.b) ∧
      (σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 12) = N0.A ∧ σ' (u + 13) = N0.h ∧ σ' (u + 14) = N0.b) := by
  refine ⟨(L.enum N0.A).symm a, rfl, by simp, ?_⟩
  exact eval_decodeE I hu hC hσ hxs body _ (by rw [ha]; simp)

/-- node free count -/
def nfEx : Ex := decodeE I (u + 4)
  (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10))) (.lit 1))

theorem eval_nfEx {a : Fin (L.gTot N0.A)} (ha : σ (u + 4) = a) :
    Ex.eval σ A (nfEx I) =
      Fintype.card ((edgeNetM (w := w) φ F ok m).Free ((L.enum N0.A).symm a)) := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 4) (by omega) ha
    (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10))) (.lit 1))
  unfold nfEx
  rw [h, hq]
  cases q with
  | src i s =>
    simp only [kindOf, kc] at k21
    simp only [Ex.eval, k21, Nat.zero_lt_one, if_true]
    rw [eval_pw (by omega), hg.1, hg.2.2.1, card_free_src]
  | gt c g =>
    have : 1 ≤ σ' (u + 21) := by
      rw [k21]; cases g <;> simp [kindOf, kc]
    have hn : ¬ σ' (u + 21) < 1 := by omega
    simp only [Ex.eval, hn, if_false]
    rw [card_free_gt]


/-- node message count -/
def nmEx : Ex := decodeE I (u + 4)
  (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 11)) (.lit 1)) (.mul (.lit 8) (.var (u + 11)))))

theorem eval_nmEx {a : Fin (L.gTot N0.A)} (ha : σ (u + 4) = a) :
    Ex.eval σ A (nmEx I) =
      Fintype.card ((edgeNetM (w := w) φ F ok m).Msg ((L.enum N0.A).symm a)) := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 4) (by omega) ha
    (.ifLt (.var (u + 21)) (.lit 1) (nprod (u + 91) (.var (u + 13)) (.var (u + 10)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 11)) (.lit 1)) (.mul (.lit 8) (.var (u + 11)))))
  unfold nmEx
  rw [h, hq]
  cases q with
  | src i s =>
    simp only [kindOf, kc] at k21
    simp only [Ex.eval, k21, Nat.zero_lt_one, if_true]
    rw [eval_pw (by omega), hg.1, hg.2.2.1, card_msg_src]
  | gt c g =>
    have hn : ¬ σ' (u + 21) < 1 := by rw [k21]; cases g <;> simp [kindOf, kc]
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g with
    | fa j s =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p11]
      rw [card_msg_fa]
    | mid k =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p11]
      rw [card_msg_mid]
    | ib k =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p11]
      rw [card_msg_ib]
    | car j =>
      have : ¬ σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, p11]
      rw [card_msg_car, pow_add]; ring

/-- message width -/
def wEx : Ex := decodeE I (u + 4)
  (.ifLt (.var (u + 21)) (.lit 1) (.mul (.var (u + 14)) (.var (u + 13)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 27)) (.lit 1)) (.add (.var (u + 27)) (.lit 3))))

theorem eval_wEx {a : Fin (L.gTot N0.A)} (ha : σ (u + 4) = a) :
    Ex.eval σ A (wEx I) = (edgeNetM (w := w) φ F ok m).w ((L.enum N0.A).symm a) := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 4) (by omega) ha
    (.ifLt (.var (u + 21)) (.lit 1) (.mul (.var (u + 14)) (.var (u + 13)))
    (.ifLt (.var (u + 21)) (.lit 4) (.add (.var (u + 27)) (.lit 1)) (.add (.var (u + 27)) (.lit 3))))
  unfold wEx
  rw [h, hq]
  unfold PForced.w
  cases q with
  | src i s =>
    simp only [kindOf, kc] at k21
    simp only [Ex.eval, k21, Nat.zero_lt_one, if_true]
    rw [hg.2.2.2, hg.2.2.1, card_msg_src, clog_src]
  | gt c g =>
    have hn : ¬ σ' (u + 21) < 1 := by rw [k21]; cases g <;> simp [kindOf, kc]
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g with
    | fa j s =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p27]
      rw [card_msg_fa, clog_ring]
    | mid k =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p27]
      rw [card_msg_mid, clog_ring]
    | ib k =>
      have : σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, if_true, p27]
      rw [card_msg_ib, clog_ring]
    | car j =>
      have : ¬ σ' (u + 21) < 4 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, hn, if_false, this, p27]
      rw [card_msg_car, clog_car]


theorem eval_parEx {p c' : Fin (L.gTot N0.A)} (hp : σ (u + 5) = p) (hc : σ (u + 6) = c') :
    Ex.eval σ A (parEx I φ Ph) =
      if (L.enum N0.A).symm p ∈ (edgeNetM (w := w) φ F ok m).pa ((L.enum N0.A).symm c') then 1 else 0 := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hpar, hg⟩ := node_dec I hu hC hσ (xs := u + 6) (by omega) hc
    (.ifLt (.var (u + 21)) (.lit 1) (.lit 0)
    (.ifLt (.var (u + 21)) (.lit 2)
      (.lett (u + 22) (.var (u + 15)) (.lett (u + 23) (.var (u + 16))
        (eqE (.var (u + 5)) (.add (.mul Ph.phiE (.var (u + 12))) (.var (u + 17))))))
      (.ifLt (.var (u + 21)) (.lit 3)
        (.ifLt (.var (u + 5)) (.var (u + 18)) (.lit 0)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 1) (.lit 0)))
        (.ifLt (.var (u + 21)) (.lit 4)
          (.ifLt (.var (u + 5)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.lit 0)
            (.ifLt (.var (u + 5)) (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.lit 1) (.lit 0)))
          (.ifLt (.lit 0)
            (eqE (.var (u + 5)) (.add (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12)))
              (.mod (.var (u + 16)) (.var (u + 12)))))
            (.lit 1)
            (.ifLt (.lit 0) (.var (u + 16))
              (eqE (.add (.var (u + 5)) (.lit 1)) (.add (.add (.add (.add (.var (u + 18))
                (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 12))) (.var (u + 12))) (.var (u + 16))))
              (.lit 0)))))))
  unfold parEx
  rw [h, hq]
  have hp5 : σ' (u + 5) = p := by rw [agr _ (Or.inl (by omega))]; exact hp
  classical
  have hiff : (L.enum N0.A).symm p ∈ (edgeNetM (w := w) φ F ok m).pa q ↔ PA L φ q (p : ℕ) := by
    show (L.enum N0.A).symm p ∈ paC (w := w) φ q ↔ _
    rw [pa_iff (w := w) L φ]; simp
  have hfin : ((if (L.enum N0.A).symm p ∈ (edgeNetM (w := w) φ F ok m).pa q then 1 else 0 : ℕ)) =
      if PA L φ q (p : ℕ) then 1 else 0 := by
    by_cases hP : PA L φ q (p : ℕ)
    · simp [hP, hiff.2 hP]
    · have : ¬ (L.enum N0.A).symm p ∈ (edgeNetM (w := w) φ F ok m).pa q := fun hh => hP (hiff.1 hh)
      simp [hP, this]
  rw [hfin]
  cases q with
  | src i s =>
    simp only [kindOf, kc] at k21
    simp only [Ex.eval, k21, Nat.zero_lt_one, if_true, PA]
    simp
  | gt c g =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hpar c rfl
    have e12 : ∀ y, y ≠ u + 22 → y ≠ u + 23 → Function.update (Function.update σ' (u + 22) (σ' (u + 15))) (u + 23) (σ' (u + 16)) y = σ' y := by
      intro y h1 h2; simp [Function.update_apply, h1, h2]
    cases g with
    | fa j s =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      simp only [coordOf] at j16 s17
      have g1 : Ag B σ₀ (Function.update σ' (u + 22) (σ' (u + 15))) := g'.upd (by omega) _
      have g2 : Ag B σ₀ (Function.update (Function.update σ' (u + 22) (σ' (u + 15))) (u + 23) (σ' (u + 16))) :=
        g1.upd (by omega) _
      have hph := Ph.hphi σ₀ hC _ g2 c j (by simp [p15]) (by simp [j16])
      simp only [Ex.eval, k1, Nat.lt_irrefl, if_false, show (1 : ℕ) < 2 by norm_num, if_true]
      have e16 : Function.update σ' (u + 22) (σ' (u + 15)) (u + 16) = σ' (u + 16) := by
        simp [Function.update_apply]
      rw [e16, eval_eqE]
      simp only [Ex.eval]
      simp only [hph]
      have v5 : Function.update (Function.update σ' (u + 22) (σ' (u + 15))) (u + 23) (σ' (u + 16)) (u + 5) = p := by
        simp [Function.update_apply, hp5]
      have v12 : Function.update (Function.update σ' (u + 22) (σ' (u + 15))) (u + 23) (σ' (u + 16)) (u + 12) = N0.A := by
        simp [Function.update_apply, p12]
      have v17 : Function.update (Function.update σ' (u + 22) (σ' (u + 15))) (u + 23) (σ' (u + 16)) (u + 17) = s := by
        simp [Function.update_apply, s17]
      simp only [v5, v12, v17]
      simp only [PA]
      by_cases hh : (p : ℕ) = L.eι (φ c j) * N0.A + s <;> simp [hh]
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, k1, p18, p19, p12, hp5, PA]
      norm_num
      refine (ite_range (p : ℕ) (L.nι * N0.A + L.off N0.A ↑c) (L.nc c * N0.A)).trans ?_
      congr
    | ib k =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      simp only [Ex.eval, k1, p18, p19, p12, hp5, PA]
      norm_num
      refine (ite_range (p : ℕ) (L.nι * N0.A + L.off N0.A ↑c + L.nc c * N0.A) N0.A).trans ?_
      congr
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      simp only [coordOf] at j16
      simp only [Ex.eval, eval_eqE, k1, p18, p19, p12, hp5, j16, PA]
      norm_num
      refine (ite_car (p : ℕ) _ _ (j : ℕ)).trans ?_
      congr

end
end ECDLP.L73
end
