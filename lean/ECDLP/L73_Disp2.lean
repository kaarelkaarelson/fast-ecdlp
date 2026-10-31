import ECDLP.L73_Disp1
import ECDLP.L73_Car
import ECDLP.L73_Src
import ECDLP.L73_Child

/-!
# L73 / Disp2: the dispatch of `outE` / `wtE` by gate kind, and the `PEx` of the edge network
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- the three gate kinds supplied by L74 (fa, mid) and L75 (ib) -/
structure Kinds where
  fa : GateKindPEx (w := w) m L .fa (L.enum N0.A) u X
  mid : GateKindPEx (w := w) m L .mid (L.enum N0.A) u X
  ib : GateKindPEx (w := w) m L .ib (L.enum N0.A) u X

/-- coordinate of the child within its kind: `child - (block start + nc*A [+ A [+ A]])` -/
def dqE : Ex :=
  let base : Ex := .add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))
  .ifLt (.var (u + 21)) (.lit 1) (.lit 0)
    (.ifLt (.var (u + 21)) (.lit 2) (.sub (.var (u + 6)) base)
      (.ifLt (.var (u + 21)) (.lit 3) (.sub (.var (u + 6)) (.add base (.var (u + 12))))
        (.ifLt (.var (u + 21)) (.lit 4) (.sub (.var (u + 6)) (.add base (.add (.var (u + 12)) (.var (u + 12))))) (.lit 0))))

/-- index oracles of the car gate (pure in the node slot `u+5`) -/
def carJ : Ex := decodeE I (u + 5) (.var (u + 16))
def carPC : Ex := .sub (.var (u + 5)) (.lit 1)
def carPIB : Ex := decodeE I (u + 5)
  (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.add (.var (u + 12)) (.mod (.var (u + 16)) (.var (u + 12)))))

def carOutX : Ex := carOutL' X (u + 10) (u + 11) (u + 92) (u + 93) (u + 94) (carJ I) (carPC (u := u)) (carPIB I)

/-- the source/check gates: the weight expression of a source node (reads the digits of its free value from the
setting code in `u+7`; hypothesis of the dispatch, discharged from the instance expressions) -/
structure SrcWt (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u) where
  srcE : Ex
  hsrc : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (i : ι) (s : Fin N0.A)
    (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a)),
    (L.enum N0.A).symm a = CG.src i s → σ (u + 4) = a →
    σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z →
    σ (u + 10) = 2 ^ N0.b → σ (u + 12) = N0.A → σ (u + 13) = N0.h → σ (u + 14) = N0.b →
    σ (u + 16) = L.eι i → σ (u + 17) = s →
    Ex.eval σ A srcE = if (edgeNetM (w := w) φ F ok m).W ((L.enum N0.A).symm a) z = 1 then 1 else 0

def carWX : Ex := carWL' X (u + 10) (u + 11) (u + 92) (u + 28) (u + 93) (u + 94) (carJ I) (carPC (u := u)) (carPIB I)

def wtChain (Sw : SrcWt (w := w) X) : Ex :=
  .ifLt (.var (u + 21)) (.lit 1) Sw.srcE
    (.ifLt (.var (u + 21)) (.lit 4) (.lit 1)
      (.lett (u + 28) (.mul (.var (u + 12)) (.var (u + 12))) (carWX I X)))

def wtEx (Sw : SrcWt (w := w) X) : Ex := decodeE I (u + 4) (wtChain I X Sw)

/-- **the message code expression**: decode the node (slot `u+5`), then dispatch on its kind -/
def outChain (Kd : Kinds (w := w) (m := m) X) : Ex :=
    (.ifLt (.var (u + 21)) (.lit 1) (.var (u + 7))
      (.ifLt (.var (u + 21)) (.lit 2) Kd.fa.outE
        (.ifLt (.var (u + 21)) (.lit 3) Kd.mid.outE
          (.ifLt (.var (u + 21)) (.lit 4) Kd.ib.outE (carOutX I X)))))

def outBody (Kd : Kinds (w := w) (m := m) X) : Ex := .lett (u + 20) (dqE (u := u)) (outChain I X Kd)

def outEx (Kd : Kinds (w := w) (m := m) X) : Ex := decodeE I (u + 5) (outBody I X Kd)

section oracles
variable {σ₀ σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem eval_carJ {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (ha : σ (u + 5) = a) :
    Ex.eval σ A (carJ I) = j.val := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 5) (by omega) ha (.var (u + 16))
  unfold carJ
  rw [h]
  have hq' : q = CG.gt c (Gate.car j) := hq.symm.trans hka
  subst hq'
  simp only [Ex.eval, j16, coordOf]

theorem eval_carPC {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (ha : σ (u + 5) = a) (h0 : 0 < j.val) :
    Ex.eval σ A (carPC (u := u)) = (L.enum N0.A (CG.gt c (Gate.car ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2⟩)) : ℕ) := by
  have hq : a = L.enum N0.A (CG.gt c (Gate.car j)) := by rw [← hka]; simp
  simp only [carPC, Ex.eval, ha, hq, Lay.enum_gt, Lay.gateE_car]
  omega

theorem eval_carPIB {a : Fin (L.gTot N0.A)} {c : Fin K} {j : Fin (N0.A * N0.A)}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j)) (ha : σ (u + 5) = a) :
    Ex.eval σ A (carPIB I) =
      (L.enum N0.A (CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)) : ℕ) := by
  obtain ⟨q, hq, -, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 5) (by omega) ha
    (.add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.add (.var (u + 12)) (.mod (.var (u + 16)) (.var (u + 12)))))
  unfold carPIB
  rw [h]
  have hq' : q = CG.gt c (Gate.car j) := hq.symm.trans hka
  subst hq'
  obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
  simp only [Ex.eval, j16, coordOf, p18, p19, p12, Lay.enum_gt, Lay.gateE_ib]
  omega


theorem kst_of {a b : Fin (L.gTot N0.A)} {q : CG ι ιc N0.A} (hq : (L.enum N0.A).symm a = q) {σ' σ2 : ℕ → ℕ}
    (e2 : ∀ y, y ≠ u + 20 → σ2 y = σ' y) (s5 : σ2 (u + 5) = a) (s6 : σ2 (u + 6) = b)
    (hp : ∀ c, idOf q = some c → σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ' (u + 12) = N0.A ∧
        σ' (u + 13) = N0.h ∧ σ' (u + 15) = c.val ∧ σ' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
        σ' (u + 19) = L.nc c ∧ σ' (u + 27) = (NP N0 w c).M ∧ σ' (u + 14) = N0.b)
    (hb14 : σ' (u + 14) = N0.b) (j16 : σ' (u + 16) = (coordOf L q).1) (s17 : σ' (u + 17) = (coordOf L q).2)
    (hdq : σ2 (u + 20) = childCoord ((L.enum N0.A).symm b)) :
    KSt (w := w) L σ2 u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) where
  ha := s5
  hb := s6
  hpar := fun c hc => by
    rw [hq] at hc
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c hc
    exact ⟨by rw [e2 _ (by omega)]; exact p10, by rw [e2 _ (by omega)]; exact p11, by rw [e2 _ (by omega)]; exact p12,
      by rw [e2 _ (by omega)]; exact p13, by rw [e2 _ (by omega)]; exact p15, by rw [e2 _ (by omega)]; exact p18,
      by rw [e2 _ (by omega)]; exact p19⟩
  hM := fun c hc => by
    rw [hq] at hc
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c hc
    rw [e2 _ (by omega)]; exact p27
  hbits := by rw [e2 _ (by omega)]; exact hb14
  hj := by rw [hq, e2 _ (by omega)]; exact j16
  hs := by rw [hq, e2 _ (by omega)]; exact s17
  hq := hdq

variable (Kd : Kinds (w := w) (m := m) X)

theorem hout_ex (a b : Fin (L.gTot N0.A)) (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (hAB : (L.enum N0.A).symm a ∈ (edgeNetM (w := w) φ F ok m).pa ((L.enum N0.A).symm b))
    (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) (hz : σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z) :
    Ex.eval σ A (outEx I X Kd) =
      ec (ι := ι) (ιc := ιc) (w := w) ((L.enum N0.A).symm a)
        ((edgeNetM (w := w) φ F ok m).out ((L.enum N0.A).symm a) z ((L.enum N0.A).symm b)) := by
  obtain ⟨q, hq, hqa, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 5) (by omega) ha
    (outBody I X Kd)
  unfold outEx
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
  have e0 : Ex.eval σ' A (outBody I X Kd) = Ex.eval σ2 A (outChain I X Kd) := rfl
  rw [e0]
  have hb6' : σ' (u + 6) = b := by rw [agr _ (Or.inl (by omega))]; exact hb
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    have hs : (L.enum N0.A).symm a = CG.src i s' := hq
    have hL : Ex.eval σ2 A (outChain I X Kd) = σ2 (u + 7) := by
      simp only [outChain, Ex.eval, s21, k21, Nat.zero_lt_one, if_true]
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
      have hL : Ex.eval σ2 A (outChain I X Kd) = Ex.eval σ2 A Kd.fa.outE := by
        simp only [outChain, Ex.eval, s21, k1]
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
      have hL : Ex.eval σ2 A (outChain I X Kd) = Ex.eval σ2 A Kd.mid.outE := by
        simp only [outChain, Ex.eval, s21, k1]
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
      have hL : Ex.eval σ2 A (outChain I X Kd) = Ex.eval σ2 A Kd.ib.outE := by
        simp only [outChain, Ex.eval, s21, k1]
        simp
      rw [hL]
      exact Kd.ib.hout σ₀ hC σ2 g2 a b z (by rw [hka]; rfl) hAB hkst s7
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      have hL : Ex.eval σ2 A (outChain I X Kd) = Ex.eval σ2 A (carOutX I X) := by
        simp only [outChain, Ex.eval, s21, k1]
        simp
      rw [hL]
      have q10 : σ2 (u + 10) = 2 ^ (NP N0 w c).b := by rw [e2 _ (by omega)]; exact p10
      have q11 : σ2 (u + 11) = 2 ^ (NP N0 w c).M := by rw [e2 _ (by omega)]; exact p11
      exact car_hout' X hu hC g2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hka q10 q11
        (fun σ'' g'' h'' => eval_carJ I hu hC g'' hka h'')
        (fun σ'' g'' h'' h0 => eval_carPC hu hC g'' hka h'' h0)
        (fun σ'' g'' h'' => eval_carPIB I hu hC g'' hka h'') z s7 s5


theorem W_fa_q (c : Fin K) (j : ιc c) (s : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.fa j s))
    (z : (edgeNetM (w := w) φ F ok m).S q) : (edgeNetM (w := w) φ F ok m).W q z = 1 := by
  subst hq; show (Int.castRingHom (ZMod m)) 1 = 1; exact map_one _
theorem W_mid_q (c : Fin K) (k : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.mid k))
    (z : (edgeNetM (w := w) φ F ok m).S q) : (edgeNetM (w := w) φ F ok m).W q z = 1 := by
  subst hq; show (Int.castRingHom (ZMod m)) 1 = 1; exact map_one _
theorem W_ib_q (c : Fin K) (k : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.ib k))
    (z : (edgeNetM (w := w) φ F ok m).S q) : (edgeNetM (w := w) φ F ok m).W q z = 1 := by
  subst hq; show (Int.castRingHom (ZMod m)) 1 = 1; exact map_one _

variable (Sw : SrcWt (w := w) X)

theorem hwt_ex (hm1 : 1 < m) (a : Fin (L.gTot N0.A)) (z : (edgeNetM (w := w) φ F ok m).S ((L.enum N0.A).symm a))
    (ha : σ (u + 4) = a) (hz : σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z) :
    Ex.eval σ A (wtEx I X Sw) =
      if (edgeNetM (w := w) φ F ok m).W ((L.enum N0.A).symm a) z = 1 then 1 else 0 := by
  obtain ⟨q, hq, hqa, σ', h, g', agr, k21, j16, s17, hp, hg⟩ := node_dec I hu hC hσ (xs := u + 4) (by omega) ha
    (wtChain I X Sw)
  unfold wtEx
  rw [h]
  have z' : σ' (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z := by
    rw [agr _ (Or.inl (by omega))]; exact hz
  have a' : σ' (u + 4) = a := by rw [agr _ (Or.inl (by omega))]; exact ha
  cases q with
  | src i s' =>
    simp only [kindOf, kc] at k21
    have hs : (L.enum N0.A).symm a = CG.src i s' := hq
    have hL : Ex.eval σ' A (wtChain I X Sw) = Ex.eval σ' A Sw.srcE := by
      simp only [wtChain, Ex.eval, k21, Nat.zero_lt_one, if_true]
    rw [hL]
    simp only [coordOf] at j16 s17
    exact Sw.hsrc σ₀ hC σ' g' a i s' z hs a' z' hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 j16 s17
  | gt c g' =>
    obtain ⟨p10, p11, p12, p13, p15, p18, p19, p27, p14⟩ := hp c rfl
    cases g' with
    | fa j s' =>
      have k1 : σ' (u + 21) = 1 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain I X Sw) = 1 := by
        simp only [wtChain, Ex.eval, k1]; simp
      rw [hL, W_fa_q hu hC hσ c j s' _ hq z]; simp
    | mid k =>
      have k1 : σ' (u + 21) = 2 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain I X Sw) = 1 := by
        simp only [wtChain, Ex.eval, k1]; simp
      rw [hL, W_mid_q hu hC hσ c k _ hq z]; simp
    | ib j =>
      have k1 : σ' (u + 21) = 3 := by rw [k21]; simp [kindOf, kc]
      have hL : Ex.eval σ' A (wtChain I X Sw) = 1 := by
        simp only [wtChain, Ex.eval, k1]; simp
      rw [hL, W_ib_q hu hC hσ c j _ hq z]; simp
    | car j =>
      have k1 : σ' (u + 21) = 4 := by rw [k21]; simp [kindOf, kc]
      have hka : (L.enum N0.A).symm a = CG.gt c (Gate.car j) := hq
      set σ3 := Function.update σ' (u + 28) (σ' (u + 12) * σ' (u + 12)) with h3
      have g3 : Ag B σ₀ σ3 := g'.upd (by omega) _
      have e3 : ∀ y, y ≠ u + 28 → σ3 y = σ' y := fun y hy => by simp [h3, Function.update_apply, hy]
      have hL : Ex.eval σ' A (wtChain I X Sw) = Ex.eval σ3 A (carWX I X) := by
        simp only [wtChain, Ex.eval, k1]
        simp
        rfl
      rw [hL]
      have q10 : σ3 (u + 10) = 2 ^ (NP N0 w c).b := by rw [e3 _ (by omega)]; exact p10
      have q11 : σ3 (u + 11) = 2 ^ (NP N0 w c).M := by rw [e3 _ (by omega)]; exact p11
      have q28 : σ3 (u + 28) = (NP N0 w c).A * (NP N0 w c).A := by
        simp [h3, p12]; rfl
      exact car_hwt' X hu hC g3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) hm1 hka q10 q11 q28
        (fun σ'' g'' h'' => eval_carJ I hu hC g'' hka h'')
        (fun σ'' g'' h'' h0 => eval_carPC hu hC g'' hka h'' h0)
        (fun σ'' g'' h'' => eval_carPIB I hu hC g'' hka h'') z (by rw [e3 _ (by omega)]; exact z')
        (by rw [e3 _ (by omega)]; exact a')

end oracles
end
end ECDLP.L73
end
