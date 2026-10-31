import ECDLP.L73_Iface
import ECDLP.L74_MidB

/-!
# L74 / Kind: the L73 `GateKindPEx` instances for the fa and mid gate kinds

The local expressions read only L73's decode slots (`KSt`) plus the instance expressions (oracles) `phiE`
(= `eι (φ c j)` from the slots `u+15 = c`, `u+16 = dj`), and for mid `nE, epsE, lE, rE` (the form of identity `c`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73

section node
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- parameters of the cluster from the decode slots: `q = 2^M + 1` in `u+30`, `w = M / (A*A/2)` in `u+31` -/
def kParams (body : Ex) : Ex :=
  .lett (u + 30) (.add (.var (u + 11)) (.lit 1))
    (.lett (u + 31) (.div (.var (u + 27)) (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))) body)

theorem kParams_eval (σ : ℕ → ℕ) (body : Ex) :
    Ex.eval σ A (kParams (u := u) body) = Ex.eval (Function.update (Function.update σ (u + 30) (σ (u + 11) + 1)) (u + 31)
      (σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2))) A body := by
  simp only [kParams, Ex.eval]
  rw [Function.update_of_ne (show u + 27 ≠ u + 30 by omega), Function.update_of_ne (show u + 12 ≠ u + 30 by omega)]

/-- the fa expression: `faOutL` with the slots of the decode state -/
def faKindE (phiE : Ex) : Ex :=
  kParams (u := u) (faOutL X (u + 30) (u + 12) (u + 13) (u + 10) (u + 31) (u + 32) (u + 33) (u + 34) (u + 35) (u + 36)
    (.var (u + 17)) (.var (u + 20)) (.add (.mul phiE (.var (u + 12))) (.var (u + 17))))

theorem NP_w_eq (c : Fin K) : (NP N0 w c).M / ((NP N0 w c).A * (NP N0 w c).A / 2) = (NP N0 w c).w := by
  have h := (NP N0 w c).hA
  have h2 : ((NP N0 w c).A * (NP N0 w c).A) / 2 = 2 ^ (NP N0 w c).k := by
    rw [h, pow_succ]; omega
  rw [h2]
  show 2 ^ (NP N0 w c).k * (NP N0 w c).w / 2 ^ (NP N0 w c).k = _
  exact Nat.mul_div_cancel_left _ (by positivity)

/-- **The fa gate kind as an instance of L73's `GateKindPEx`.**  Extra hypotheses: `B <= u`, `M >= 1` for every identity, and
the instance expression `phiE` computing `eι (φ c j)` from the slots `u+15 = c`, `u+16 = ecc c j`. -/
def faKind (hu : B ≤ u) (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (phiE : Ex)
    (hphi : ∀ (σ' : ℕ → ℕ) (c : Fin K) (j : ιc c), σ' (u + 15) = c.val → σ' (u + 16) = (L.ecc c j : ℕ) →
      Ex.eval σ' A phiE = (L.eι (φ c j) : ℕ)) :
    GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L .fa (L.enum N0.A) u X where
  outE := faKindE (m := m) (φ := φ) (F := F) (ok := ok) L X phiE
  hout := by
    intro σ₀ hC σ hσ a b z hk hpa hKS hz
    obtain ⟨c, j, s, hka⟩ : ∃ (c : Fin K) (j : ιc c) (s : Fin N0.A), (L.enum N0.A).symm a = CG.gt c (Gate.fa j s) := by
      cases h : (L.enum N0.A).symm a with
      | src i s => rw [h] at hk; simp [kindOf] at hk
      | gt c g =>
        cases g with
        | fa j s => exact ⟨c, j, s, rfl⟩
        | mid _ => rw [h] at hk; simp [kindOf] at hk
        | ib _ => rw [h] at hk; simp [kindOf] at hk
        | car _ => rw [h] at hk; simp [kindOf] at hk
    have hpa' : (L.enum N0.A).symm a ∈ paC (w := w) φ ((L.enum N0.A).symm b) := hpa
    have hpa'' := hpa'
    rw [hka] at hpa''
    obtain ⟨kk, hkk⟩ := fa_child (w := w) φ c j s hpa''
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hKS.hpar c (by simp [idOf, hka])
    have hM' := hKS.hM c (by simp [idOf, hka])
    have hj := hKS.hj
    have hs' := hKS.hs
    have hq := hKS.hq
    simp only [hka, coordOf] at hj hs'
    simp only [hkk, childCoord] at hq
    show Ex.eval σ A (faKindE (m := m) (φ := φ) (F := F) (ok := ok) L X phiE) = _
    unfold faKindE
    rw [kParams_eval]
    set σ2 := Function.update (Function.update σ (u + 30) (σ (u + 11) + 1)) (u + 31)
      (σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2)) with hσ2
    have g2 : Ag B σ₀ σ2 := (hσ.upd (by omega) _).upd (by omega) _
    have e5 : σ2 (u + 5) = a := by
      rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hKS.ha
    have e6 : σ2 (u + 6) = b := by
      rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hKS.hb
    have e7 : σ2 (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z := by
      rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz
    have o : ∀ y, y ≠ u + 30 → y ≠ u + 31 → σ2 y = σ y := fun y h1 h2 => by
      rw [hσ2, Function.update_of_ne h2, Function.update_of_ne h1]
    have agσ : ∀ σ' : ℕ → ℕ, Agr u (u + 32) σ2 σ' → ∀ y, u + 2 < y → y < u + 30 → σ' y = σ y := fun σ' hσ' y h1 h2 => by
      rw [hσ' y (Or.inr ⟨h1, by omega⟩), o y (by omega) (by omega)]
    exact fa_hout (w := w) (φ := φ) (F := F) (ok := ok) X hu hC g2 (vq := u + 30) (vA := u + 12) (vh := u + 13)
      (vb := u + 10) (vw := u + 31) (vs := u + 32) (vk := u + 33) (vcd := u + 34) (x1 := u + 35) (xp := u + 36)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hM1 c) hka (by simp [hσ2, hp2])
      (by rw [o _ (by omega) (by omega), hp3]; rfl) (by rw [o _ (by omega) (by omega), hp4]; rfl)
      (by rw [o _ (by omega) (by omega), hp1]) (by rw [hσ2, Function.update_self, hM', hp3]; exact NP_w_eq c)
      hpa'
      (fun σ' hσ' => by simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hs')
      (fun σ' hσ' kk' c' hkk' => by
        simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega), hq]
        have := hkk.symm.trans hkk'
        cases this; rfl)
      (fun σ' hσ' => by
        simp only [Ex.eval]
        rw [hphi σ' c j (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5)
          (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hj), agσ σ' hσ' _ (by omega) (by omega),
          agσ σ' hσ' _ (by omega) (by omega), hp3, hs', Lay.enum_src])
      z e7 e5 e6


/-- extra parameter slot of a mid node: `Ei = w * (A*A - 1)` in `u+37` (the root exponent of `ωi`) -/
def kParams2 (body : Ex) : Ex :=
  kParams (u := u) (.lett (u + 37) (.mul (.var (u + 31)) (.sub (.mul (.var (u + 12)) (.var (u + 12))) (.lit 1))) body)

/-- global index of the node `fa (code i, s)` of the block: `dbase + min(i, nc-1) * A + s` (slots `vI = u+45`, `vS = u+46`) -/
def pfaKE : Ex :=
  .add (.add (.var (u + 18)) (.mul (.ifLt (.sub (.var (u + 19)) (.lit 1)) (.var (u + 45))
    (.sub (.var (u + 19)) (.lit 1)) (.var (u + 45))) (.var (u + 12)))) (.var (u + 46))

/-- the mid expression -/
def midKindE (nE epsE lE rE : Ex) : Ex :=
  kParams2 (u := u) (midOutL X (u + 30) (u + 12) (u + 37) (u + 31) (u + 40) (u + 41) (u + 42) (u + 43) (u + 44)
    (u + 45) (u + 46) (.var (u + 16)) (.var (u + 20)) nE epsE lE rE (pfaKE (u := u)))


/-- **The mid gate kind as an instance of L73's `GateKindPEx`.**  Extra hypotheses: `B <= u`, `M >= 1`, `nc c >= 1` (so a
clamped decode of form-slot codes exists), the free-variable facts of `X`'s node expressions, and the instance expressions
`nE epsE lE rE` of the form of identity `c` (slot `u+15 = c`; `lE, rE` return the `ecc`-codes `ecc c (F c).l t`). -/
def midKind (hu : B ≤ u) (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c)
    (hXnf : Ex.FV (· < u + 10) X.nfE) (hXnm : Ex.FV (· < u + 10) X.nmE) (hXpar : Ex.FV (· < u + 10) X.parE)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ (σ' : ℕ → ℕ) (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ (σ' : ℕ → ℕ) (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ (σ' : ℕ → ℕ) (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ (σ' : ℕ → ℕ) (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ)) :
    GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L .mid (L.enum N0.A) u X where
  outE := midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE
  hout := by
    intro σ₀ hC σ hσ a b z hk hpa hKS hz
    obtain ⟨c, k, hka⟩ : ∃ (c : Fin K) (k : Fin N0.A), (L.enum N0.A).symm a = CG.gt c (Gate.mid k) := by
      cases h : (L.enum N0.A).symm a with
      | src i s => rw [h] at hk; simp [kindOf] at hk
      | gt c g =>
        cases g with
        | fa _ _ => rw [h] at hk; simp [kindOf] at hk
        | mid k => exact ⟨c, k, rfl⟩
        | ib _ => rw [h] at hk; simp [kindOf] at hk
        | car _ => rw [h] at hk; simp [kindOf] at hk
    have hpa' : (L.enum N0.A).symm a ∈ paC (w := w) φ ((L.enum N0.A).symm b) := hpa
    have hpa'' := hpa'
    rw [hka] at hpa''
    obtain ⟨j₁, hj₁⟩ := mid_child (w := w) φ c k hpa''
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hKS.hpar c (by simp [idOf, hka])
    have hM' := hKS.hM c (by simp [idOf, hka])
    have hj := hKS.hj
    have hs' := hKS.hs
    have hq := hKS.hq
    simp only [hka, coordOf] at hj hs'
    simp only [hj₁, childCoord] at hq
    show Ex.eval σ A (midKindE (m := m) (φ := φ) (F := F) (ok := ok) L X nE epsE lE rE) = _
    unfold midKindE kParams2
    rw [kParams_eval]
    set σ2 := Function.update (Function.update σ (u + 30) (σ (u + 11) + 1)) (u + 31)
      (σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2)) with hσ2
    have g2 : Ag B σ₀ σ2 := (hσ.upd (by omega) _).upd (by omega) _
    have hw2 : σ2 (u + 31) = (NP N0 w c).w := by rw [hσ2, Function.update_self, hM', hp3]; exact NP_w_eq c
    have hA2 : σ2 (u + 12) = N0.A := by
      rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hp3]
    simp only [Ex.eval]
    set σ3 := Function.update σ2 (u + 37) (σ2 (u + 31) * (σ2 (u + 12) * σ2 (u + 12) - 1)) with hσ3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have o : ∀ y, y ≠ u + 30 → y ≠ u + 31 → y ≠ u + 37 → σ3 y = σ y := fun y h1 h2 h3 => by
      rw [hσ3, Function.update_of_ne h3, hσ2, Function.update_of_ne h2, Function.update_of_ne h1]
    have e5 : σ3 (u + 5) = a := by rw [o _ (by omega) (by omega) (by omega)]; exact hKS.ha
    have e6 : σ3 (u + 6) = b := by rw [o _ (by omega) (by omega) (by omega)]; exact hKS.hb
    have e7 : σ3 (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m (L.enum N0.A) a z := by
      rw [o _ (by omega) (by omega) (by omega)]; exact hz
    have agσ : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → ∀ y, u + 2 < y → y < u + 30 → σ' y = σ y := fun σ' hσ' y h1 h2 => by
      rw [hσ' y (Or.inr ⟨h1, by omega⟩), o y (by omega) (by omega) (by omega)]
    have hdec : ∀ i : ℕ, ∃ x : ιc c, x = (L.ecc c).symm ⟨min i (L.nc c - 1), by have := hne c; omega⟩ := fun i => ⟨_, rfl⟩
    let dec : ℕ → ιc c := fun i => (L.ecc c).symm ⟨min i (L.nc c - 1), by have := hne c; omega⟩
    have hdec_ecc : ∀ x : ιc c, dec (L.ecc c x : ℕ) = x := by
      intro x
      have h1 : min (L.ecc c x : ℕ) (L.nc c - 1) = (L.ecc c x : ℕ) :=
        Nat.min_eq_left (by have := (L.ecc c x).2; omega)
      show (L.ecc c).symm ⟨min (L.ecc c x : ℕ) (L.nc c - 1), _⟩ = x
      rw [Equiv.symm_apply_eq]
      exact Fin.ext h1
    have hei3 : σ3 (u + 37) = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
      rw [hσ3, Function.update_self, hw2, hA2]
      rw [show N0.A * N0.A = 2 ^ ((NP N0 w c).k + 1) from (NP N0 w c).hA]
    have hfvp : Ex.FV (fun y => y < u + 42 ∨ y = u + 45 ∨ y = u + 46) (pfaKE (u := u)) := by
      simp [pfaKE, Ex.FV]
    have hpf : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → ∀ (i s : ℕ) (hs : s < N0.A), σ' (u + 45) = i → σ' (u + 46) = s →
        Ex.eval σ' A (pfaKE (u := u)) = (L.enum N0.A (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)) : ℕ) := by
      intro σ' hσ' i s hs hi hs2
      have e18 : σ' (u + 18) = L.nι * N0.A + L.off N0.A c := by
        rw [agσ σ' hσ' (u + 18) (by omega) (by omega)]; exact hp6
      have e19 : σ' (u + 19) = L.nc c := by
        rw [agσ σ' hσ' (u + 19) (by omega) (by omega)]; exact hp7
      have e12 : σ' (u + 12) = N0.A := by
        rw [agσ σ' hσ' (u + 12) (by omega) (by omega)]; exact hp3
      simp only [pfaKE, Ex.eval, e18, e19, e12, hi, hs2]
      rw [Lay.enum_gt, Lay.gateE_fa]
      have hl1 : ((L.ecc c) (dec i) : ℕ) = min i (L.nc c - 1) := by
        show (((L.ecc c) ((L.ecc c).symm ⟨min i (L.nc c - 1), _⟩)) : ℕ) = _
        rw [Equiv.apply_symm_apply]
      rw [hl1]
      have : (if L.nc c - 1 < i then L.nc c - 1 else i) = min i (L.nc c - 1) := by
        split_ifs with h <;> omega
      rw [this]
      show L.nι * N0.A + L.off N0.A c + min i (L.nc c - 1) * N0.A + s = _
      ring
    exact mid_hout (w := w) (φ := φ) (F := F) (ok := ok) X hu hC g3 (vq := u + 30) (vA := u + 12) (vei := u + 37)
      (vw := u + 31) (vK := u + 40) (vJ := u + 41) (x1 := u + 42) (x2 := u + 43) (x3 := u + 44) (vI := u + 45)
      (vS := u + 46) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (a := a) (b := b) (c := c) (k := k)
      (hM1 c) hka (by simp [hσ3, hσ2, hp2])
      (by rw [o _ (by omega) (by omega) (by omega), hp3]; rfl)
      hei3 (by rw [hσ3, Function.update_of_ne (by omega)]; exact hw2) hpa' (kE := .var (u + 16)) (j1E := .var (u + 20))
      (nE := nE) (epsE := epsE) (lE := lE) (rE := rE) (pfaE := pfaKE (u := u)) dec
      (fun σ' hσ' => by simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hj)
      (fun σ' hσ' c' j₁' hj' => by
        simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega), hq]
        have := hj₁.symm.trans hj'
        cases this; rfl)
      hnFV hεFV hlFV hrFV hfvp hXnf hXnm hXpar
      (fun σ' hσ' => by rw [hn σ' c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5)])
      (fun σ' hσ' t ht => heps σ' c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht)
      (fun σ' hσ' t ht => by
        rw [hl σ' c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht]; exact hdec_ecc _)
      (fun σ' hσ' t ht => by
        rw [hr σ' c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht]; exact hdec_ecc _)
      (fun σ' hσ' i s hs hi hs2 => hpf σ' hσ' i s hs hi hs2)
      z e7 e5 e6

end node
end ECDLP.L74
end
