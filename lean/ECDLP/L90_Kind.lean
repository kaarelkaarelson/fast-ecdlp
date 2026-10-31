import ECDLP.L90_Mid
import ECDLP.L79_AsmC

/-!
# L90 / Kind: `midKindC'` with `hne` weakened to `0 < nc c ∨ (F c).n = 0`
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L79
open ECDLP.L74 (fa_child midKindE kParams kParams2 kParams_eval NP_w_eq pfaKE mid_child Agr)

section node
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

/-- the mid kind with `hne` weakened: an identity with no used slot must have no term -/
def midKindC' (hu : B ≤ u) (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c ∨ (F c).n = 0)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ)) :
    GateKindPEx (w := w) (φ := φ) (F := F) (ok := ok) m L .mid (L.enum N0.A) u X where
  outE := midKindEC (u := u) nE epsE lE rE
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
    show Ex.eval σ A (midKindEC (u := u) nE epsE lE rE) = _
    unfold midKindEC kParams2
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
    have hei3 : σ3 (u + 37) = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
      rw [hσ3, Function.update_self, hw2, hA2]
      rw [show N0.A * N0.A = 2 ^ ((NP N0 w c).k + 1) from (NP N0 w c).hA]
    rcases hne c with hpos | hn0
    · have hdec : ∀ i : ℕ, ∃ x : ιc c, x = (L.ecc c).symm ⟨min i (L.nc c - 1), by omega⟩ := fun i => ⟨_, rfl⟩
      let dec : ℕ → ιc c := fun i => (L.ecc c).symm ⟨min i (L.nc c - 1), by omega⟩
      have hdec_ecc : ∀ x : ιc c, dec (L.ecc c x : ℕ) = x := by
        intro x
        have h1 : min (L.ecc c x : ℕ) (L.nc c - 1) = (L.ecc c x : ℕ) :=
          Nat.min_eq_left (by have := (L.ecc c x).2; omega)
        show (L.ecc c).symm ⟨min (L.ecc c x : ℕ) (L.nc c - 1), _⟩ = x
        rw [Equiv.symm_apply_eq]
        exact Fin.ext h1
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
      have hDfvC : Ex.FV (fun y => y < u + 42 ∨ y = u + 1) (digCmid u) := by
        simp only [digCmid, nprod, Ex.FV]
        repeat' first
          | trivial
          | omega
          | (simp; done)
          | apply And.intro
      exact mid_houtD (w := w) (φ := φ) (F := F) (ok := ok) hu hC g3 (digCmid u) (vq := u + 30) (vA := u + 12) (vei := u + 37)
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
        hnFV hεFV hlFV hrFV hfvp z e7 hDfvC
        (fun τ gτ hτ kk i s hkk hτu hτ1 hτ2 => by
          have h11 : τ (u + 11) = 2 ^ (NP N0 w c).M := by rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega) (by omega)]; exact hp2
          have h18 : τ (u + 18) = L.nι * N0.A + L.off N0.A c := by rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega) (by omega)]; exact hp6
          rw [digCmid_eq_digE L X hu hC gτ hka hkk hτu hτ1 h11 h18]
          exact eval_digE_pm X hu hC gτ (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := kk) (p := CG.gt c (Gate.fa i s))
            hτu hτ1 hkk (by rw [hka]; exact ECDLP.L74.mid_fa_mem (w := w) φ c k i s) z hτ2)
        (fun σ' hσ' => by rw [hn σ₀ hC σ' (ag_of_agr hu g3 hσ') c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5)])
        (fun σ' hσ' t ht => heps σ₀ hC σ' (ag_of_agr hu g3 hσ') c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht)
        (fun σ' hσ' t ht => by
          rw [hl σ₀ hC σ' (ag_of_agr hu g3 hσ') c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht]; exact hdec_ecc _)
        (fun σ' hσ' t ht => by
          rw [hr σ₀ hC σ' (ag_of_agr hu g3 hσ') c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5) t ht]; exact hdec_ecc _)
        (fun σ' hσ' i s hs hi hs2 => hpf σ' hσ' i s hs hi hs2)
        e5 e6
    · exact mid_hout0 (w := w) (φ := φ) (F := F) (ok := ok) hu hC g3 (digCmid u) (vq := u + 30) (vA := u + 12) (vei := u + 37)
        (vw := u + 31) (vK := u + 40) (vJ := u + 41) (x1 := u + 42) (x2 := u + 43) (x3 := u + 44) (vI := u + 45)
        (vS := u + 46) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (a := a) (b := b) (c := c) (k := k)
        (hM1 c) hka (by simp [hσ3, hσ2, hp2])
        (by rw [o _ (by omega) (by omega) (by omega), hp3]; rfl)
        hei3 (by rw [hσ3, Function.update_of_ne (by omega)]; exact hw2) hpa' (kE := .var (u + 16)) (j1E := .var (u + 20))
        (nE := nE) (epsE := epsE) (lE := lE) (rE := rE) (pfaE := pfaKE (u := u))
        (fun σ' hσ' => by simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hj)
        (fun σ' hσ' c' j₁' hj' => by
          simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega), hq]
          have := hj₁.symm.trans hj'
          cases this; rfl)
        hnFV
        (fun σ' hσ' => by rw [hn σ₀ hC σ' (ag_of_agr hu g3 hσ') c (by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5)])
        hn0 z e7 e5 e6


end node

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  {L : Lay ι ιc} (I : InstEx L N0 w B Ctx A u) (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u)

/-- **L73's `Kinds` with the shallow digit**: guarded fa and mid, and ib.  No free-variable hypotheses on `nfE, nmE, parE` are needed
(the kinds do not call `digE`).  `h27` of the ib kind is discharged by `KSt.hM`. -/
def kindsC' (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c ∨ (F c).n = 0) (hw1 : ∀ c, 1 ≤ w c)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ)) :
    Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu) where
  fa := guardKind (φ := φ) (F := F) (ok := ok) L _ (Or.inl rfl)
    (faKindC (φ := φ) (F := F) (ok := ok) L _ hu hM1 (phiWrap u Ph.phiE) (hphi_of_PhiEx L Ph hu))
  mid := guardKind (φ := φ) (F := F) (ok := ok) L _ (Or.inr rfl)
    (midKindC' (φ := φ) (F := F) (ok := ok) L _ hu hM1 hne nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr)
  ib := ibKindC (φ := φ) (F := F) (ok := ok) L _ hu hw1 (fun σ₀ hC σ hσ a b hks c hid => hks.hM c hid)


/-- the three kind expressions of `kindsC'` are the same as those of `kindsC` (so L86's depth / NoRd results for `kindsC` transfer verbatim) -/
theorem kindsC'_outE (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c ∨ (F c).n = 0) (hw1 : ∀ c, 1 ≤ w c)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ)) :
    (kindsC' (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).fa.outE =
        guardE u (faKindEC (u := u) (phiWrap u Ph.phiE)) ∧
    (kindsC' (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).mid.outE =
        guardE u (midKindEC (u := u) nE epsE lE rE) ∧
    (kindsC' (m := m) (φ := φ) (F := F) (ok := ok) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr).ib.outE =
        ibOutIC (u := u) := ⟨rfl, rfl, rfl⟩
end
end ECDLP.L90
end
