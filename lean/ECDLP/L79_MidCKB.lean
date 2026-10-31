import ECDLP.L79_MidCB
import ECDLP.L79_KindC
import ECDLP.L79_DigB

/-!
# L79 / MidCKB: `PExB.bout` for the mid kind with the shallow digit (`midKindC_bout`)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (kParams2 kParams kParams_eval pfaKE NP_w_eq PExB0 Agr)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ} (H : PExB0 X V)

include H in
theorem midKindC_bout (hu : B ≤ u) (hN : MidNum V N0 w) (hne : ∀ c : Fin K, 0 < L.nc c)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ))
    (bn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Bdd V σ' A nE)
    (bε : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Bdd V (Function.update σ' (u + 43) t) A epsE)
    (bl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Bdd V (Function.update σ' (u + 43) t) A lE)
    (br : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Bdd V (Function.update σ' (u + 43) t) A rE) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A),
      kindOf ((L.enum N0.A).symm a) = GKind.mid →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V →
      Bdd V σ A (guardE u (midKindEC (u := u) nE epsE lE rE)) ∧
        Ex.eval σ A (guardE u (midKindEC (u := u) nE epsE lE rE)) + 1 ≤ V := by
  intro σ₀ hC σ hσ a b hk hKS hz0
  haveI := edge_free_nonempty (w := w) φ F ok m
  obtain ⟨c, k, hka⟩ : ∃ (c : Fin K) (k : Fin N0.A), (L.enum N0.A).symm a = CG.gt c (Gate.mid k) := by
    cases h : (L.enum N0.A).symm a with
    | src i s => rw [h] at hk; simp [kindOf] at hk
    | gt c g =>
      cases g with
      | fa _ _ => rw [h] at hk; simp [kindOf] at hk
      | mid k => exact ⟨c, k, rfl⟩
      | ib _ => rw [h] at hk; simp [kindOf] at hk
      | car _ => rw [h] at hk; simp [kindOf] at hk
  have hid : idOf ((L.enum N0.A).symm a) = some c := by simp [idOf, hka]
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hKS.hpar c hid
  have hM' := hKS.hM c hid
  have hj := hKS.hj
  have hs' := hKS.hs
  have hq := hKS.hq
  simp only [hka, coordOf] at hj hs'
  have hV8 := H.hV
  have hgV := H.hgV
  have hA1 := hN.hA1
  have hA3 := hN.hA3
  have hAA : N0.A * N0.A ≤ V := le_trans (Nat.le_mul_of_pos_right _ hA1) hA3
  have hAV : N0.A ≤ V := le_trans (Nat.le_mul_self _) hAA
  have hqq := hN.hqq c
  have hq3 : 3 ≤ 2 ^ (NP N0 w c).M + 1 := by
    have : 2 ^ 1 ≤ 2 ^ (NP N0 w c).M := Nat.pow_le_pow_right (by norm_num) (hN.hM1 c)
    omega
  have hQV : 2 ^ (NP N0 w c).M + 1 ≤ V := le_trans (Nat.le_mul_self _) hqq
  have hpM : 2 ^ (NP N0 w c).M ≤ V := by omega
  have hMV : (NP N0 w c).M ≤ V := le_trans (Nat.lt_two_pow_self).le hpM
  have hdq : σ (u + 20) < N0.A * N0.A := by
    rw [hq]
    rcases ECDLP.L75.childCoord_lt ((L.enum N0.A).symm b) with h | h
    · exact h
    · omega
  have hdqV : σ (u + 20) ≤ V := le_trans hdq.le hAA
  have hk_lt : σ (u + 16) < N0.A := by rw [hj]; exact k.2
  have hkV : σ (u + 16) ≤ V := le_trans hk_lt.le hAV
  by_cases hd : σ (u + 20) < N0.A
  · have hwv : w c ≤ V := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (hN.hwA c)
    have hwdef : σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2) = w c := by
      rw [hM', hp3]; exact NP_w_eq c
    have hAAk : N0.A * N0.A = 2 ^ ((NP N0 w c).k + 1) := (NP N0 w c).hA
    set σ1 := Function.update σ (u + 30) (σ (u + 11) + 1) with hσ1
    set σ2 := Function.update σ1 (u + 31) (σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2)) with hσ2
    have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
    have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
    have hw2 : σ2 (u + 31) = w c := by rw [hσ2, Function.update_self, hwdef]
    have hA2 : σ2 (u + 12) = N0.A := by
      rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega), hp3]
    set σ3 := Function.update σ2 (u + 37) (σ2 (u + 31) * (σ2 (u + 12) * σ2 (u + 12) - 1)) with hσ3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have o : ∀ y, y ≠ u + 30 → y ≠ u + 31 → y ≠ u + 37 → σ3 y = σ y := fun y h1 h2 h3 => by
      rw [hσ3, Function.update_of_ne h3, hσ2, Function.update_of_ne h2, hσ1, Function.update_of_ne h1]
    have e5 : σ3 (u + 5) = a := by rw [o _ (by omega) (by omega) (by omega)]; exact hKS.ha
    have e6 : σ3 (u + 6) = b := by rw [o _ (by omega) (by omega) (by omega)]; exact hKS.hb
    have e7 : σ3 (u + 7) ≤ V := by rw [o _ (by omega) (by omega) (by omega)]; exact hz0
    have e30 : σ3 (u + 30) = 2 ^ (NP N0 w c).M + 1 := by
      rw [hσ3, Function.update_of_ne (by omega), hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self, hp2]
    have e12 : σ3 (u + 12) = N0.A := by rw [o _ (by omega) (by omega) (by omega)]; exact hp3
    have e31 : σ3 (u + 31) = w c := by rw [hσ3, Function.update_of_ne (by omega)]; exact hw2
    have e37 : σ3 (u + 37) = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
      rw [hσ3, Function.update_self, hw2, hA2, hAAk]; rfl
    have agσ : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → ∀ y, u + 2 < y → y < u + 30 → σ' y = σ y := fun σ' hσ' y h1 h2 => by
      rw [hσ' y (Or.inr ⟨h1, by omega⟩), o y (by omega) (by omega) (by omega)]
    let dec : ℕ → ιc c := fun i => (L.ecc c).symm ⟨min i (L.nc c - 1), by have := hne c; omega⟩
    have hdec_ecc : ∀ x : ιc c, dec (L.ecc c x : ℕ) = x := by
      intro x
      have h1 : min (L.ecc c x : ℕ) (L.nc c - 1) = (L.ecc c x : ℕ) :=
        Nat.min_eq_left (by have := (L.ecc c x).2; omega)
      show (L.ecc c).symm ⟨min (L.ecc c x : ℕ) (L.nc c - 1), _⟩ = x
      rw [Equiv.symm_apply_eq]
      exact Fin.ext h1
    have hfvp : Ex.FV (fun y => y < u + 42 ∨ y = u + 45 ∨ y = u + 46) (pfaKE (u := u)) := by
      simp [pfaKE, Ex.FV]
    have h15 : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → σ' (u + 15) = c.val := fun σ' hσ' => by
      rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5
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
    -- bound of pfaKE for i <= V
    have hpB : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → ∀ (i s : ℕ), s < N0.A → σ' (u + 45) = i → σ' (u + 46) = s →
        i ≤ V → Bdd V σ' A (pfaKE (u := u)) := by
      intro σ' hσ' i s hs hi hs2 hiV
      have hv := hpf σ' hσ' i s hs hi hs2
      have hlt : ((L.enum N0.A (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩)) : Fin _) : ℕ) < V :=
        lt_of_lt_of_le (L.enum N0.A (CG.gt c (Gate.fa (dec i) ⟨s, hs⟩))).2 hgV
      have e18 : σ' (u + 18) = L.nι * N0.A + L.off N0.A c := by
        rw [agσ σ' hσ' (u + 18) (by omega) (by omega)]; exact hp6
      have e19 : σ' (u + 19) = L.nc c := by
        rw [agσ σ' hσ' (u + 19) (by omega) (by omega)]; exact hp7
      have e12 : σ' (u + 12) = N0.A := by
        rw [agσ σ' hσ' (u + 12) (by omega) (by omega)]; exact hp3
      have hncV : L.nc c ≤ V := nc_le_V L X H hA1 c
      have hbase : L.nι * N0.A + L.off N0.A c ≤ V := by
        have hb := hlt; rw [Lay.enum_gt] at hb; omega
      apply bdd_pfaKE (by rw [e18]; exact hbase) (by rw [e19]; exact hncV) (by rw [e12]; exact hAV) (by rw [hi]; exact hiV)
        (by rw [hs2]; exact le_trans hs.le hAV) (by omega)
      simp only [pfaKE, Ex.eval, e18, e19, e12, hi, hs2] at hv hlt
      rw [e18, e19, e12, hi, hs2]
      omega
    have hAAk' : (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) = w c * (N0.A * N0.A - 1) := by
      rw [← hAAk]; rfl
    have hEA' : (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) * (N0.A * N0.A * N0.A) ≤ V := by
      rw [hAAk']; exact hN.hEA c
    have hEV : (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) ≤ V :=
      le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hEA'
    have hn' : ∀ σ' : ℕ → ℕ, Agr u (u + 40) σ3 σ' → ∀ t, t < Ex.eval σ' A nE → t < (F c).n := fun σ' hσ' t ht => by
      rw [hn σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ')] at ht; exact ht
    have hDfvC : Ex.FV (fun y => y < u + 42 ∨ y = u + 1) (digCmid u) := by
      simp only [digCmid, nprod, Ex.FV]
      repeat' first
        | trivial
        | omega
        | (simp; done)
        | apply And.intro
    have hDbC : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, (y < u ∨ (u + 2 < y ∧ y < u + 40)) → τ y = σ3 y) →
        ∀ (kf : Fin (L.gTot N0.A)) (i' : ιc c) (s' : Fin N0.A), (L.enum N0.A).symm kf = CG.gt c (Gate.fa i' s') →
        τ u = a → τ (u + 1) = kf → τ (u + 2) ≤ V →
        Bdd V τ A (digCmid u) ∧ Ex.eval τ A (digCmid u) < 2 ^ (NP N0 w c).M + 1 := by
      intro τ gτ hτ kf i' s' hkk hτu hτ1 hτz
      have h11 : τ (u + 11) = 2 ^ (NP N0 w c).M := by
        rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega) (by omega)]; exact hp2
      have h18 : τ (u + 18) = L.nι * N0.A + L.off N0.A c := by
        rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega) (by omega)]; exact hp6
      have hbaseV : L.nι * N0.A + L.off N0.A c ≤ V := by
        have := mid_off_le L c k; omega
      have hkfV : kf.val ≤ V := le_trans kf.2.le hgV
      have hpow := mid_Qpow_le L H.hsN hka hkk
      have hnp : Bdd V τ A (nprod (u + 8) (.sub (.var (u + 1)) (.var (u + 18))) (.add (.var (u + 11)) (.lit 1))) := by
        refine bdd_nprod_const (c := 2 ^ (NP N0 w c).M + 1) ⟨(show τ (u + 1) ≤ V by rw [hτ1]; exact hkfV),
          (show τ (u + 18) ≤ V by rw [h18]; exact hbaseV)⟩ (fun j => ?_) (fun j => ?_) (fun j hj => ?_)
        · refine ⟨(show Function.update τ (u + 8) j (u + 11) ≤ V by rw [Function.update_of_ne (by omega), h11]; exact hpM),
            (show 1 ≤ V by omega), ?_⟩
          simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11]; exact hQV
        · simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11]
        · have : j ≤ kf.val - (L.nι * N0.A + L.off N0.A c) := by
            simpa [Ex.eval, hτ1, h18] using hj
          exact le_trans (Nat.pow_le_pow_right (by omega) this) hpow
      refine ⟨⟨⟨(show τ (u + 2) ≤ V from hτz), hnp⟩, ⟨(show τ (u + 11) ≤ V by rw [h11]; exact hpM), (show 1 ≤ V by omega), ?_⟩⟩, ?_⟩
      · simp only [Ex.eval]; rw [h11]; exact hQV
      · simp only [digCmid, Ex.eval, h11]
        exact Nat.mod_lt _ (by omega)
    have hmain := mid_bout'D (w := w) (φ := φ) (F := F) (ok := ok) X H hu hC g3 (digCmid u) (vq := u + 30) (vA := u + 12) (vei := u + 37)
      (vw := u + 31) (vK := u + 40) (vJ := u + 41) (x1 := u + 42) (x2 := u + 43) (x3 := u + 44) (vI := u + 45) (vS := u + 46)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (a := a) (b := b) (c := c) (k := k)
      (hN.hM1 c) hka (Q := 2 ^ (NP N0 w c).M + 1) (Av := N0.A) (wv := w c)
      (Ei := (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1)) rfl rfl e30 e12 e37 e31 hqq (by omega) hAV hwv hEV hA3
      (hN.hwA c) hEA'
      (kE := .var (u + 16)) (j1E := .var (u + 20)) (nE := nE) (epsE := epsE) (lE := lE) (rE := rE) (pfaE := pfaKE (u := u)) dec
      hnFV hεFV hlFV hrFV hfvp hDfvC hDbC
      (fun σ' hσ' => by show σ' (u + 16) ≤ V; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hkV)
      (fun σ' hσ' => by show σ' (u + 20) ≤ V; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hdqV)
      (fun σ' hσ' => by simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hk_lt)
      (fun σ' hσ' => by simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hd)
      (fun σ' hσ' => bn σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ'))
      (fun σ' hσ' t ht => by
        have ht' := hn' σ' hσ' t ht
        refine ⟨bε σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t ht', ?_⟩
        have := heps σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t ht'
        unfold Rp at this
        rw [this]; exact ZMod.val_lt _)
      (fun σ' hσ' t ht => bl σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t (hn' σ' hσ' t ht))
      (fun σ' hσ' t ht => br σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t (hn' σ' hσ' t ht))
      (fun σ' hσ' t ht => by
        rw [hl σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t (hn' σ' hσ' t ht)]; exact ecc_le_V L X H hA1 c _)
      (fun σ' hσ' t ht => by
        rw [hr σ₀ hC σ' (ag_of_agr hu g3 hσ') c (h15 σ' hσ') t (hn' σ' hσ' t ht)]; exact ecc_le_V L X H hA1 c _)
      hpB
      (fun σ' hσ' i s hs hi hs2 => hpf σ' hσ' i s hs hi hs2)
      e7 e5 e6
    -- assemble
    have hadd : Bdd V σ A (.add (.var (u + 11)) (.lit 1)) :=
      ⟨(show σ (u + 11) ≤ V by rw [hp2]; exact hpM), (show 1 ≤ V by omega),
        by simp only [Ex.eval]; rw [hp2]; exact hQV⟩
    have o1 : ∀ y, y ≠ u + 30 → σ1 y = σ y := fun y hy => by rw [hσ1, Function.update_of_ne hy]
    have hdiv : Bdd V σ1 A (.div (.var (u + 27)) (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))) := by
      refine ⟨(show σ1 (u + 27) ≤ V by rw [o1 _ (by omega), hM']; exact hMV), ?_⟩
      refine ⟨⟨(show σ1 (u + 12) ≤ V by rw [o1 _ (by omega), hp3]; exact hAV),
        (show σ1 (u + 12) ≤ V by rw [o1 _ (by omega), hp3]; exact hAV), ?_⟩, (show 2 ≤ V by omega)⟩
      simp only [Ex.eval]; rw [o1 _ (by omega), hp3]; exact hAA
    have hev2 : Ex.eval σ1 A (.div (.var (u + 27)) (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))) =
        σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2) := by
      simp only [Ex.eval]
      rw [o1 _ (by omega), o1 _ (by omega)]
    have hσ2eq : Function.update σ1 (u + 31) (Ex.eval σ1 A (.div (.var (u + 27))
        (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2)))) = σ2 := by rw [hev2]
    have hmul37 : Bdd V σ2 A (.mul (.var (u + 31)) (.sub (.mul (.var (u + 12)) (.var (u + 12))) (.lit 1))) := by
      refine ⟨(show σ2 (u + 31) ≤ V by rw [hw2]; exact hwv), ⟨⟨(show σ2 (u + 12) ≤ V by rw [hA2]; exact hAV),
        (show σ2 (u + 12) ≤ V by rw [hA2]; exact hAV), ?_⟩, B_lit (by omega)⟩, ?_⟩
      · simp only [Ex.eval]; rw [hA2]; exact hAA
      · simp only [Ex.eval]; rw [hw2, hA2]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (le_trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hA1)) (hN.hwA c))
    have hb3 : Bdd V (Function.update σ2 (u + 37) (Ex.eval σ2 A (.mul (.var (u + 31))
        (.sub (.mul (.var (u + 12)) (.var (u + 12))) (.lit 1))))) A
        (midOutLD (u := u) (digCmid u) (u + 30) (u + 12) (u + 37) (u + 31) (u + 40) (u + 41) (u + 42) (u + 43) (u + 44)
          (u + 45) (u + 46) (.var (u + 16)) (.var (u + 20)) nE epsE lE rE (pfaKE (u := u))) := hmain.1
    have hb2 : Bdd V (Function.update σ1 (u + 31) (Ex.eval σ1 A (.div (.var (u + 27))
        (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))))) A (.lett (u + 37) (.mul (.var (u + 31))
        (.sub (.mul (.var (u + 12)) (.var (u + 12))) (.lit 1)))
        (midOutLD (u := u) (digCmid u) (u + 30) (u + 12) (u + 37) (u + 31) (u + 40) (u + 41) (u + 42) (u + 43) (u + 44)
          (u + 45) (u + 46) (.var (u + 16)) (.var (u + 20)) nE epsE lE rE (pfaKE (u := u)))) := by
      rw [hσ2eq]; exact ⟨hmul37, hb3⟩
    have hguard : Bdd V σ A (guardE u (midKindEC (u := u) nE epsE lE rE)) := by
      refine ⟨(show σ (u + 20) ≤ V from hdqV), (show σ (u + 12) ≤ V by rw [hp3]; exact hAV), ?_⟩
      have : (if Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12)) then
          Bdd V σ A (midKindEC (u := u) nE epsE lE rE) else Bdd V σ A (.lit 0)) := by
        rw [if_pos (by simp only [Ex.eval]; rw [hp3]; exact hd)]
        exact ⟨hadd, hdiv, hb2⟩
      exact this
    refine ⟨hguard, ?_⟩
    have hd' : σ (u + 20) < σ (u + 12) := by rw [hp3]; exact hd
    have hev : Ex.eval σ A (guardE u (midKindEC (u := u) nE epsE lE rE)) =
        Ex.eval σ A (midKindEC (u := u) nE epsE lE rE) := by
      simp only [guardE, Ex.eval, hd', if_true]
    rw [hev]
    unfold midKindEC kParams2
    rw [kParams_eval]
    exact hmain.2
  · have hge : N0.A ≤ σ (u + 20) := by omega
    have hd' : ¬ σ (u + 20) < σ (u + 12) := by rw [hp3]; exact hd
    refine ⟨⟨hdqV, (show σ (u + 12) ≤ V by rw [hp3]; exact hAV), ?_⟩, ?_⟩
    · have : ¬ (Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12))) := by
        simp only [Ex.eval]; exact hd'
      show (if Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12)) then _ else Bdd V σ A (.lit 0))
      rw [if_neg this]; show 0 ≤ V; omega
    · simp only [guardE, Ex.eval, hd', if_false]; omega


end
end ECDLP.L79
end
