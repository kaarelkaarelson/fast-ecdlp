import ECDLP.L79_KindC
import ECDLP.L79_FaCB
import ECDLP.L79_FaB

/-!
# L79 / FaCB2: `PExB.bout` for the fa kind with the shallow digit

`faKind_bout`: for the guarded fa expression `guardE u (faKindE L X phiE)` (= `outE` of `guardKind _ (faKind ..)`), in the decode state
`KSt` of ANY pair of nodes `(a, b)` with `a` of kind fa (no edge hypothesis), for every setting code `z <= V`:
all values met are `<= V` and the message code `+ 1 <= V`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Factoring.Aux.SB Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73
open ECDLP.L74 (fa_bout faKindE kParams kParams_eval NP_w_eq PExB0 Agr)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ} (H : PExB0 X V)

include H in
theorem faKindC_bout (hu : B ≤ u) (hN : FaNum V N0 w) (phiE : Ex)
    (hphi : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K) (j : ιc c), σ' (u + 15) = c.val →
      σ' (u + 16) = (L.ecc c j : ℕ) → Ex.eval σ' A phiE = (L.eι (φ c j) : ℕ))
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K) (j : ιc c), σ' (u + 15) = c.val →
      σ' (u + 16) = (L.ecc c j : ℕ) → Bdd V σ' A phiE) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A),
      kindOf ((L.enum N0.A).symm a) = GKind.fa →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V →
      Bdd V σ A (guardE u (faKindEC (u := u) phiE)) ∧
        Ex.eval σ A (guardE u (faKindEC (u := u) phiE)) + 1 ≤ V := by
  intro σ₀ hC σ hσ a b hk hKS hz0
  haveI := edge_free_nonempty (w := w) φ F ok m
  obtain ⟨c, j, s, hka⟩ : ∃ (c : Fin K) (j : ιc c) (s : Fin N0.A), (L.enum N0.A).symm a = CG.gt c (Gate.fa j s) := by
    cases h : (L.enum N0.A).symm a with
    | src i s => rw [h] at hk; simp [kindOf] at hk
    | gt c g =>
      cases g with
      | fa j s => exact ⟨c, j, s, rfl⟩
      | mid _ => rw [h] at hk; simp [kindOf] at hk
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
  by_cases hd : σ (u + 20) < N0.A
  · -- the real branch
    have hs_lt : σ (u + 17) < N0.A := by rw [hs']; exact s.2
    have hsV : σ (u + 17) ≤ V := le_trans hs_lt.le hAV
    have hw1 : (NP N0 w c).w = w c := rfl
    have hwv : w c ≤ V := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (hN.hwA c)
    have hhV : N0.h ≤ V := by
      have := ECDLP.L57.h_le_A N0; omega
    have hBV := hN.hBh c
    have hB1 : 1 ≤ 2 ^ (NP N0 w c).b := Nat.one_le_two_pow
    have hwdef : σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2) = w c := by
      rw [hM', hp3]; exact NP_w_eq c
    -- the kParams chain
    set σ1 := Function.update σ (u + 30) (σ (u + 11) + 1) with hσ1
    set σ2 := Function.update σ1 (u + 31) (σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2)) with hσ2
    have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
    have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
    have o : ∀ y, y ≠ u + 30 → y ≠ u + 31 → σ2 y = σ y := fun y h1 h2 => by
      rw [hσ2, Function.update_of_ne h2, hσ1, Function.update_of_ne h1]
    have e30 : σ2 (u + 30) = 2 ^ (NP N0 w c).M + 1 := by
      rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self, hp2]
    have e31 : σ2 (u + 31) = w c := by rw [hσ2, Function.update_self, hwdef]
    have e12 : σ2 (u + 12) = N0.A := by rw [o _ (by omega) (by omega)]; exact hp3
    have e13 : σ2 (u + 13) = N0.h := by rw [o _ (by omega) (by omega)]; exact hp4
    have e10 : σ2 (u + 10) = 2 ^ (NP N0 w c).b := by rw [o _ (by omega) (by omega)]; exact hp1
    have e5 : σ2 (u + 5) = a := by rw [o _ (by omega) (by omega)]; exact hKS.ha
    have e6 : σ2 (u + 6) = b := by rw [o _ (by omega) (by omega)]; exact hKS.hb
    have e7 : σ2 (u + 7) ≤ V := by rw [o _ (by omega) (by omega)]; exact hz0
    have e17 : σ2 (u + 17) = s.val := by rw [o _ (by omega) (by omega)]; exact hs'
    have e20 : σ2 (u + 20) = σ (u + 20) := o _ (by omega) (by omega)
    have agσ : ∀ σ' : ℕ → ℕ, Agr u (u + 32) σ2 σ' → ∀ y, u + 2 < y → y < u + 30 → σ' y = σ y := fun σ' hσ' y h1 h2 => by
      rw [hσ' y (Or.inr ⟨h1, by omega⟩), o y (by omega) (by omega)]
    have hmain := fa_boutD (w := w) (φ := φ) (F := F) (ok := ok) X H hu hC g2 (digCfa u) (vq := u + 30) (vA := u + 12) (vh := u + 13)
      (vb := u + 10) (vw := u + 31) (vs := u + 32) (vk := u + 33) (vcd := u + 34) (x1 := u + 35) (xp := u + 36)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      e30 e12 e13 e10 e31 hq3 hqq (by omega) hAV hA3 hwv (hN.hwA c) hhV hBV hB1
      (sE := .var (u + 17)) (kE := .var (u + 20))
      (psrcE := .add (.mul phiE (.var (u + 12))) (.var (u + 17))) (a := a) (b := b)
      (fun σ' hσ' => by show σ' (u + 17) ≤ V; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hsV)
      (fun σ' hσ' => by show σ' (u + 20) ≤ V; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hdqV)
      (fun σ' hσ' => by
        have h15 : σ' (u + 15) = c.val := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5
        have h16 : σ' (u + 16) = (L.ecc c j : ℕ) := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hj
        have h17 : σ' (u + 17) = s.val := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hs'
        have h12 : σ' (u + 12) = N0.A := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp3
        have hv := hphi σ₀ hC σ' (ag_of_agr hu g2 hσ') c j h15 h16
        have hlt : ((L.enum N0.A (CG.src (φ c j) s) : Fin _) : ℕ) < V :=
          lt_of_lt_of_le (L.enum N0.A (CG.src (φ c j) s)).2 hgV
        rw [Lay.enum_src] at hlt
        refine ⟨⟨hphiB σ₀ hC σ' (ag_of_agr hu g2 hσ') c j h15 h16, (show σ' (u + 12) ≤ V by rw [h12]; exact hAV), ?_⟩,
          (show σ' (u + 17) ≤ V by rw [h17]; exact le_trans s.2.le hAV), ?_⟩
        · simp only [Ex.eval, hv, h12]; omega
        · simp only [Ex.eval, hv, h12, h17]; omega)
      (fun σ' hσ' => by
        simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega), hs']; exact s.2)
      (fun σ' hσ' => by
        simp only [Ex.eval]; rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hd)
      (fun σ' hσ' => by
        have h15 : σ' (u + 15) = c.val := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp5
        have h16 : σ' (u + 16) = (L.ecc c j : ℕ) := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hj
        have h17 : σ' (u + 17) = s.val := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hs'
        have h12 : σ' (u + 12) = N0.A := by rw [agσ σ' hσ' _ (by omega) (by omega)]; exact hp3
        refine ⟨L.enum N0.A (CG.src (φ c j) s), ?_⟩
        simp only [Ex.eval, hphi σ₀ hC σ' (ag_of_agr hu g2 hσ') c j h15 h16, h12, h17, Lay.enum_src])
      (fun τ gτ hτ kf hτu hτ1 hτz => by
        have h10 : τ (u + 10) = 2 ^ (NP N0 w c).b := by
          rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega)]; exact hp1
        have h13 : τ (u + 13) = N0.h := by
          rw [hτ _ (Or.inr ⟨by omega, by omega⟩), o _ (by omega) (by omega)]; exact hp4
        have hhV' : N0.h ≤ V := hhV
        refine ⟨(show τ (u + 2) ≤ V from hτz), ?_⟩
        refine bdd_nprod_const (c := 2 ^ (NP N0 w c).b) (B_var (show τ (u + 13) ≤ V by rw [h13]; exact hhV'))
          (fun j => B_var ?_) (fun j => ?_) (fun j hj => ?_)
        · show Function.update τ (u + 8) j (u + 10) ≤ V
          rw [Function.update_of_ne (by omega), h10]
          exact le_trans (by have := Nat.pow_le_pow_right hB1 (show 1 ≤ N0.h from Nat.pos_of_ne_zero (fun h0 => by
            have h1 := N0.hAh; rw [h0, Nat.mul_zero] at h1; exact absurd h1.symm (by positivity))); simpa using this) hBV
        · simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h10]
        · simp only [Ex.eval, h13] at hj
          exact le_trans (Nat.pow_le_pow_right hB1 hj) hBV)
      e7 e5 e6
    -- assemble
    have hadd : Bdd V σ A (.add (.var (u + 11)) (.lit 1)) :=
      ⟨(show σ (u + 11) ≤ V by rw [hp2]; exact hpM), (show 1 ≤ V by omega),
        by simp only [Ex.eval]; rw [hp2]; exact hQV⟩
    have hdiv : Bdd V σ1 A (.div (.var (u + 27)) (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))) := by
      have o1 : ∀ y, y ≠ u + 30 → σ1 y = σ y := fun y hy => by rw [hσ1, Function.update_of_ne hy]
      refine ⟨(show σ1 (u + 27) ≤ V by rw [o1 _ (by omega), hM']; exact hMV), ?_⟩
      refine ⟨⟨(show σ1 (u + 12) ≤ V by rw [o1 _ (by omega), hp3]; exact hAV),
        (show σ1 (u + 12) ≤ V by rw [o1 _ (by omega), hp3]; exact hAV), ?_⟩, (show 2 ≤ V by omega)⟩
      simp only [Ex.eval]; rw [o1 _ (by omega), hp3]; exact hAA
    have hguard : Bdd V σ A (guardE u (faKindEC (u := u) phiE)) := by
      refine ⟨(show σ (u + 20) ≤ V from hdqV), (show σ (u + 12) ≤ V by rw [hp3]; exact hAV), ?_⟩
      have : (if Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12)) then
          Bdd V σ A (faKindEC (u := u) phiE) else Bdd V σ A (.lit 0)) := by
        rw [if_pos (by simp only [Ex.eval]; rw [hp3]; exact hd)]
        have hev2 : Ex.eval σ1 A (.div (.var (u + 27)) (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))) =
            σ (u + 27) / (σ (u + 12) * σ (u + 12) / 2) := by
          simp only [Ex.eval, hσ1]
          rw [Function.update_of_ne (show u + 27 ≠ u + 30 by omega), Function.update_of_ne (show u + 12 ≠ u + 30 by omega)]
        have hb2 : Bdd V (Function.update σ1 (u + 31) (Ex.eval σ1 A (.div (.var (u + 27))
            (.div (.mul (.var (u + 12)) (.var (u + 12))) (.lit 2))))) A (faOutLD (u := u) (digCfa u) (u + 30) (u + 12) (u + 13) (u + 10) (u + 31) (u + 32) (u + 33) (u + 34) (u + 35) (u + 36)
            (.var (u + 17)) (.var (u + 20)) (.add (.mul phiE (.var (u + 12))) (.var (u + 17)))) := by
          rw [hev2]; exact hmain.1
        exact ⟨hadd, hdiv, hb2⟩
      exact this
    refine ⟨hguard, ?_⟩
    have hev : Ex.eval σ A (guardE u (faKindEC (u := u) phiE)) =
        Ex.eval σ A (faKindEC (u := u) phiE) := by
      have hd' : σ (u + 20) < σ (u + 12) := by rw [hp3]; exact hd
      simp only [guardE, Ex.eval, hd', if_true]
    rw [hev]
    unfold faKindEC
    rw [kParams_eval]
    exact hmain.2
  · -- the guard returns 0
    have hge : N0.A ≤ σ (u + 20) := by omega
    refine ⟨⟨hdqV, (show σ (u + 12) ≤ V by rw [hp3]; exact hAV), ?_⟩, ?_⟩
    · have : ¬ (Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12))) := by
        simp only [Ex.eval]; rw [hp3]; exact hd
      show (if Ex.eval σ A (.var (u + 20)) < Ex.eval σ A (.var (u + 12)) then _ else Bdd V σ A (.lit 0))
      rw [if_neg this]; show 0 ≤ V; omega
    · have hd' : ¬ σ (u + 20) < σ (u + 12) := by rw [hp3]; exact hd
      simp only [guardE, Ex.eval, hd', if_false]; omega


end
end ECDLP.L79
end
