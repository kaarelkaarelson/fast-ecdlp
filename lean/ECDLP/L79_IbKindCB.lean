import ECDLP.L79_IbKindC
import ECDLP.L79_IbCB
import ECDLP.L79_DigB
import ECDLP.L75_IbKindB

/-!
# L79 / IbKindCB: `PExB.bout` for the ib kind with the shallow digit
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L73 (Lay GKind kindOf idOf coordOf childCoord KSt zcode GateKindPEx)
open ECDLP.L75 (PExB0 e0I tEI kEI pmidEI kind_ib NP_M tInv_val ib_child childCoord_lt)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)
  {V : ℕ} (H : PExB0 X V)

include H in
theorem ibKindC_bout (hu : B ≤ u) (hw1 : ∀ c, 1 ≤ w c)
    (h27 : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A),
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) →
      ∀ c, idOf ((L.enum N0.A).symm a) = some c → σ (u + 27) = (NP N0 w c).M)
    (hqq : ∀ c, (2 ^ (NP N0 w c).M + 1) * (2 ^ (NP N0 w c).M + 1) ≤ V) (hA3 : N0.A * N0.A * N0.A ≤ V)
    (hw5 : ∀ c, w c * (N0.A * N0.A) * (N0.A * N0.A * N0.A) ≤ V) (hA1 : 1 ≤ N0.A) :
    ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), 
      kindOf ((L.enum N0.A).symm a) = GKind.ib →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V →
      Bdd V σ A (ibOutIC (u := u)) ∧ Ex.eval σ A (ibOutIC (u := u)) + 1 ≤ V := by
  intro σ₀ hC σ hσ a b hkd hks hz0
  haveI := edge_free_nonempty (w := w) φ F ok m
  obtain ⟨c, j1, hka⟩ := kind_ib hkd
  have hid : idOf ((L.enum N0.A).symm a) = some c := by rw [hka]; rfl
  obtain ⟨hb1, hM1, hA1', hh1, hc1, hbase1, hnc1⟩ := hks.hpar c hid
  have hM27 := h27 σ₀ hC σ hσ a b hks c hid
  set σ' := Function.update σ (u + 60) (σ (u + 11) + 1) with hσ'
  have hg' : Ag B σ₀ σ' := hσ.upd (by omega) _
  have lowσ : ∀ y, y ≠ u + 60 → σ' y = σ y := fun y hy => by rw [hσ', Function.update_of_ne hy]
  have hMk : (NP N0 w c).k + 1 ≤ (NP N0 w c).M := by
    have h1 := hw1 c
    have h2 : N0.k < 2 ^ N0.k := Nat.lt_two_pow_self
    show N0.k + 1 ≤ 2 ^ N0.k * w c
    nlinarith
  have hM1' : 1 ≤ (NP N0 w c).M := by have := hMk; omega
  have hAA : N0.A * N0.A = 2 ^ (N0.k + 1) := N0.hA
  have hqq' := hqq c
  have hq3 : 2 < 2 ^ (NP N0 w c).M + 1 := by
    have : 2 ^ 1 ≤ 2 ^ (NP N0 w c).M := Nat.pow_le_pow_right (by norm_num) hM1'
    omega
  have hqV : 2 ^ (NP N0 w c).M + 1 ≤ V := le_trans (Nat.le_mul_self _) hqq'
  have hAV : N0.A * N0.A ≤ V := le_trans (Nat.le_mul_of_pos_right _ hA1) hA3
  have hAV1 : N0.A ≤ V := le_trans (Nat.le_mul_self _) hAV
  have hV8 := H.hV
  have hA' : σ' (u + 12) = N0.A := by rw [lowσ _ (by omega)]; exact hA1'
  have e60 : σ' (u + 60) = 2 ^ (NP N0 w c).M + 1 := by rw [hσ', Function.update_self, hM1]
  have e11 : σ' (u + 11) = 2 ^ (NP N0 w c).M := by rw [lowσ (u + 11) (by omega)]; exact hM1
  have e13 : σ' (u + 13) = N0.h := by rw [lowσ (u + 13) (by omega)]; exact hh1
  have e27 : σ' (u + 27) = (NP N0 w c).M := by rw [lowσ (u + 27) (by omega)]; exact hM27
  have e18 : σ' (u + 18) = L.nι * N0.A + L.off N0.A c := by rw [lowσ (u + 18) (by omega)]; exact hbase1
  have e19 : σ' (u + 19) = L.nc c := by rw [lowσ (u + 19) (by omega)]; exact hnc1
  have e20 : σ' (u + 20) < N0.A * N0.A := by
    rw [lowσ (u + 20) (by omega), hks.hq]
    rcases childCoord_lt ((L.enum N0.A).symm b) with h | h
    · exact h
    · omega
  -- bounds of the leaf expressions at any state agreeing with `σ'` on the read-only region
  have hag : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) →
      σ'' (u + 60) = 2 ^ (NP N0 w c).M + 1 ∧ σ'' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ'' (u + 12) = N0.A ∧
      σ'' (u + 13) = N0.h ∧ σ'' (u + 27) = (NP N0 w c).M ∧ σ'' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
      σ'' (u + 19) = L.nc c ∧ σ'' (u + 20) < N0.A * N0.A := by
    intro σ'' h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h _ (by omega) (by omega)]; exact e60
    · rw [h _ (by omega) (by omega)]; exact e11
    · rw [h _ (by omega) (by omega)]; exact hA'
    · rw [h _ (by omega) (by omega)]; exact e13
    · rw [h _ (by omega) (by omega)]; exact e27
    · rw [h _ (by omega) (by omega)]; exact e18
    · rw [h _ (by omega) (by omega)]; exact e19
    · rw [h _ (by omega) (by omega)]; exact e20
  have hAh : N0.A * N0.h = 2 ^ N0.k := N0.hAh
  have hAhV : N0.A * N0.h ≤ V := by
    rw [hAh]
    refine le_trans ?_ hAV
    rw [hAA]; exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
  have hMV : (NP N0 w c).M ≤ V := le_trans (Nat.lt_two_pow_self).le (le_trans (Nat.le_succ _) hqV)
  have hpM : 2 ^ (NP N0 w c).M ≤ V := by omega
  have hwAA : w c * (N0.A * N0.A) ≤ V := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (hw5 c)
  have hAAle : N0.A * N0.A ≤ 2 ^ (NP N0 w c).M := by
    rw [hAA]; exact Nat.pow_le_pow_right (by norm_num) hMk
  have hdivpos : 1 ≤ 2 ^ (NP N0 w c).M / (N0.A * N0.A) := Nat.div_pos hAAle (by positivity)
  have hB0 : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) →
      Bdd V σ'' A (e0I u) ∧ Ex.eval σ'' A (e0I u) ≤ w c * (N0.A * N0.A) := by
    intro σ'' h
    obtain ⟨-, -, h12, h13, h27, -, -, -⟩ := hag σ'' h
    have hev : Ex.eval σ'' A (e0I u) = w c * (N0.A * N0.A - 1) := by
      simp only [e0I, Ex.eval]
      rw [h27, h12, h13, hAh, NP_M, Nat.mul_div_cancel_left _ (by positivity)]
    have hle : w c * (N0.A * N0.A - 1) ≤ w c * (N0.A * N0.A) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    refine ⟨?_, by rw [hev]; exact hle⟩
    refine ⟨⟨(show σ'' (u + 27) ≤ V by rw [h27]; exact hMV), ⟨(show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1),
      (show σ'' (u + 13) ≤ V by rw [h13]; have := ECDLP.L57.h_le_A N0; omega), by simp only [Ex.eval, h12, h13]; exact hAhV⟩⟩,
      ⟨⟨(show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1), (show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1),
        by simp only [Ex.eval, h12]; exact hAV⟩, (show 1 ≤ V by omega)⟩, ?_⟩
    simp only [e0I, Ex.eval] at hev ⊢
    rw [hev]; exact le_trans hle hwAA
  have hBT : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) →
      Bdd V σ'' A (tEI u) ∧ Ex.eval σ'' A (tEI u) < 2 ^ (NP N0 w c).M + 1 := by
    intro σ'' h
    obtain ⟨h60, h11, h12, -, -, -, -, -⟩ := hag σ'' h
    refine ⟨⟨(show σ'' (u + 60) ≤ V by rw [h60]; exact hqV), ⟨(show σ'' (u + 11) ≤ V by rw [h11]; exact hpM),
      ⟨(show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1), (show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1),
        by simp only [Ex.eval, h12]; exact hAV⟩⟩⟩, ?_⟩
    simp only [tEI, Ex.eval, h60, h11, h12]
    omega
  have hBk : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) →
      Bdd V σ'' A (kEI u) ∧ Ex.eval σ'' A (kEI u) ≤ N0.A := by
    intro σ'' h
    obtain ⟨-, -, h12, -, -, -, -, h20⟩ := hag σ'' h
    refine ⟨⟨(show σ'' (u + 20) ≤ V by exact le_trans h20.le hAV), (show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1)⟩, ?_⟩
    simp only [kEI, Ex.eval, h12]
    exact (Nat.div_lt_of_lt_mul h20).le
  have hpmv : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) → ∀ (i : ℕ) (hi : i < N0.A),
      σ'' (u + 61) = i → Ex.eval σ'' A (pmidEI u) = (L.enum N0.A) (CG.gt c (Gate.mid ⟨i, hi⟩)) := by
    intro σ'' hag' i hi hx
    obtain ⟨-, -, h12, -, -, h18, h19, -⟩ := hag σ'' hag'
    simp only [pmidEI, Ex.eval]
    rw [h12, h18, h19, hx, L.enum_gt, L.gateE_mid]
    show _ = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + i))
    ring
  have hBp : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) → ∀ (i : ℕ) (hi : i < N0.A),
      σ'' (u + 61) = i → Bdd V σ'' A (pmidEI u) := by
    intro σ'' hag' i hi hx
    obtain ⟨-, -, h12, -, -, h18, h19, -⟩ := hag σ'' hag'
    have hv := hpmv σ'' hag' i hi hx
    have hlt : ((L.enum N0.A) (CG.gt c (Gate.mid ⟨i, hi⟩)) : ℕ) < V :=
      lt_of_lt_of_le ((L.enum N0.A) (CG.gt c (Gate.mid ⟨i, hi⟩))).2 H.hgV
    simp only [pmidEI, Ex.eval, h12, h18, h19, hx] at hv hlt ⊢
    have hnc : L.nc c * N0.A ≤ V := by omega
    have hb : L.nι * N0.A + L.off N0.A c ≤ V := by omega
    refine ⟨⟨(show σ'' (u + 18) ≤ V by rw [h18]; exact hb), ⟨(show σ'' (u + 19) ≤ V by rw [h19]; exact le_trans (Nat.le_mul_of_pos_right _ hA1) hnc),
      (show σ'' (u + 12) ≤ V by rw [h12]; exact hAV1), by simp only [Ex.eval, h12, h19]; exact hnc⟩,
      by simp only [Ex.eval, h12, h18, h19]; omega⟩, (show σ'' (u + 61) ≤ V by rw [hx]; omega), ?_⟩
    simp only [Ex.eval, h12, h18, h19, hx]; omega
  have hbaseV : L.nι * N0.A + L.off N0.A c + L.nc c * N0.A ≤ V := by
    have := ECDLP.L79.mid_off_le L c ⟨0, hA1⟩; have := H.hgV; omega
  have hDbI : ∀ τ : ℕ → ℕ, Ag B σ₀ τ → (∀ y, u + 10 ≤ y → y < u + 61 → τ y = σ' y) → ∀ (i : Fin N0.A), τ u = a →
      τ (u + 1) = (L.enum N0.A) (CG.gt c (Gate.mid i)) → τ (u + 2) ≤ V →
      Bdd V τ A (digCib u) ∧ Ex.eval τ A (digCib u) < 2 ^ (NP N0 w c).M + 1 := by
    intro τ gτ hτ i hτu hτ1 hτz
    have h11 : τ (u + 11) = 2 ^ (NP N0 w c).M := by rw [hτ _ (by omega) (by omega)]; exact e11
    have h18 : τ (u + 18) = L.nι * N0.A + L.off N0.A c := by rw [hτ _ (by omega) (by omega)]; exact e18
    have h19 : τ (u + 19) = L.nc c := by rw [hτ _ (by omega) (by omega)]; exact e19
    have h12 : τ (u + 12) = N0.A := by rw [hτ _ (by omega) (by omega)]; exact hA'
    have hkfV : ((L.enum N0.A) (CG.gt c (Gate.mid i)) : ℕ) ≤ V := le_trans (L.enum N0.A _).2.le H.hgV
    have hncA : L.nc c * N0.A ≤ V := by omega
    have hpow := ECDLP.L79.ib_Qpow_le L H.hsN hka (kk := (L.enum N0.A) (CG.gt c (Gate.mid i))) (k := i) (by simp)
    have hnp : Bdd V τ A (nprod (u + 8) (.sub (.var (u + 1)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))))
        (.add (.var (u + 11)) (.lit 1))) := by
      refine bdd_nprod_const (c := 2 ^ (NP N0 w c).M + 1) ⟨(show τ (u + 1) ≤ V by rw [hτ1]; exact hkfV),
        ⟨(show τ (u + 18) ≤ V by rw [h18]; omega), ⟨(show τ (u + 19) ≤ V by rw [h19]; exact le_trans (Nat.le_mul_of_pos_right _ hA1) hncA),
          (show τ (u + 12) ≤ V by rw [h12]; exact hAV1), by simp only [Ex.eval]; rw [h19, h12]; exact hncA⟩,
          by simp only [Ex.eval]; rw [h18, h19, h12]; exact hbaseV⟩⟩ (fun j => ?_) (fun j => ?_) (fun j hj => ?_)
      · refine ⟨(show Function.update τ (u + 8) j (u + 11) ≤ V by rw [Function.update_of_ne (by omega), h11]; exact hpM),
          (show 1 ≤ V by omega), ?_⟩
        simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11]; exact hqV
      · simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11]
      · have : j ≤ ((L.enum N0.A) (CG.gt c (Gate.mid i)) : ℕ) - (L.nι * N0.A + L.off N0.A c + L.nc c * N0.A) := by
          simpa [Ex.eval, hτ1, h18, h19, h12] using hj
        exact le_trans (Nat.pow_le_pow_right (by omega) this) hpow
    refine ⟨⟨⟨(show τ (u + 2) ≤ V from hτz), hnp⟩, ⟨(show τ (u + 11) ≤ V by rw [h11]; exact hpM), (show 1 ≤ V by omega), ?_⟩⟩, ?_⟩
    · simp only [Ex.eval]; rw [h11]; exact hqV
    · simp only [digCib, Ex.eval, h11]
      exact Nat.mod_lt _ (by omega)
  have hmain := ib_bout2D (m := m) (B := B) (g := L.gTot N0.A) (σ₀ := σ₀) (Ctx := Ctx) (A := A) (φ := φ) (F := F)
    (ok := ok) (e := L.enum N0.A) (u := u) X H hu hC hg' (digCib u) (vq := u + 60) (vA := u + 12) (x1 := u + 61)
    (by omega) (by omega) (by omega) (a := a) (b := b) (c := c) (j1 := j1) hka hM1' e60 hA' hqq' hAV1 hAV
    (w c * (N0.A * N0.A)) N0.A (by simpa using hA3) (by simpa using hw5 c)
    hB0 hBT hBk hpmv hBp hDbI (by rw [lowσ _ (by omega)]; exact hks.ha) (by rw [lowσ _ (by omega)]; exact hz0)
  have hadd : Bdd V σ A (.add (.var (u + 11)) (.lit 1)) :=
    ⟨(show σ (u + 11) ≤ V by rw [hM1]; exact hpM), (show 1 ≤ V by omega),
      by simp only [Ex.eval]; rw [hM1]; exact hqV⟩
  refine ⟨⟨hadd, ?_⟩, ?_⟩
  · exact hmain.1
  · exact hmain.2


end
end ECDLP.L79
end
