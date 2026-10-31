import ECDLP.L75_IbKind
import ECDLP.L79_IbC
import ECDLP.L79_KindC

/-!
# L79 / IbKindC: the `ib` kind with the shallow digit `digCib`
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68
open ECDLP.L73 (Lay GKind kindOf idOf coordOf childCoord KSt zcode GateKindPEx)
open ECDLP.L75 (e0I tEI kEI pmidEI FV_e0I FV_tEI FV_kEI kind_ib NP_M tInv_val ib_child ibE2 rp_ibOut2 out_ib_q mid_mem_ib)

def e0I (u : ℕ) : Ex :=
  .mul (.div (.var (u + 27)) (.mul (.var (u + 12)) (.var (u + 13)))) (.sub (.mul (.var (u + 12)) (.var (u + 12))) (.lit 1))
def tEI (u : ℕ) : Ex := .sub (.var (u + 60)) (.div (.var (u + 11)) (.mul (.var (u + 12)) (.var (u + 12))))
def kEI (u : ℕ) : Ex := .div (.var (u + 20)) (.var (u + 12))
def pmidEI (u : ℕ) : Ex := .add (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))) (.var (u + 61))

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)


/-- the `ib` expression with the shallow digit -/
def ibOutIC : Ex :=
  .lett (u + 60) (.add (.var (u + 11)) (.lit 1)) (ibOutL2D (u := u) (digCib u) (u + 60) (u + 12) (u + 61) (ECDLP.L75.e0I u) (ECDLP.L75.tEI u) (ECDLP.L75.kEI u) (ECDLP.L75.pmidEI u))

/-- **`GateKindPEx .ib`**: the `ib` kind of L73's per-kind interface. -/
def ibKindC (hu : B ≤ u) (hw1 : ∀ c, 1 ≤ w c)
    (h27 : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A),
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) →
      ∀ c, idOf ((L.enum N0.A).symm a) = some c → σ (u + 27) = (NP N0 w c).M) :
    GateKindPEx (φ := φ) (F := F) (ok := ok) (A := A) (Ctx := Ctx) (B := B) m L .ib (L.enum N0.A) u X where
  outE := ibOutIC (u := u)
  hout := by
    intro σ₀ hC σ hσ a b z hkd hpa hks hz
    obtain ⟨c, j1, hka⟩ := kind_ib hkd
    have hid : idOf ((L.enum N0.A).symm a) = some c := by rw [hka]; rfl
    obtain ⟨hb1, hM1, hA1, hh1, hc1, hbase1, hnc1⟩ := hks.hpar c hid
    have hM27 := h27 σ₀ hC σ hσ a b hks c hid
    obtain ⟨j, hbj, -⟩ := ib_child (w := w) φ c j1 ((L.enum N0.A).symm b) (hka ▸ hpa)
    have hq20 : σ (u + 20) = j.val := by rw [hks.hq, hbj]; rfl
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
    have hA' : σ' (u + 12) = N0.A := by rw [lowσ _ (by omega)]; exact hA1
    have hE : Ex.eval σ' A (e0I u) = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
      simp only [e0I, Ex.eval]
      rw [lowσ (u + 27) (by omega), lowσ (u + 13) (by omega), hA', hM27, hh1]
      have hAh : N0.A * N0.h = 2 ^ N0.k := N0.hAh
      rw [hAh, NP_M, Nat.mul_div_cancel_left _ (by positivity), hAA]
      rfl
    have hTv : Ex.eval σ' A (tEI u) = (NP N0 w c).tInv.val := by
      simp only [tEI, Ex.eval]
      have e60 : σ' (u + 60) = 2 ^ (NP N0 w c).M + 1 := by rw [hσ', Function.update_self, hM1]
      have e11 : σ' (u + 11) = 2 ^ (NP N0 w c).M := by rw [lowσ (u + 11) (by omega)]; exact hM1
      rw [e60, e11, hA']
      have := tInv_val (NP N0 w c).toPar hMk
      refine Eq.trans ?_ this.symm
      show 2 ^ (NP N0 w c).M + 1 - 2 ^ (NP N0 w c).M / (N0.A * N0.A) = _
      rfl
    have hkv : ∀ j' : Fin (N0.A * N0.A), (L.enum N0.A).symm b = CG.gt c (Gate.car j') →
        Ex.eval σ' A (kEI u) = j'.val / N0.A := by
      intro j' hj'
      have : j = j' := by
        rw [hbj] at hj'
        exact Gate.car.inj (eq_of_heq (CG.gt.inj hj').2)
      subst this
      simp only [kEI, Ex.eval]
      rw [lowσ (u + 20) (by omega), lowσ (u + 12) (by omega), hq20, hA1]
    have hpm : ∀ σ'' : ℕ → ℕ, (∀ y, u + 10 ≤ y → y < u + 61 → σ'' y = σ' y) → ∀ (i : ℕ) (hi : i < N0.A),
        σ'' (u + 61) = i → Ex.eval σ'' A (pmidEI u) = (L.enum N0.A) (CG.gt c (Gate.mid ⟨i, hi⟩)) := by
      intro σ'' hag i hi hx
      simp only [pmidEI, Ex.eval]
      rw [hag (u + 18) (by omega) (by omega), hag (u + 19) (by omega) (by omega), hag (u + 12) (by omega) (by omega),
        lowσ (u + 18) (by omega), lowσ (u + 19) (by omega), lowσ (u + 12) (by omega), hbase1, hnc1, hA1, hx,
        L.enum_gt, L.gateE_mid]
      show _ = L.nι * N0.A + (L.off N0.A c + (L.nc c * N0.A + i))
      ring
    exact ib_hout2D (m := m) (B := B) (g := L.gTot N0.A) (σ₀ := σ₀) (Ctx := Ctx) (A := A) (φ := φ) (F := F)
      (ok := ok) (e := L.enum N0.A) (u := u) hu hC hg' (digCib u) (vq := u + 60) (vA := u + 12) (x1 := u + 61)
      (by omega) (by omega) (by omega) (a := a) (b := b) (c := c) (j1 := j1) hka hpa hM1'
      (by rw [hσ', Function.update_self, hM1]) hA'
      (e0 := e0I u) (tE := tEI u) (kE := kEI u) (pmidE := pmidEI u) FV_e0I FV_tEI hE hTv FV_kEI hkv hpm z
      (by rw [lowσ _ (by omega)]; exact hz)
      (fun τ gτ hτ i hτu hτ1 hτ2 => by
        have h11 : τ (u + 11) = 2 ^ (NP N0 w c).M := by rw [hτ _ (by omega) (by omega), lowσ _ (by omega)]; exact hM1
        have h18 : τ (u + 18) = L.nι * N0.A + L.off N0.A c := by rw [hτ _ (by omega) (by omega), lowσ _ (by omega)]; exact hbase1
        have h19 : τ (u + 19) = L.nc c := by rw [hτ _ (by omega) (by omega), lowσ _ (by omega)]; exact hnc1
        have h12 : τ (u + 12) = N0.A := by rw [hτ _ (by omega) (by omega), lowσ _ (by omega)]; exact hA1
        rw [digCib_eq_digE L X hu hC gτ hka (kk := L.enum N0.A (CG.gt c (Gate.mid i))) (k := i) (by simp) hτu hτ1 h11 h18 h19 h12]
        exact eval_digE_pm X hu hC gτ (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := L.enum N0.A (CG.gt c (Gate.mid i)))
          (p := CG.gt c (Gate.mid i)) hτu hτ1 (by simp) (by rw [hka]; exact mid_mem_ib φ c j1 _) z hτ2)
      (by rw [lowσ _ (by omega)]; exact hks.ha)


end
end
end ECDLP.L79
end
