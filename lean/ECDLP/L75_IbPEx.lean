import ECDLP.L75_IbSem
import ECDLP.L68_Msg

/-!
# L75 / IbPEx: the `hout` / `hwt` obligations of L64's `PEx` for an `ib` node

`ibOutL X vq vA x1 e0 eT kE pmidE`: the local expression for the code of the message sent by `ib c j1` to its child
`car c j`: it copies the node into slot `u` and the setting code into `u+2`, reads (by `digE`) the ring element
received from `mid i` for each loop index `i < A` (the global index of `mid i` comes from the oracle `pmidE`), and
computes `ibE = 2^eT * hat(...)(j / A)` (the oracle `kE` gives `j / A` from the child slot `u+6`).
The oracles are exactly the layout facts of the gate enumeration (the `hjE/hpc/hpib` of L68's car case).
-/
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {e : CG ι ιc N0.A ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

/-- the message body of the `ib` gate: the ring element read from `mid i` (loop variable `x1` holds `i`) -/
def ibBody (pmidE : Ex) : Ex := .lett (u + 1) pmidE (digE X u (u + 1))

/-- the local expression for the code of the message of an `ib` node -/
def ibOutL (vq vA x1 : ℕ) (e0 eT kE pmidE : Ex) : Ex :=
  .lett u (.var (u + 5)) (.lett (u + 2) (.var (u + 7)) (ibE vq vA x1 e0 eT kE (ibBody X pmidE)))

/-- the weight expression of an `ib` node -/
def ibWtL : Ex := .lit 1

variable {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem ib_hout {vq vA x1 : ℕ} (hvq : vq < u) (hvA : vA < u) (hx1 : u + 10 ≤ x1)
    {a b : Fin g} {c : Fin K} {j1 : Fin N0.A} (hka : e.symm a = CG.gt c (Gate.ib j1))
    (hpa : e.symm a ∈ (edgeNetM (w := w) φ F ok m).pa (e.symm b)) (hM : 1 ≤ (NP N0 w c).M)
    (hq' : σ vq = 2 ^ (NP N0 w c).M + 1) (hA' : σ vA = N0.A)
    {e0 eT kE pmidE : Ex} (h0 : Ex.FV (· < u) e0) (hT : Ex.FV (· < u) eT)
    (hE : Ex.eval σ A e0 = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1))
    (hTv : Ex.eval σ A eT = (2 * (NP N0 w c).M - 1) * ((NP N0 w c).k + 1))
    (hk : Ex.FV (fun y => y = u + 6) kE)
    (hkv : ∀ j : Fin (N0.A * N0.A), e.symm b = CG.gt c (Gate.car j) → Ex.eval σ A kE = j.val / N0.A)
    (hpm : ∀ σ' : ℕ → ℕ, σ' (u + 5) = a → ∀ (i : ℕ) (hi : i < N0.A), σ' x1 = i →
      Ex.eval σ' A pmidE = e (CG.gt c (Gate.mid ⟨i, hi⟩)))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (hz : σ (u + 7) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z) (ha : σ (u + 5) = a) (hb : σ (u + 6) = b) :
    Ex.eval σ A (ibOutL X vq vA x1 e0 eT kE pmidE) =
      ec (ι := ι) (ιc := ιc) (w := w) (e.symm a) ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b)) := by
  obtain ⟨j, hbj, -⟩ := ib_child (w := w) φ c j1 (e.symm b) (hka ▸ hpa)
  rw [hbj, out_ib_q (w := w) φ F ok m c j1 (e.symm a) hka z c j]
  set σ1 := Function.update σ u (σ (u + 5)) with hσ1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with hσ2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have a2 : σ2 (u + 5) = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]; exact ha
  have u2 : σ2 u = a := by
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_self]; exact ha
  have hz2 : σ2 (u + 2) = (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
      (hF := edge_free_nonempty φ F ok m)).e a z := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by omega)]; exact hz
  have low : ∀ y, y < u → σ2 y = σ y := by
    intro y hy
    rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]
  have hq2 : σ2 vq = 2 ^ (NP N0 w c).M + 1 := by rw [low vq hvq]; exact hq'
  have hA2 : σ2 vA = N0.A := by rw [low vA hvA]; exact hA'
  have hE2 : Ex.eval σ2 A e0 = (NP N0 w c).w * (2 ^ ((NP N0 w c).k + 1) - 1) := by
    rw [← eval_fv h0 (fun y hy => (low y hy).symm)]; exact hE
  have hT2 : Ex.eval σ2 A eT = (2 * (NP N0 w c).M - 1) * ((NP N0 w c).k + 1) := by
    rw [← eval_fv hT (fun y hy => (low y hy).symm)]; exact hTv
  have hK2 : Ex.eval σ2 A kE = j.val / N0.A := by
    rw [← eval_fv hk (fun y hy => by
      subst hy; rw [hσ2, Function.update_of_ne (by omega), hσ1, Function.update_of_ne (by omega)]) ]
    exact hkv j hbj
  have hbody : ∀ i < N0.A, Rp (Function.update σ2 x1 i) A (ibBody X pmidE) (ibZ (w := w) φ F ok m c j1 z i) := by
    intro i hi
    set σ3 := Function.update σ2 x1 i with hσ3
    have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
    have a3 : σ3 (u + 5) = a := by rw [hσ3, Function.update_of_ne (by omega)]; exact a2
    have hp := hpm σ3 a3 i hi (by rw [hσ3, Function.update_self])
    set σ4 := Function.update σ3 (u + 1) (Ex.eval σ3 A pmidE) with hσ4
    have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
    have hd := eval_digE_pm (w := w) X hu hC g4 (fr := u) (tt := u + 1) (by omega) (by omega) (a := a)
      (k := e (CG.gt c (Gate.mid ⟨i, hi⟩))) (p := CG.gt c (Gate.mid ⟨i, hi⟩))
      (by rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact u2)
      (by rw [hσ4, Function.update_self, hp])
      (Equiv.symm_apply_apply _ _) (by rw [hka]; exact mid_mem_ib φ c j1 _) z
      (by rw [hσ4, Function.update_of_ne (by omega), hσ3, Function.update_of_ne (by omega)]; exact hz2)
    unfold Rp
    show Ex.eval σ4 A (digE X u (u + 1)) = _
    rw [hd]
    unfold ibZ
    rw [dif_pos hi, ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt (pm_mid_lt (w := w) φ F ok m c j1 ⟨i, hi⟩ _ hka z)).symm
  have hmain := rp_ibOut (σ := σ2) (A := A) (NP N0 w c) hM hq2 (show vq < x1 by omega) (show vA < x1 by omega) hA2
    (e0 := e0) (eT := eT) (k := kE) (u := ibBody X pmidE)
    (Ex.FV_mono (fun y hy => by omega) _ h0) (Ex.FV_mono (fun y hy => by omega) _ hk) hE2 hT2 hK2
    (ibZ (w := w) φ F ok m c j1 z) hbody
  exact hmain

theorem ib_hwt {a : Fin g} {c : Fin K} {j1 : Fin N0.A} (hka : e.symm a = CG.gt c (Gate.ib j1))
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a)) :
    Ex.eval σ A (ibWtL) = if (edgeNetM (w := w) φ F ok m).W (e.symm a) z = 1 then 1 else 0 := by
  exact (w_ib_q (w := w) φ F ok m c j1 (e.symm a) hka z).symm

end
end ECDLP.L75
end
