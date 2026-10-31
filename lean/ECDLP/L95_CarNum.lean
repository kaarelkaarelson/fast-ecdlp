import ECDLP.L95_Car
import ECDLP.L89_Num

/-!
# L95 / CarNum: the numeric hypothesis `4 * (2^b * (8 * 2^M)) <= V` of the car bounds from `EdgeReq.hset`; `hcarO`/`hcarW` for `pex0`
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L59 ECDLP.L64 ECDLP.L65 ECDLP.L68 ECDLP.L73 ECDLP.L84 ECDLP.L89

/-- `4 * (2^b * (8 * 2^M)) <= V` for the real parameters (`b <= 432 X^3`, `M <= 960 X^3`, `b + M + 5 <= 19680 X^3 = Sb n`) -/
theorem hZ_edge {K : ℕ} (L n : ℕ) (hn : L + 4 ≤ 4 * n) {V : ℕ} (hset : 2 ^ Sb n ≤ V) :
    ∀ c : Fin K, 4 * (2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).b * (8 * 2 ^ (NP (NParE L) (fun _ : Fin K => wP L) c).M)) ≤ V := by
  intro c
  obtain ⟨hA, hD, hAD, hM, hb, hbh, hw⟩ := parB L n hn
  have hX := Xs_pos n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  have hSb : Sb n = 19680 * Xs n ^ 3 := rfl
  have hMc : (NP (NParE L) (fun _ : Fin K => wP L) c).M = DP L * wP L := rfl
  have hbc : (NP (NParE L) (fun _ : Fin K => wP L) c).b = bP L := rfl
  rw [hMc, hbc]
  have : 4 * (2 ^ bP L * (8 * 2 ^ (DP L * wP L))) = 2 ^ (bP L + DP L * wP L + 5) := by
    rw [pow_add, pow_add]; ring
  rw [this]
  exact pow_le_V hset (by omega)

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) {V : ℕ}

/-- **`hcarO` and `hcarW` of `EdgeBdd` (L89), for `pex0 I Ph hu`** (the exact field types), from `InstBdd`, `DecNum`, `NodeNum`, `phiE` bound, `sN` bound, `A*A <= V`, `4 2^b 8 2^M <= V`. -/
theorem hcar_pex0 (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w) (h8 : 8 ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE)
    (hsN : ∀ a : ℕ, sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V)
    (hAA : N0.A * N0.A ≤ V) (hZ : ∀ c : Fin K, 4 * (2 ^ (NP N0 w c).b * (8 * 2 ^ (NP N0 w c).M)) ≤ V) :
    (∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 5) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 7) ≤ V → Bdd V σ A (carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu))) ∧
    (∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 4) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 28) = N0.A * N0.A → σ (u + 7) ≤ V →
      Bdd V σ A (carWX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu))) :=
  have H := pexB0_L75 (F := F) (ok := ok) (m := m) I IB DN NN Ph hu h8 hphiB hsN
  ⟨hcarO_of I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) hu IB DN h8 H hAA hZ,
   hcarW_of I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) hu IB DN h8 H hAA hZ⟩

end
end ECDLP.L95
end
