import ECDLP.L89_Asm
import ECDLP.L89_Num

/-!
# L89 / Kinds: `EdgeBdd` for the real kinds (L79's `kindsC`): fa and ib from `faKindC_bout`, `ibKindC_bout`

`edgeBdd_of_kinds`: `EdgeBdd` for any `Kd` whose fa / ib expressions are those of `kindsC` (definitional for `kindsC`/`kindsReal`),
from the numeric facts (`FaNum`, the ib conditions, produced by `edge_num` of L89_Num from `2^(Sb n) <= V`), `hmid` (the mid bound; from `midKindC_bout`
when `hne` holds, or L90's `hne`-free version), and the car / source-weight hypotheses.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L89
open Finset Factoring.Aux Ex SB ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73 ECDLP.L84 ECDLP.L79

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {m : ℕ}
  (Ph : PhiEx L φ B Ctx A u) (hu : B ≤ u) {V : ℕ}

theorem edgeBdd_of_kinds (IB : InstBdd V I) (DN : DecNum V L N0 w) (NN : NodeNum V N0 w)
    (Kd : Kinds (w := w) (m := m) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu))
    (h8 : 8 ≤ V) (hAA : N0.A * N0.A ≤ V)
    (hphiB : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin K) (j : ιc c), τ (u + 22) = c.val →
      τ (u + 23) = (L.ecc c j : ℕ) → Bdd V τ A Ph.phiE)
    (hsN : ∀ a : ℕ, sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V)
    (hcV : ∀ a b : Fin (L.gTot N0.A), 2 ^ (toGNetE (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)).c
      ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) ≤ V)
    (hwV : ∀ i, (edgeNetM (w := w) φ F ok m).w i + 1 ≤ V)
    -- numerics
    (Fa : FaNum V N0 w) (hw1 : ∀ c, 1 ≤ w c) (hw5 : ∀ c, w c * (N0.A * N0.A) * (N0.A * N0.A * N0.A) ≤ V)
    -- the fa and ib kinds are those of `kindsC`
    (hKfa : Kd.fa.outE = guardE u (faKindEC (u := u) (phiWrap u Ph.phiE)))
    (hKib : Kd.ib.outE = ibOutIC (u := u))
    -- mid, car, source weight, car weight
    (hmid : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin (L.gTot N0.A), kindOf ((L.enum N0.A).symm a) = GKind.mid →
      KSt (w := w) L σ u a b ((L.enum N0.A).symm a) ((L.enum N0.A).symm b) → σ (u + 7) ≤ V → Bdd V σ A Kd.mid.outE)
    (hcarO : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 5) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 7) ≤ V → Bdd V σ A (carOutX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)))
    (hsrc : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (i : ι) (s : Fin N0.A),
      (L.enum N0.A).symm a = CG.src i s → σ (u + 4) = a → σ (u + 7) ≤ V →
      σ (u + 10) = 2 ^ N0.b → σ (u + 12) = N0.A → σ (u + 13) = N0.h → σ (u + 14) = N0.b →
      σ (u + 16) = L.eι i → σ (u + 17) = s → Bdd V σ A Sw.srcE)
    (hcarW : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin (L.gTot N0.A)) (c : Fin K) (j : Fin (N0.A * N0.A)),
      (L.enum N0.A).symm a = CG.gt c (Gate.car j) → σ (u + 4) = a → σ (u + 10) = 2 ^ (NP N0 w c).b →
      σ (u + 11) = 2 ^ (NP N0 w c).M → σ (u + 28) = N0.A * N0.A → σ (u + 7) ≤ V →
      Bdd V σ A (carWX I (pex0 (F := F) (ok := ok) (m := m) I Ph hu))) :
    EdgeBdd (F := F) (ok := ok) (m := m) I Ph hu IB DN NN Kd Sw := by
  have H74 := pexB0_L74 (F := F) (ok := ok) (m := m) I IB DN NN Ph hu h8 hphiB hsN
  have H75 := pexB0_L75 (F := F) (ok := ok) (m := m) I IB DN NN Ph hu h8 hphiB hsN
  refine ⟨h8, hAA, hphiB, hsN, hcV, hwV, ?_, hmid, ?_, hcarO, hsrc, hcarW⟩
  · intro σ₀ hC σ hσ a b hk hKS hz
    rw [hKfa]
    exact (faKindC_bout L _ H74 hu Fa (phiWrap u Ph.phiE) (hphi_of_PhiEx L Ph hu)
      (hphiB_of_PhiEx L _ H74 hu Fa.hA1 Ph.phiE hphiB) σ₀ hC σ hσ a b hk hKS hz).1
  · intro σ₀ hC σ hσ a b hk hKS hz
    rw [hKib]
    exact (ibKindC_bout L _ H75 hu hw1 (fun σ₀ hC σ hσ a b hks c hid => hks.hM c hid) Fa.hqq Fa.hA3 hw5 Fa.hA1
      σ₀ hC σ hσ a b hk hKS hz).1

end
end ECDLP.L89
end
