import ECDLP.L95_CarNum
import ECDLP.L95_Bdd2
import ECDLP.L95_Dec
import ECDLP.L89_Kinds
import ECDLP.L89_Rep

/-!
# L95 / Edge: `EdgeBdd` and `NBdd` of the CLAMPED edge network built from the repaired instance (`instEx2`, `kindsReal2'`)

`edgeBdd_real2`: L89's `EdgeBdd` for the real instance, with the numerics discharged from `EdgeReq`-level facts
(`size p + 4 <= 4 n_eng`, `hset`, `16 n_eng + 4 <= V`, `nodesE n n_eng <= V`) and `InstBdd`/`DecNum`/`NodeNum`/`hcarO`/`hcarW`/`mid` from L95.
Remaining hypotheses (named): `hsN` (sN <= V, L75 `sN_le_wtH`), `hcV`, `hwV` (counts), `hsrc` (L81 `bdd_srcSlot` at the decode state), `hphiB`-free (proved here).
`nbdd_real2C`: the `NBdd` conjunct of `EdgeCore.bnd` for `pexEdgeC`.
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex SB ECDLP.L81 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L44 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L59 ECDLP.L63 ECDLP.L64 ECDLP.L65 ECDLP.L68 ECDLP.L73 ECDLP.L76
  ECDLP.L83 ECDLP.L84 ECDLP.L89 ECDLP.L90
open ECDLP.L79 (guardE faKindEC ibOutIC phiWrap)
open Slot Cst

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ}
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n) (hn : 40 * n + 40 ≤ V) (N : LNum2 V (Nat.size p)) (hu : B ≤ u)
include hbn hn N

/-- the `hphiB` hypothesis for the real `phiExInst` (L90's `phiBdd_real` without the unused `2^sigma0 <= V`) -/
theorem phiBdd_real2 : ∀ σ₀, Ctx σ₀ → ∀ τ, Ag B σ₀ τ → ∀ (c : Fin (18 * n + 12)) (j : UC (sgR n ℓ π) (cnEquiv n) c),
    τ (u + 22) = c.val → τ (u + 23) = (eccOf (sgR n ℓ π) c j : ℕ) →
    Bdd V τ A (phiExInst (n := n) (ℓ := ℓ) (π := π) u hB hR).phiE := by
  intro σ₀ hC τ hτ c j h22 h23
  have hlt : (eccOf (sgR n ℓ π) c j : ℕ) < 10 := by
    have h1 := (eccOf (sgR n ℓ π) c j).2
    have h2 := slotList_len_le (sgR n ℓ π) ((cnEquiv n).symm c)
    have : (lst (sgR n ℓ π) c).length ≤ 9 := h2
    omega
  exact bdd_phiEx (u + 22) (BN_ag hB hτ (hbn σ₀ hC)) hn (by rw [h22]; exact c.2) (u + 23)
    (by rw [h23]; have := N.h40; omega)

end

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} {V : ℕ} (hu : B ≤ u)
  {m : ℕ} (hm1 : 1 < m) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)
  (neng : ℕ) (hnS : Nat.size p + 4 ≤ 4 * neng) (hset : 2 ^ Sb neng ≤ V) (h16 : 16 * neng + 4 ≤ V)
  (hN : ECDLP.L65.nodesE n neng ≤ V)
  (hbn : ∀ σ₀, Ctx σ₀ → BN V σ₀ A n)
  (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu))
  (hsN : ∀ a : ℕ, sN (edgeNetM (w := fun _ : Fin (18 * n + 12) => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m)
      ((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A) a ≤ V)
  (hcV : ∀ a b : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A),
    2 ^ (toGNetE (edgeNetM (w := fun _ : Fin (18 * n + 12) => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m)
      (edgeEM (w := fun _ : Fin (18 * n + 12) => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m)).c
      (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a) (((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm b) ≤ V)
  (hwV : ∀ i, (edgeNetM (w := fun _ : Fin (18 * n + 12) => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m).w i + 1 ≤ V)
  (hsrc : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (a : Fin ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A)) (i : Slot n)
      (s : Fin (NParE (Nat.size p)).A),
      ((layOf (sgR n ℓ π)).enum (NParE (Nat.size p)).A).symm a = CG.src i s → σ (u + 4) = a → σ (u + 7) ≤ V →
      σ (u + 10) = 2 ^ (NParE (Nat.size p)).b → σ (u + 12) = (NParE (Nat.size p)).A → σ (u + 13) = (NParE (Nat.size p)).h →
      σ (u + 14) = (NParE (Nat.size p)).b → σ (u + 16) = (layOf (sgR n ℓ π)).eι i → σ (u + 17) = s → Bdd V σ A Sw.srcE)

include hbn Sw hsN hcV hwV hsrc hnS hset h16 hN hB hR hu in
/-- **`EdgeBdd` (L89) for the REPAIRED real instance** (`instEx2`, `kindsReal2'`): numerics from `size p + 4 <= 4 neng`, `hset`, `16 neng + 4 <= V`, `nodesE n neng <= V` -/
theorem edgeBdd_real2 :
    EdgeBdd (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu
      (instBdd_real2 hB hR hbn (hn_r_of_nodes n neng hN) (lnum2_edge (Nat.size p) neng hnS hset h16))
      (decNum_real n p neng hnS hset hN (sgR n ℓ π))
      (edge_num (K := 18 * n + 12) (Nat.size p) neng hnS hset).2.2.2.1
      (kindsReal2' hB hR hu m ok) Sw := by
  have hn' : 40 * n + 40 ≤ V := hn_r_of_nodes n neng hN
  have N : LNum2 V (Nat.size p) := lnum2_edge (Nat.size p) neng hnS hset h16
  have IB := instBdd_real2 (ℓ := ℓ) (π := π) hB hR hbn hn' N (u := u)
  have DN := decNum_real n p neng hnS hset hN (sgR n ℓ π)
  obtain ⟨Fa, Mid, hw5, NN, hAAv, h8, hMV⟩ := edge_num (K := 18 * n + 12) (Nat.size p) neng hnS hset
  have hphiB := phiBdd_real2 (ℓ := ℓ) (π := π) (u := u) hB hR hbn hn' N
  have H74 := pexB0_L74 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) IB DN NN
    (phiExInst u hB hR) hu h8 hphiB hsN
  have hcar := hcar_pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu
    IB DN NN h8 hphiB hsN hAAv (hZ_edge (K := 18 * n + 12) (Nat.size p) neng hnS hset)
  have hout := kindsReal2'_outE (ℓ := ℓ) (π := π) hB hR hu m ok
  refine edgeBdd_of_kinds (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu IB DN NN
    (kindsReal2' hB hR hu m ok) Sw h8 hAAv hphiB hsN hcV hwV Fa (fun c => wP_pos _) hw5 hout.1 hout.2.2 ?_ hcar.1 hsrc hcar.2
  intro σ₀ hC σ hσ a b hk hKS hz
  rw [hout.2.1]
  exact (midReal_bout2 hB hR hbn hn' N hu H74 Mid σ₀ hC σ hσ a b hk hKS hz).1

include hbn Sw hsN hcV hwV hsrc hnS hset h16 hN hB hR hu in
/-- **`NBdd` of the CLAMPED, REPAIRED real edge network** (the `NBdd` conjunct of `EdgeCore.bnd`) -/
theorem nbdd_real2C (hm1 : 1 < m) {σ₀ : ℕ → ℕ} (hC : Ctx σ₀) :
    haveI := edge_free_nonempty (w := fun _ : Fin (18 * n + 12) => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m
    NBdd V B σ₀ A (NVars.std u)
      (netEx (pexEdgeC (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu hm1 (kindsReal2' hB hR hu m ok) Sw))
      ((layOf (sgR n ℓ π)).gTot (NParE (Nat.size p)).A) :=
  nbdd_edgeC (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu hm1
    (instBdd_real2 hB hR hbn (hn_r_of_nodes n neng hN) (lnum2_edge (Nat.size p) neng hnS hset h16))
    (decNum_real n p neng hnS hset hN (sgR n ℓ π))
    (edge_num (K := 18 * n + 12) (Nat.size p) neng hnS hset).2.2.2.1
    (kindsReal2' hB hR hu m ok) Sw
    (edgeBdd_real2 hB hR hu ok neng hnS hset h16 hN hbn Sw hsN hcV hwV hsrc) hC

end
end ECDLP.L95
end
