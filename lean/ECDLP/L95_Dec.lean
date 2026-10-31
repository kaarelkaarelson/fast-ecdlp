import ECDLP.L95_Bdd2
import ECDLP.L89_Num

/-!
# L95 / Dec: `DecNum` (`hG`, `hK`, `hM`) of the real layout from the arithmetic part of `EdgeReq` (item 4)

`decNum_real`: gate count `gTot <= ECDLP.L65.nodesE r n` (L65 `edge_bridge_gates`, through `Lay.enum`), `K = 18 r + 12 <= 828 (r+1) X^2 <= ECDLP.L65.nodesE r n`, `2^M <= V` (L89 `edge_num`).
Hypotheses: `size p + 4 <= 4 n`, `2^(Sb n) <= V` and `ECDLP.L65.nodesE r n <= V`.  The last is implied by `EdgeReq.hgN` (`Gs * ECDLP.L65.nodesE <= V`, `Gs >= 1`): `decNum_of_edgeReq`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 Slot Cst
open ECDLP.L83 ECDLP.L84 ECDLP.L65 ECDLP.L89 ECDLP.L90

theorem gTot_le_nodes (r p n : ℕ) (hn : Nat.size p + 4 ≤ 4 * n) (sg : Fin (r + 1) → Sg) :
    (layOf sg).gTot (NParE (Nat.size p)).A ≤ ECDLP.L65.nodesE r n := by
  have h := edge_bridge_gates p n hn sg (cnEquiv r)
  have hc : Fintype.card (CG (Slot r) (UC sg (cnEquiv r)) (NParE (Nat.size p)).A) = (layOf sg).gTot (NParE (Nat.size p)).A := by
    rw [Fintype.card_congr ((layOf sg).enum (NParE (Nat.size p)).A), Fintype.card_fin]
  rw [← hc]; exact h

theorem K_le_nodes (r n : ℕ) : 18 * r + 12 ≤ ECDLP.L65.nodesE r n := by
  have hX := Xs_pos n
  have h2 : 1 ≤ Xs n ^ 2 := Nat.one_le_pow _ _ hX
  unfold ECDLP.L65.nodesE
  nlinarith [Nat.zero_le (r * Xs n ^ 2)]

/-- **`DecNum` of the real layout** -/
theorem decNum_real (r p n : ℕ) {V : ℕ} (hn : Nat.size p + 4 ≤ 4 * n) (hset : 2 ^ Sb n ≤ V) (hN : ECDLP.L65.nodesE r n ≤ V)
    (sg : Fin (r + 1) → Sg) :
    DecNum V (layOf sg) (NParE (Nat.size p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size p)) where
  hV := by have := K_le_nodes r n; omega
  hG := le_trans (gTot_le_nodes r p n hn sg) hN
  hK := le_trans (K_le_nodes r n) hN
  hK0 := by omega
  hM := (edge_num (K := 18 * r + 12) (Nat.size p) n hn hset).2.2.2.2.2.2

/-- **`DecNum` from `EdgeReq`**: the gate-count / `K` conditions come from `hgN : Gs * ECDLP.L65.nodesE r n <= V` (`Gs >= 1`), `hset` from `hset`. -/
theorem decNum_of_edgeReq {r V m K0 ℓ n : ℕ} (h : EdgeReq r V m K0 ℓ n) (hK0 : 2 ≤ K0) (p : ℕ) (hn : Nat.size p + 4 ≤ 4 * n)
    (sg : Fin (r + 1) → Sg) :
    DecNum V (layOf sg) (NParE (Nat.size p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size p)) := by
  have hg : 1 ≤ Gs K0 ℓ := by
    show 1 ≤ 3 * Kb K0 ℓ ^ 8
    have := Nat.pow_pos (n := 8) (show 0 < Kb K0 ℓ by have := Kb_ge K0 hK0 ℓ; omega)
    omega
  refine decNum_real r p n hn h.hset ?_ sg
  exact le_trans (Nat.le_mul_of_pos_left _ hg) h.hgN

/-- **`LNum2` (the numeric side conditions of the repaired Bdd bounds) from `EdgeReq`-level facts**: `size p + 4 <= 4 n`, `hset`, `16 n + 4 <= V` (`EdgeReq.hn`).
Note: there is NO `2^(size p) <= V` here (L90's `LNum.hL2`), see `gap_hset`. -/
theorem lnum2_edge (L n : ℕ) {V : ℕ} (hn : L + 4 ≤ 4 * n) (hset : 2 ^ Sb n ≤ V) (h16 : 16 * n + 4 ≤ V) : LNum2 V L := by
  obtain ⟨hA, hD, hAD, hM, hb, hbh, hw⟩ := parB L n hn
  have hX := Xs_pos n
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX
  have hSb : Sb n = 19680 * Xs n ^ 3 := rfl
  refine ⟨le_V hset (by omega), by omega, pow_le_V hset (by omega), ?_⟩
  have hDe : DP L = 2 ^ kP L := rfl
  rw [← hDe]
  exact pow_le_V hset (by omega)

/-- `40 r + 40 <= V` (the `hn` of `instBdd_real2`, with `r` the number of points parameter) from `nodesE r n <= V` -/
theorem hn_r_of_nodes (r n : ℕ) {V : ℕ} (hN : ECDLP.L65.nodesE r n ≤ V) : 40 * r + 40 ≤ V := by
  have hX := Xs_pos n
  have h2 : 1 ≤ Xs n ^ 2 := Nat.one_le_pow _ _ hX
  unfold ECDLP.L65.nodesE at hN
  nlinarith [Nat.zero_le (r * Xs n ^ 2)]


end ECDLP.L95
end
