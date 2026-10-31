import ECDLP.L65_Arith

/-!
# L65 / Fam: the ECDLP edge-network family as an L60 `NetFamily`, and its size `Spec`

Fixed parameter `r` (the number of points is `m = r + 1`, a constant of the family).  Scale
`X n = 2^(sOf n)` (Rudich), so `n ≤ 4 X^4`, `X^4 ≤ 4 n + 4`.  With `n ≥ L + ...` the input length,
the bounds proved in `L65_Bridge` for the real network (total bits `≤ Uc X^4`, per-cluster overhead
`Wcn X^3`, setting length `≤ 19680 X^3`, gates `≤ 828 m X^2`) are the data below.
`FamOK` is the explicit requirement list `EdgeReq` (the arithmetic part of Rudich's `TopReq`).
-/
namespace ECDLP.L65
open Factoring.Aux ECDLP.L60

/-- the scale -/
def Xs (n : ℕ) : ℕ := 2 ^ sOf n

/-- total shared bits per `X^4` : `96552 · 16 · m` -/
def Uc (r : ℕ) : ℕ := 1544832 * (r + 1)
/-- per-cluster overhead per `X^3` : `(666 m + 1045) · 12 ≤ 20532 m` -/
def Wcn (r : ℕ) : ℕ := 20532 * (r + 1)
/-- max setting length per `X^3` : `1640 · 12` -/
def Scn : ℕ := 19680
/-- the constant of the size interface -/
def cE (r : ℕ) : ℕ := 10000000 * (r + 1)

def Ub (r n : ℕ) : ℕ := Uc r * Xs n ^ 4
def Wm (r n : ℕ) : ℕ := Wcn r * Xs n ^ 3
def Sb (n : ℕ) : ℕ := Scn * Xs n ^ 3
/-- node (gate) count bound -/
def nodesE (r n : ℕ) : ℕ := 828 * (r + 1) * Xs n ^ 2
/-- top width `(K U + g P) / K^3`, `P = U / g + Wm` -/
def LtopE (r : ℕ) (K g n : ℕ) : ℕ := ltopOf (Ub r n) (Wm r n) K g
/-- cluster width `P` -/
def Pb (r : ℕ) (g n : ℕ) : ℕ := Ub r n / g + Wm r n
def eFamE (r : ℕ) (K g n : ℕ) : ℕ := eOf (Ub r n) (Wm r n) (Sb n) K g

theorem Xs_pos (n : ℕ) : 1 ≤ Xs n := Nat.one_le_two_pow

/-- The requirements of the edge family on the value bound `V` (the arithmetic part of Rudich's `TopReq`). -/
structure EdgeReq (r V m K0 ℓ n : ℕ) : Prop where
  hm : 1 < m
  hset : 2 ^ Sb n ≤ V
  mm : m * m ≤ V
  hn : 16 * n + 4 ≤ V
  hK3 : 64 * Kb K0 ℓ ^ 3 ≤ V
  hKg : Kb K0 ℓ ^ Gs K0 ℓ ≤ V
  hKG : Kb K0 ℓ * Gs K0 ℓ ≤ V
  hgg : Gs K0 ℓ * Gs K0 ℓ ≤ V
  hg1 : 2 * Gs K0 ℓ + 1 ≤ V
  hgN : Gs K0 ℓ * nodesE r n ≤ V
  hWc : 2 ^ Pb r (Gs K0 ℓ) n ≤ V
  hgrp : 2 ^ (Pb r (Gs K0 ℓ) n * (2 * Gs K0 ℓ / Kb K0 ℓ)) ≤ V
  hLK : 2 ^ (LtopE r (Kb K0 ℓ) (Gs K0 ℓ) n * Kb K0 ℓ) ≤ V
  deep : DeepReq V m K0 ℓ (LtopE r (Kb K0 ℓ) (Gs K0 ℓ) n)

theorem EdgeReq.mono {r V W m K0 ℓ n : ℕ} (h : EdgeReq r V m K0 ℓ n) (hVW : V ≤ W) :
    EdgeReq r W m K0 ℓ n :=
  ⟨h.hm, h.hset.trans hVW, h.mm.trans hVW, h.hn.trans hVW, h.hK3.trans hVW, h.hKg.trans hVW,
    h.hKG.trans hVW, h.hgg.trans hVW, h.hg1.trans hVW, h.hgN.trans hVW, h.hWc.trans hVW,
    h.hgrp.trans hVW, h.hLK.trans hVW, UCost.DeepReq.mono hVW _ _ h.deep⟩

/-- **The ECDLP edge-network family.** -/
def edgeFamily (r : ℕ) : NetFamily where
  c := cE r
  hc := by unfold cE; omega
  X := Xs
  hX := Xs_pos
  nodes := nodesE r
  Ltop := LtopE r
  eFam := eFamE r
  FamOK V m K0 ℓ n := EdgeReq r V m K0 ℓ n

theorem edge_eTop (r K0 ℓ n mb : ℕ) :
    (edgeFamily r).eTop K0 ℓ n mb = Sb n + Pb r (Gs K0 ℓ) n + Pb r (Gs K0 ℓ) n * (2 * Gs K0 ℓ / Kb K0 ℓ) +
      LtopE r (Kb K0 ℓ) (Gs K0 ℓ) n * Kb K0 ℓ +
      (Gs K0 ℓ + 4) * (Nat.log 2 (mb + 16 * n + Kb K0 ℓ + Gs K0 ℓ + nodesE r n + 64) + 1) := by
  unfold NetFamily.eTop NetFamily.ePoly edgeFamily eFamE eOf Pb LtopE
  rfl

/-! ### The Props -/

theorem Xs_n_le (n : ℕ) : n ≤ 4 * Xs n ^ 4 := n_le_S n
theorem Xs_X4_le (n : ℕ) : Xs n ^ 4 ≤ 4 * n + 4 := S_le_n n

theorem total_le_E (r K g n : ℕ) (hK : 1 ≤ K) :
    K ^ 2 * LtopE r K g n ≤ cE r * Xs n ^ 4 + cE r * (g * Xs n ^ 3) := by
  have h := ltop_bound (Ub r n) (Wm r n) K g hK
  unfold LtopE Ub Wm Uc Wcn at h ⊢
  unfold cE
  nlinarith [Nat.zero_le ((r + 1) * Xs n ^ 4), Nat.zero_le (g * (r + 1) * Xs n ^ 3)]

theorem eFam_le_E (r K g n : ℕ) (hK2 : 2 ≤ K) (hKg : K ≤ g) :
    K * eFamE r K g n ≤ cE r * Xs n ^ 4 + K * (cE r * (g * Xs n ^ 3) + cE r * Xs n ^ 3) := by
  have h := eOf_bound (Ub r n) (Wm r n) (Sb n) K g hK2 hKg
  unfold eFamE
  unfold Ub Wm Sb Uc Wcn Scn at h ⊢
  unfold cE
  have h1 : 0 ≤ (r + 1) * Xs n ^ 4 := Nat.zero_le _
  have h2 : K * ((r + 1) * Xs n ^ 3) ≤ K * (g * ((r + 1) * Xs n ^ 3)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have h3 : g * ((r + 1) * Xs n ^ 3) ≤ K * (g * ((r + 1) * Xs n ^ 3)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  nlinarith [Nat.zero_le (K * ((r + 1) * Xs n ^ 3)), Nat.zero_le (g * ((r + 1) * Xs n ^ 3))]

theorem nodes_le_E (r n : ℕ) : nodesE r n ≤ cE r * Xs n ^ 4 := by
  unfold nodesE cE
  have h : Xs n ^ 2 ≤ Xs n ^ 4 := Nat.pow_le_pow_right (Xs_pos n) (by norm_num)
  nlinarith [Nat.zero_le ((r + 1) * Xs n ^ 2)]

end ECDLP.L65
