import FactoringAux.UniMain

/-!
# L60: an abstract network family for Rudich's cost/exponent layer

`NetFamily` bundles what the uniform engine's cost/exponent layer (Rudich: `TopReq`, `UniReq`, `eTop`,
`Ltop`, `Ntn`, `Wn`, `mbn`, `Mof`, `mainReq_of`) takes from the factoring network: a size scale `X n`
(Rudich `2^(sOf n)`), a node count, the top width `Ltop K g n`, the exponent `eFam` of the top's value
bounds, and the requirement predicate `FamOK`.  `NetFamily.Spec` is the size interface (Props): total and
per-cluster sizes `O(n)`, in exactly the form Rudich's `Ntop_S`, `eTop_le`, `S_le_n`, `n_le_S`,
`mulNodes_le`, `topReq_of` give for the multiplication network.

Originals: `FactoringAux/EngineCostReq.lean` (eTop, topReq_of, mainReq_of), `EngineCostMain.lean`
(Mof, MainReq), `EngineCostFinal.lean` (Ntn, Wn, W0n, mbn, cWn, cmbn, chain_hyp1/2, Wn_le, mbn_le),
`UniCost.lean` (UniReq).
-/

namespace ECDLP.L60

open Factoring.Aux

/-- An abstract network family at the top of the uniform engine (data). -/
structure NetFamily where
  /-- the constant of the size interface -/
  c : ℕ
  hc : 1 ≤ c
  /-- size scale at input length `n` (Rudich: `2 ^ sOf n`) -/
  X : ℕ → ℕ
  hX : ∀ n, 1 ≤ X n
  /-- number of nodes of the top network (Rudich: `mulNodes (sOf n)`) -/
  nodes : ℕ → ℕ
  /-- top width of the clustered network: `K` = group count, `g` = cluster count, `n` = input length
  (Rudich: `Ltop K g (sOf n)`) -/
  Ltop : ℕ → ℕ → ℕ → ℕ
  /-- the exponents of the value bounds of the top, without the `ePoly` part (Rudich: the first six
  summands of `eTop`) -/
  eFam : ℕ → ℕ → ℕ → ℕ
  /-- the requirement on the value bound `V` at modulus `m`, `K0`, `ℓ` levels, input length `n`
  (Rudich: `UCost.TopReq`); includes the chain's `DeepReq` -/
  FamOK : ℕ → ℕ → ℕ → ℕ → ℕ → Prop

namespace NetFamily

variable (F : NetFamily)

/-- The polynomial exponent of the top (Rudich `ePolyT`). -/
def ePoly (K g n mb : ℕ) : ℕ := (g + 4) * (Nat.log 2 (mb + 16 * n + K + g + F.nodes n + 64) + 1)

/-- All exponents of the top (Rudich `eTop`). -/
def eTop (K0 ℓ n mb : ℕ) : ℕ :=
  F.eFam (Kb K0 ℓ) (Gs K0 ℓ) n + F.ePoly (Kb K0 ℓ) (Gs K0 ℓ) n mb

/-- The modulus bound (Rudich `Mof`). -/
def Mof (K0 ℓ n : ℕ) : ℕ := n + mlogN K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n) + 4

def mbn (K0 ℓ n : ℕ) : ℕ := 2 * F.Mof K0 ℓ n + 1

/-- The top clique's bits, bounded (Rudich `Ntn`). -/
def Ntn (K0 ℓ n : ℕ) : ℕ := F.c * F.X n ^ 4 + F.c * (Gs K0 ℓ * F.X n ^ 3)
def Wn (K0 ℓ n : ℕ) : ℕ := F.Ntn K0 ℓ n + 2 * ℓ * Gm4 K0 ℓ
def W0n (K0 ℓ n : ℕ) : ℕ := 23 ^ ℓ * F.Ntn K0 ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0 ℓ
def cWn (K0 ℓ : ℕ) : ℕ := F.c + F.c * Gs K0 ℓ + 2 * ℓ * Gm4 K0 ℓ + 1
def cmbn (K0 ℓ : ℕ) : ℕ := 2 * F.c + 9 + 4 * ℓ * Gm4 K0 ℓ * F.cWn K0 ℓ

/-- **The size interface** (the Props the exponent layer consumes). -/
structure Spec : Prop where
  /-- total size `Θ(n)`: `n ≤ c X^4` and `X^4 ≤ c n + c` (Rudich `n_le_S`, `S_le_n`) -/
  n_le : ∀ n, n ≤ F.c * F.X n ^ 4
  X4_le : ∀ n, F.X n ^ 4 ≤ F.c * n + F.c
  /-- node count `O(n)` (Rudich `mulNodes_le`) -/
  nodes_le : ∀ n, F.nodes n ≤ F.c * F.X n ^ 4
  /-- the top clique's bits: total `O(X^4)` plus per-cluster overhead `g X^3` (Rudich `Ntop_S`) -/
  total_le : ∀ K g n, 1 ≤ K → K ^ 2 * F.Ltop K g n ≤ F.c * F.X n ^ 4 + F.c * (g * F.X n ^ 3)
  /-- the exponents of the value bounds times `K` (Rudich `eTop_le`) -/
  eFam_le : ∀ K g n, 2 ≤ K → K ≤ g →
    K * F.eFam K g n ≤ F.c * F.X n ^ 4 + K * (F.c * (g * F.X n ^ 3) + F.c * F.X n ^ 3)
  /-- the evaluation-cost interface: the exponents bound the requirement (Rudich `topReq_of`) -/
  req_of_exp : ∀ {V m mb K0 ℓ n Z : ℕ}, 2 ≤ K0 → 1 < m → m ≤ mb →
    F.eTop K0 ℓ n mb ≤ Z → DeepE Z mb K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n) → 2 ^ Z ≤ V →
    F.FamOK V m K0 ℓ n
  ok_mono : ∀ {V W m K0 ℓ n : ℕ}, F.FamOK V m K0 ℓ n → V ≤ W → F.FamOK W m K0 ℓ n

/-- Counting-expression requirements (Rudich `MainReq`). -/
structure MainReq (V K0 ℓ n : ℕ) : Prop where
  top : ∀ m, 2 ≤ m → m ≤ 2 * F.Mof K0 ℓ n + 1 → F.FamOK V m K0 ℓ n
  hM : 2 * F.Mof K0 ℓ n + 1 ≤ V

/-- Requirements of the uniform engine at input length `n` (Rudich `UniReq`). -/
structure UniReq (V n : ℕ) : Prop where
  main : F.MainReq V K0u (ellOf n) n
  np : NPof K0u (ellOf n) (F.Ltop (Kb K0u (ellOf n)) (Gs K0u (ellOf n)) n) ≤ V
  lv : lvlV (Kb K0u (ellOf n)) ≤ V
  small : n + ellOf n + 64 ≤ V
  kb : Kb K0u (ellOf n + 1) ^ 40 ≤ V

variable {F}

theorem MainReq.mono {V W K0 ℓ n : ℕ} (hS : F.Spec) (h : F.MainReq V K0 ℓ n) (hVW : V ≤ W) :
    F.MainReq W K0 ℓ n where
  top m h1 h2 := hS.ok_mono (h.top m h1 h2) hVW
  hM := le_trans h.hM hVW

/-- Rudich `mainReq_of`. -/
theorem mainReq_of (hS : F.Spec) {V K0 ℓ n Z : ℕ} (hK : 2 ≤ K0)
    (hZ : F.eTop K0 ℓ n (2 * F.Mof K0 ℓ n + 1) ≤ Z)
    (hD : DeepE Z (2 * F.Mof K0 ℓ n + 1) K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n)) (hV : 2 ^ Z ≤ V) :
    F.MainReq V K0 ℓ n where
  top m hm hmb := hS.req_of_exp hK (by omega) hmb hZ hD hV
  hM := by
    refine le_trans ?_ (le_trans (Nat.pow_le_pow_right (by norm_num) hZ) hV)
    have hg : 1 ≤ Gs K0 ℓ := by
      show 1 ≤ 3 * Kb K0 ℓ ^ 8; have := Nat.pow_pos (n := 8) (show 0 < Kb K0 ℓ by have := Kb_ge K0 hK ℓ; omega); omega
    refine le_trans (le_two_pow_log (2 * F.Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + F.nodes n + 64)).le
      (Nat.pow_le_pow_right (by norm_num) ?_) |>.trans' (by omega)
    unfold eTop ePoly
    have : Nat.log 2 (2 * F.Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + F.nodes n + 64) + 1 ≤
        (Gs K0 ℓ + 4) * (Nat.log 2 (2 * F.Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + F.nodes n + 64) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-! ### The chain hypotheses and the bounds `Wn`, `mbn` -/

theorem chain_hyp1 (hS : F.Spec) {K0 : ℕ} (hK : 48 ≤ K0) (ℓ n : ℕ) :
    Kb K0 ℓ ^ 2 * F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n + 2 * ℓ * Gm4 K0 ℓ ≤ F.Wn K0 ℓ n := by
  have := hS.total_le (Kb K0 ℓ) (Gs K0 ℓ) n (le_trans (by omega) (Kb_ge K0 (by omega) ℓ))
  unfold Wn Ntn; omega

theorem chain_hyp2 (hS : F.Spec) {K0 : ℕ} (hK : 48 ≤ K0) (ℓ n : ℕ) :
    23 ^ ℓ * (Kb K0 ℓ ^ 2 * F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n) +
      24 ^ ℓ * (2 * ℓ * Gm4 K0 ℓ) ≤ 24 ^ ℓ * F.W0n K0 ℓ n := by
  have h := hS.total_le (Kb K0 ℓ) (Gs K0 ℓ) n (le_trans (by omega) (Kb_ge K0 (by omega) ℓ))
  have h1 : 23 ^ ℓ * (Kb K0 ℓ ^ 2 * F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n) ≤ 23 ^ ℓ * F.Ntn K0 ℓ n :=
    Nat.mul_le_mul_left _ h
  have h2 : 23 ^ ℓ * F.Ntn K0 ℓ n < 24 ^ ℓ * (23 ^ ℓ * F.Ntn K0 ℓ n / 24 ^ ℓ + 1) := by
    have := Nat.div_add_mod (23 ^ ℓ * F.Ntn K0 ℓ n) (24 ^ ℓ)
    have := Nat.mod_lt (23 ^ ℓ * F.Ntn K0 ℓ n) (Nat.pow_pos (n := ℓ) (show 0 < 24 by norm_num))
    rw [mul_add, mul_one]; omega
  unfold W0n
  have e : 24 ^ ℓ * (23 ^ ℓ * F.Ntn K0 ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0 ℓ) =
      24 ^ ℓ * (23 ^ ℓ * F.Ntn K0 ℓ n / 24 ^ ℓ + 1) + 24 ^ ℓ * (2 * ℓ * Gm4 K0 ℓ) := by ring
  omega

theorem Wn_le (F : NetFamily) (K0 ℓ n : ℕ) : F.Wn K0 ℓ n + 1 ≤ F.cWn K0 ℓ * F.X n ^ 4 := by
  have h1 : 1 ≤ F.X n ^ 4 := Nat.one_le_pow _ _ (F.hX n)
  have h2 : F.X n ^ 3 ≤ F.X n ^ 4 := Nat.pow_le_pow_right (F.hX n) (by norm_num)
  have h3 : F.c * (Gs K0 ℓ * F.X n ^ 3) ≤ F.c * (Gs K0 ℓ * F.X n ^ 4) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
  have h4 : 2 * ℓ * Gm4 K0 ℓ + 1 ≤ (2 * ℓ * Gm4 K0 ℓ + 1) * F.X n ^ 4 := Nat.le_mul_of_pos_right _ h1
  unfold Wn Ntn cWn
  have e : (F.c + F.c * Gs K0 ℓ + 2 * ℓ * Gm4 K0 ℓ + 1) * F.X n ^ 4 = F.c * F.X n ^ 4 +
      F.c * (Gs K0 ℓ * F.X n ^ 4) + (2 * ℓ * Gm4 K0 ℓ + 1) * F.X n ^ 4 := by ring
  omega

theorem mbn_le (hS : F.Spec) {K0 : ℕ} (hK : 48 ≤ K0) (ℓ n : ℕ) :
    F.mbn K0 ℓ n ≤ F.cmbn K0 ℓ * F.X n ^ 4 := by
  have hm : mlogN K0 ℓ (F.Ltop (Kb K0 ℓ) (Gs K0 ℓ) n) ≤ 2 * ℓ * Gm4 K0 ℓ * (F.Wn K0 ℓ n + 1) :=
    mlogN_le K0 (F.Wn K0 ℓ n) (Gs K0 ℓ) hK ℓ _ (K_le_G _) (chain_hyp1 hS hK ℓ n)
  have hw := Wn_le F K0 ℓ n
  have hn := hS.n_le n
  have h1 : 1 ≤ F.X n ^ 4 := Nat.one_le_pow _ _ (F.hX n)
  have h5 : 2 * ℓ * Gm4 K0 ℓ * (F.Wn K0 ℓ n + 1) ≤ 2 * ℓ * Gm4 K0 ℓ * (F.cWn K0 ℓ * F.X n ^ 4) :=
    Nat.mul_le_mul_left _ hw
  unfold mbn Mof cmbn
  have e : (2 * F.c + 9 + 4 * ℓ * Gm4 K0 ℓ * F.cWn K0 ℓ) * F.X n ^ 4 = 2 * F.c * F.X n ^ 4 + 9 * F.X n ^ 4 +
      2 * (2 * ℓ * Gm4 K0 ℓ * (F.cWn K0 ℓ * F.X n ^ 4)) := by ring
  rw [e]
  have e2 : 2 * F.c * F.X n ^ 4 = 2 * (F.c * F.X n ^ 4) := by ring
  omega

end NetFamily

end ECDLP.L60
