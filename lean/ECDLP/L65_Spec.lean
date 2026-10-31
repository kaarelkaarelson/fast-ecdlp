import ECDLP.L65_Fam

/-!
# L65 / Spec: `edgeFamily r` satisfies L60's `NetFamily.Spec`

All seven fields.  `req_of_exp` is Rudich's `topReq_of` re-run for `EdgeReq` (the exponent bound
`eTop ≤ Z`, the chain bound `DeepE` and `2^Z ≤ V` give every requirement).  NOTE: this is a statement about the
explicit requirement list `EdgeReq`; that these requirements suffice for the evaluation cost bound is
the separate hypothesis `τ` (see `L65_Rate`).
-/
namespace ECDLP.L65
open Factoring.Aux ECDLP.L60

theorem edgeReq_of {r V m mb K0 ℓ n Z : ℕ} (hK : 2 ≤ K0) (hm : 1 < m) (hmb : m ≤ mb)
    (hZ : (edgeFamily r).eTop K0 ℓ n mb ≤ Z)
    (hD : DeepE Z mb K0 ℓ (LtopE r (Kb K0 ℓ) (Gs K0 ℓ) n)) (hV : 2 ^ Z ≤ V) :
    EdgeReq r V m K0 ℓ n := by
  rw [edge_eTop] at hZ
  have hZ1 : (Gs K0 ℓ + 4) * (Nat.log 2 (mb + 16 * n + Kb K0 ℓ + Gs K0 ℓ + nodesE r n + 64) + 1) ≤ Z :=
    le_trans (by omega) hZ
  set K := Kb K0 ℓ with hKdef
  set g := Gs K0 ℓ with hgdef
  set B := mb + 16 * n + K + g + nodesE r n + 64 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hg : 1 ≤ g := by
    show 1 ≤ 3 * K ^ 8; have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have h2 : ∀ a, a ≤ Sb n + Pb r g n + Pb r g n * (2 * g / K) + LtopE r K g n * K → 2 ^ a ≤ V := fun a ha =>
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : a ≤ Z)) hV
  have hPV : B ^ (g + 4) ≤ V := by
    refine le_trans (pow_le_two_pow_log B (g + 4)) ?_
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hZ1) hV
  have hBe : ∀ x i, x ≤ B ^ i → i ≤ g + 4 → x ≤ V := fun x i hx hi =>
    le_trans (le_pow_of_le hB1 hx hi) hPV
  have hB2 : B ^ 2 = B * B := by ring
  have mul2 : ∀ x y, x ≤ B → y ≤ B → x * y ≤ B ^ 2 := fun x y hx hy => by rw [hB2]; exact Nat.mul_le_mul hx hy
  have hKB : K ≤ B := by omega
  have hgB : g ≤ B := by omega
  have h64 : 64 ≤ B := by omega
  exact
    { hm := hm
      hset := h2 (Sb n) (by omega)
      mm := hBe _ 2 (mul2 _ _ (by omega) (by omega)) (by omega)
      hn := hBe _ 1 (by rw [pow_one]; omega) (by omega)
      hK3 := by
        refine hBe _ 4 ?_ (by omega)
        have k3 : K ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left hKB 3
        calc 64 * K ^ 3 ≤ B * B ^ 3 := Nat.mul_le_mul h64 k3
          _ = B ^ 4 := by ring
      hKg := hBe _ g (Nat.pow_le_pow_left hKB g) (by omega)
      hKG := hBe _ 2 (mul2 _ _ hKB hgB) (by omega)
      hgg := hBe _ 2 (mul2 _ _ hgB hgB) (by omega)
      hg1 := hBe _ 2 (by
        have : 3 * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
        rw [hB2]; omega) (by omega)
      hgN := hBe _ 2 (mul2 _ _ hgB (show nodesE r n ≤ B by omega)) (by omega)
      hWc := h2 (Pb r g n) (by omega)
      hgrp := h2 (Pb r g n * (2 * g / K)) (by omega)
      hLK := h2 (LtopE r K g n * K) (by omega)
      deep := deepReq_of hm hmb hK hV ℓ _ hD }

/-- **The size interface for the ECDLP edge family.** -/
theorem edgeFamily_spec (r : ℕ) : (edgeFamily r).Spec where
  n_le n := by
    show n ≤ cE r * Xs n ^ 4
    have := Xs_n_le n
    unfold cE
    nlinarith [Nat.zero_le (r * Xs n ^ 4)]
  X4_le n := by
    show Xs n ^ 4 ≤ cE r * n + cE r
    have := Xs_X4_le n
    unfold cE
    nlinarith [Nat.zero_le (r * n), Nat.zero_le r]
  nodes_le n := nodes_le_E r n
  total_le K g n hK := total_le_E r K g n hK
  eFam_le K g n h2 h3 := eFam_le_E r K g n h2 h3
  req_of_exp {V m mb K0 ℓ n Z} hK hm hmb hZ hD hV := edgeReq_of hK hm hmb hZ hD hV
  ok_mono h hVW := EdgeReq.mono h hVW

end ECDLP.L65
