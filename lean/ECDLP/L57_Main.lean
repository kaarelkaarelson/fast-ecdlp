import ECDLP.L57_Param
import FactoringAux.EngineGroup

/-!
# L57 / Main: the engine's size conditions for the coarsened `edgeNet`

`edgeNet_engine_fits`: under explicit parameter inequalities, for every cluster count `G` with `G⁴ ≤ L` the
network `edgeNet` (enumerated by any `e`) can be coarsened into `G` clusters with
* `Net.Fits P` (the hypothesis `hfit` of Rudich's `good_exists` / `Net.lemma1`),
* `Net.total ≤ C₁ m L` (`htot`),
* `G · P ≤ (C₁ m + cw θ) L`,
* the same value as `edgeNet`, which is the count of `edge_value` (under `SizeOK`, `1 ≤ b`).
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

open Classical in
/-- **Engine size conditions for the coarsened child-specific-message network.**
Parameters: `D = 2^k`; `b ≤ β D` digit bits; `w c ≤ ω` (`M_c = D · w c`); `≤ nmax` slots per identity;
`≤ occmax` identities per shared slot; `K ≤ κ m`; `D² ≤ ν L`; `4 ν³ ≤ θ⁴`; `G⁴ ≤ L`. -/
theorem edgeNet_engine_fits (nmax occmax β ω κ ν θ m L G : ℕ)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax)
    (hw : ∀ c, w c ≤ ω) (hb : N0.b ≤ β * 2 ^ N0.k) (hDL : 2 ^ N0.k * 2 ^ N0.k ≤ ν * L)
    (hK : K ≤ κ * m) (hθ : 4 * ν ^ 3 ≤ θ ^ 4) (hG : 0 < G) (hG4 : G ^ 4 ≤ L)
    (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb1 : 1 ≤ N0.b)
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∃ χ : Fin g → Fin G,
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).Fits
          ((κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) / G +
            ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k)) ∧
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).total ≤
          κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L ∧
      G * ((κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) / G +
            ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k)) ≤
          (κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m +
            ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * θ) * L ∧
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).value =
        ((univ.filter fun d : ι → Fin N0.A → Dg N0 =>
          (∀ i s, ok i s (d i s)) ∧
            ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card : ℤ) := by
  have hmax := Bw_le (w := w) φ occmax nmax β ω hn hocc hw hb
  obtain ⟨χ, h1, h2, h3⟩ := edgeNet_fits (w := w) φ F ok e G hG _ hmax
  have hW := Wsum_le (N0 := N0) (w := w) nmax β ω κ ν m L hn hw hb hDL hK
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro a
    refine (h1 a).trans ?_
    exact Nat.add_le_add_right (Nat.div_le_div_right hW) _
  · exact h2.trans hW
  · have hq := quartic_bound N0.A (2 ^ N0.k) ν θ G L (hA_dd N0) hDL hθ hG4
    calc _ ≤ (κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) +
          G * (((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k)) := by
          rw [Nat.mul_add]
          exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
      _ ≤ (κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) +
          ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (θ * L) := by
          refine Nat.add_le_add_left ?_ _
          calc G * (((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k))
              = ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (G * (N0.A * 2 ^ N0.k)) := by ring
            _ ≤ _ := Nat.mul_le_mul_left _ hq
      _ = _ := by ring
  · rw [h3]
    exact edge_value (w := w) φ F ok hS hb1 e

open Classical in
/-- **Interface with Rudich's engine.**  With `G = 3 K₀⁸` clusters (`K₀ ≥ 2`, `G⁴ ≤ L`) the coarsened network
is a `Net ℤ G` to which `Factoring.Aux.good_exists` (Lemma 1 by codes) applies with `P₀ = Fits` bound and
`U₀ = C₁ m L`: a good grouping code into `K₀` groups exists, every pair of groups sharing at most
`(K₀ U₀ + G P₀) / K₀³` bits. -/
theorem edgeNet_good_code (nmax occmax β ω κ ν θ m L G K₀ : ℕ)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax)
    (hw : ∀ c, w c ≤ ω) (hb : N0.b ≤ β * 2 ^ N0.k) (hDL : 2 ^ N0.k * 2 ^ N0.k ≤ ν * L)
    (hK : K ≤ κ * m) (hθ : 4 * ν ^ 3 ≤ θ ^ 4) (hK0 : 2 ≤ K₀) (hGeq : G = 3 * K₀ ^ 8) (hG4 : G ^ 4 ≤ L)
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∃ χ : Fin g → Fin G,
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).value =
        (((edgeNet (w := w) φ F ok).toGNet).toNet e).value ∧
      ∃ x < K₀ ^ G, okG ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ) K₀
          ((K₀ * (κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) +
            G * ((κ * ν * (4 * nmax * (β + ω + 5) + 12 * (ω + 4)) * m * L) / G +
              ((occmax + 1) * (β + 1) + (nmax + 3) * (ω + 4)) * (N0.A * 2 ^ N0.k))) / K₀ ^ 3)
          (by omega) x := by
  have hG : 0 < G := by rw [hGeq]; positivity
  have hmax := Bw_le (w := w) φ occmax nmax β ω hn hocc hw hb
  obtain ⟨χ, h1, h2, h3⟩ := edgeNet_fits (w := w) φ F ok e G hG _ hmax
  have hW := Wsum_le (N0 := N0) (w := w) nmax β ω κ ν m L hn hw hb hDL hK
  refine ⟨χ, h3, ?_⟩
  exact good_exists (((edgeNet (w := w) φ F ok).toGNet).toNet e |>.coarsen χ) _ _
    (fun a => (h1 a).trans (Nat.add_le_add_right (Nat.div_le_div_right hW) _)) (h2.trans hW) hK0 hGeq

end
end ECDLP.L57
end

#print axioms ECDLP.L57.edgeNet_engine_fits
#print axioms ECDLP.L57.edgeNet_good_code
