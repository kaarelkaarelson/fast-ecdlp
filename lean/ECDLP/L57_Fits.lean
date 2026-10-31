import ECDLP.L57_Edge

/-!
# L57 / Fits: the coarsened `edgeNet` meets the engine's size conditions (generic form)

`edgeNet_fits`: for every enumeration `e` of the gates and every cluster count `g > 0` there is a clustering `χ`
of the gates into `g` clusters such that the coarsened network
* has the same value as `edgeNet` (`Net.value_coarsen`),
* `Fits (Wsum / g + wmax)` (= Rudich's `Net.Fits`, the hypothesis `hfit` of `good_exists`/`lemma1`),
* has `total ≤ Wsum` (the hypothesis `htot`),
where `Wsum = Σ_c (2 n_c A eS + 2 n_c A² eM_c + 6 A² eM_c)` is a closed form and `wmax` is any bound of the gate
weights `Bw` (closed form).
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem rowsum_le {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    ∑ b, (((edgeNet (w := w) φ F ok).toGNet).toNet e).cc a b ≤ Bw (w := w) φ (e.symm a) := by
  rw [PForcedW.rowsum_eq]
  exact gate_le (w := w) φ F ok _

theorem edgeNet_fits {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (G : ℕ) (hG : 0 < G) (wmax : ℕ)
    (hmax : ∀ x : CG ι ιc N0.A, Bw (w := w) φ x ≤ wmax) :
    ∃ χ : Fin g → Fin G,
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).Fits
          (Wsum N0 w (fun c => Fintype.card (ιc c)) / G + wmax) ∧
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).total ≤ Wsum N0 w (fun c => Fintype.card (ιc c)) ∧
      ((((edgeNet (w := w) φ F ok).toGNet).toNet e).coarsen χ).value =
        (((edgeNet (w := w) φ F ok).toGNet).toNet e).value := by
  have hsum : ∑ a : Fin g, Bw (w := w) φ (e.symm a) = Wsum N0 w (fun c => Fintype.card (ιc c)) := by
    rw [Fintype.sum_equiv e.symm (fun a => Bw (w := w) φ (e.symm a)) (fun x => Bw (w := w) φ x) (fun _ => rfl)]
    exact sum_Bw φ
  obtain ⟨χ, h1, h2⟩ := exists_cluster (((edgeNet (w := w) φ F ok).toGNet).toNet e)
    (fun a => Bw (w := w) φ (e.symm a)) (rowsum_le φ F ok e) wmax (fun a => hmax _) G hG
  rw [hsum] at h1 h2
  exact ⟨χ, h1, h2, Net.value_coarsen _ χ⟩

end
end ECDLP.L57
end

#print axioms ECDLP.L57.edgeNet_fits
