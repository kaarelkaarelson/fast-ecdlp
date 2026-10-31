import ECDLP.L83_Mid
import ECDLP.L68_Ring

/-!
# L83 / Orc: the Ag-form oracle hypotheses of L79's `midKindC` / `kindsC` for the real network

`hn_real, heps_real, hl_real, hr_real` are, verbatim, the hypotheses `hn heps hl hr` of `kindsC` for
`F = frF (sgR n l pi) (cnEquiv n)`, `L = layOf (sgR n l pi)`, `N0 = NParE (size p)`, `w = fun _ => wP (size p)`,
with `nE = nEx n (u+15)`, `epsE = epsEx n (u+15) (u+43) u`, `lE = lEx n (u+15) (u+43)`, `rE = rEx n (u+15) (u+43)`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

include hB hR hu

theorem hn_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    Ex.eval σ' A (nEx n (u + 15)) = (frF (sgR n ℓ π) (cnEquiv n) c).n := by
  intro σ₀ hC σ hσ c hc
  exact eval_nEx (u + 15) (reads_ag hB hR hC hσ) ((cnEquiv n).symm c) (by rw [hc]; exact cn_symm c)

theorem term_real (σ₀ : ℕ → ℕ) (hC : Ctx σ₀) (σ' : ℕ → ℕ) (hσ : Ag B σ₀ σ') (c : Fin (18 * n + 12)) (hc : σ' (u + 15) = c.val)
    (t : ℕ) (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n) :
    let τ := Function.update σ' (u + 43) t
    Ex.eval τ A (lEx n (u + 15) (u + 43)) = ((layOf (sgR n ℓ π)).ecc c ((frF (sgR n ℓ π) (cnEquiv n) c).l ⟨t, ht⟩) : ℕ) ∧
    Ex.eval τ A (rEx n (u + 15) (u + 43)) = ((layOf (sgR n ℓ π)).ecc c ((frF (sgR n ℓ π) (cnEquiv n) c).r ⟨t, ht⟩) : ℕ) ∧
    ((((frF (sgR n ℓ π) (cnEquiv n) c).ε ⟨t, ht⟩ : ℤ) = 1 ∧ Ex.eval τ A (negEx n (u + 15) (u + 43)) = 0) ∨
     (((frF (sgR n ℓ π) (cnEquiv n) c).ε ⟨t, ht⟩ : ℤ) = -1 ∧ Ex.eval τ A (negEx n (u + 15) (u + 43)) = 1)) := by
  intro τ
  have gτ : Ag B σ₀ τ := hσ.upd (by omega) _
  have h1 : τ (u + 15) = c.val := by simp only [τ]; rw [Function.update_of_ne (by omega)]; exact hc
  have h2 : τ (u + 43) = t := by simp only [τ]; exact Function.update_self ..
  have ht' : t < (formL (sgR n ℓ π) ((cnEquiv n).symm c)).length := ht
  have hg := List.getElem?_eq_getElem ht'
  exact term_spec (u + 15) (u + 43) (reads_ag hB hR hC gτ) ((cnEquiv n).symm c) (by rw [h1]; exact cn_symm c) t h2 _ _ _ hg

theorem hl_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Ex.eval (Function.update σ' (u + 43) t) A (lEx n (u + 15) (u + 43)) =
        ((layOf (sgR n ℓ π)).ecc c ((frF (sgR n ℓ π) (cnEquiv n) c).l ⟨t, ht⟩) : ℕ) :=
  fun σ₀ hC σ' hσ c hc t ht => (term_real hB hR hu σ₀ hC σ' hσ c hc t ht).1

theorem hr_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Ex.eval (Function.update σ' (u + 43) t) A (rEx n (u + 15) (u + 43)) =
        ((layOf (sgR n ℓ π)).ecc c ((frF (sgR n ℓ π) (cnEquiv n) c).r ⟨t, ht⟩) : ℕ) :=
  fun σ₀ hC σ' hσ c hc t ht => (term_real hB hR hu σ₀ hC σ' hσ c hc t ht).2.1

theorem heps_real : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Rp (Function.update σ' (u + 43) t) A (epsEx n (u + 15) (u + 43) u)
        ((((frF (sgR n ℓ π) (cnEquiv n) c).ε ⟨t, ht⟩ : ℤ) : (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).Rg)) := by
  intro σ₀ hC σ' hσ c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ.upd (by omega) _
  have hM := eval_MEx u (reads_ag hB hR hC gτ)
  obtain ⟨hl, hr, hε⟩ := term_real hB hR hu σ₀ hC σ' hσ c hc t ht
  have hq : 1 < 2 ^ (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M + 1 := by
    have := Nat.one_le_two_pow (n := (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M); omega
  haveI : Fact (1 < 2 ^ (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M + 1) := ⟨hq⟩
  unfold Rp
  rcases hε with ⟨h1, h0⟩ | ⟨h1, h0⟩
  · simp only [epsEx, Ex.eval, h0] at *
    rw [h1]
    simp only [Int.cast_one]
    exact (ZMod.val_one _).symm
  · simp only [epsEx, Ex.eval, h0] at *
    rw [h1]
    simp only [eval_pow2, hM]
    rw [if_neg (by omega)]
    simp only [eval_pow2, hM, Int.cast_neg, Int.cast_one]
    exact (ZMod.val_neg_one _).symm.trans rfl

end
end ECDLP.L83
end
