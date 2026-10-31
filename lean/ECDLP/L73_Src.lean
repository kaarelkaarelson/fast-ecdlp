import ECDLP.L73_Child
import ECDLP.L73_Iface

/-!
# L73 / Src: the message of a source node is its free value; the setting code of a node without parents is the code of its free value
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  (φ : ∀ c, ιc c → ι) (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop) (m : ℕ)

/-- node level: the code of the message of a source node is the code of its free value -/
theorem out_src_q (i : ι) (s : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.src i s)
    (z : (edgeNetM (w := w) φ F ok m).S q) (ch : CG ι ιc N0.A) :
    ec (ι := ι) (ιc := ιc) (w := w) q ((edgeNetM (w := w) φ F ok m).out q z ch) =
      ((edgeEFM φ F ok m q z.1 : Fin _) : ℕ) := by
  subst hq
  rfl

theorem zcode_noparent {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g)
    (hpa : (edgeNetM (w := w) φ F ok m).pa (e.symm a) = ∅)
    (z : (edgeNetM (w := w) φ F ok m).S (e.symm a)) :
    zcode (w := w) (φ := φ) (F := F) (ok := ok) m e a z = ((edgeEFM φ F ok m (e.symm a) z.1 : Fin _) : ℕ) := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  obtain ⟨x, ms⟩ := z
  unfold zcode
  have h1 := code_eq (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e a x ms
  have hn : ∀ k, nA (edgeNetM (w := w) φ F ok m) e a k = 1 := by
    intro k
    by_cases hk : k < g
    · have : e.symm ⟨k, hk⟩ ∉ (edgeNetM (w := w) φ F ok m).pa (e.symm a) := by rw [hpa]; simp
      have := nA_npar (edgeNetM (w := w) φ F ok m) e (a := a) (k := ⟨k, hk⟩) this
      simpa using this
    · unfold nA; simp [a.2, hk]
  have h2 : pp (nA (edgeNetM (w := w) φ F ok m) e a) g = 1 := by
    rw [pp_congr (f' := fun _ => 1) (fun i _ => hn i), pp_const]; simp
  have h4 : ((codeEquiv (nA (edgeNetM (w := w) φ F ok m) e a) g
      fun i _ => nA_pos (edgeNetM (w := w) φ F ok m) e a i) (msgsEquiv (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) e a ms) : ℕ) <
      1 := lt_of_lt_of_eq (Fin.is_lt _) h2
  show ((pfCoding _ _ _ e).e a (x, ms) : ℕ) = _
  rw [h1]
  have : ((codeEquiv (nA (edgeNetM (w := w) φ F ok m) e a) g
      fun i _ => nA_pos (edgeNetM (w := w) φ F ok m) e a i) (msgsEquiv (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) e a ms) : ℕ) = 0 := by
    omega
  rw [this]; simp

end
end ECDLP.L73
end
