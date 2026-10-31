import ECDLP.L95_Inst

/-!
# L95 / Real: `instEx2` (L83's `instEx` with the repaired prelude), `heps_real2`, `instFV_real2`, `kindsReal2'`
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L95
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L83 ECDLP.L90

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}

/-- **`InstEx` of the real network with the repaired prelude** (same type as L83's `instEx`) -/
def instEx2 (u : ℕ) (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) :
    InstEx (layOf (sgR n ℓ π)) (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) B Ctx A u where
  nIE := .lit (24 * n + 23)
  KE := .lit (18 * n + 12)
  AE := AEx2 u
  hE := hEx2 u
  pbE := pbEx2 u
  bE := bEx2 u
  ncE := ncEx n u
  MeE := MEx2 u
  hnI _ _ _ _ := rfl
  hK _ _ _ _ := rfl
  hA σ₀ hC σ hσ := eval_AEx2 u (reads_ag hB hR hC hσ)
  hh σ₀ hC σ hσ := eval_hEx2 u (reads_ag hB hR hC hσ)
  hpb σ₀ hC σ hσ := eval_pbEx2 u (reads_ag hB hR hC hσ)
  hbv σ₀ hC σ hσ := eval_bEx2 u (reads_ag hB hR hC hσ)
  hnc σ₀ hC σ hσ c hc := eval_ncEx (reads_ag hB hR hC hσ) ((cnEquiv n).symm c) (by rw [hc]; exact cn_symm c)
  hMe σ₀ hC σ hσ c hc := eval_MEx2 u (reads_ag hB hR hC hσ)

variable (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

theorem instFV_real2 : ECDLP.L79.InstFV (instEx2 (n := n) u hB hR) :=
  ⟨fv_AEx2 u _ (by omega), fv_hEx2 u _ (by omega), fv_pbEx2 u _ (by omega), trivial, trivial, fv_bEx2 u _ (by omega),
    fv_ncEx n u _ (by omega) (Or.inr rfl), fv_MEx2 u _ (by omega)⟩

include hB hR hu in
theorem heps_real2 : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin (18 * n + 12)), σ' (u + 15) = c.val →
    ∀ t (ht : t < (frF (sgR n ℓ π) (cnEquiv n) c).n),
      Rp (Function.update σ' (u + 43) t) A (epsEx2 u n (u + 15) (u + 43))
        ((((frF (sgR n ℓ π) (cnEquiv n) c).ε ⟨t, ht⟩ : ℤ) : (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).Rg)) := by
  intro σ₀ hC σ' hσ c hc t ht
  have gτ : Ag B σ₀ (Function.update σ' (u + 43) t) := hσ.upd (by omega) _
  have hM := eval_MEx2 u (reads_ag hB hR hC gτ)
  obtain ⟨hl, hr, hε⟩ := term_real hB hR hu σ₀ hC σ' hσ c hc t ht
  have hq : 1 < 2 ^ (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M + 1 := by
    have := Nat.one_le_two_pow (n := (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M); omega
  haveI : Fact (1 < 2 ^ (NP (NParE (Nat.size p)) (fun _ => wP (Nat.size p)) c).M + 1) := ⟨hq⟩
  unfold Rp
  rcases hε with ⟨h1, h0⟩ | ⟨h1, h0⟩
  · simp only [epsEx2, Ex.eval, h0] at *
    rw [h1]
    simp only [Int.cast_one]
    exact (ZMod.val_one _).symm
  · simp only [epsEx2, Ex.eval, h0] at *
    rw [h1]
    simp only [eval_pow2, hM]
    rw [if_neg (by omega)]
    simp only [eval_pow2, hM, Int.cast_neg, Int.cast_one]
    exact (ZMod.val_neg_one _).symm.trans rfl

/-- **`Kinds` of the real network (repaired prelude), for every prefix** (no `hne`) -/
def kindsReal2' (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop) :
    Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu) :=
  kindsC' (instEx2 (n := n) u hB hR) (phiExInst u hB hR) hu (fun c => M_pos c) (hne_real (sgR n ℓ π)) (fun c => wP_pos _)
    (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43)) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx2 n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real2 hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)

theorem kindsReal2'_outE (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop) :
    (kindsReal2' (ℓ := ℓ) (π := π) hB hR hu m ok).fa.outE =
        ECDLP.L79.guardE u (ECDLP.L79.faKindEC (u := u) (ECDLP.L79.phiWrap u (phiExInst (n := n) u hB hR).phiE)) ∧
    (kindsReal2' (ℓ := ℓ) (π := π) hB hR hu m ok).mid.outE =
        ECDLP.L79.guardE u (ECDLP.L79.midKindEC (u := u) (nEx n (u + 15)) (epsEx2 u n (u + 15) (u + 43))
          (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))) ∧
    (kindsReal2' (ℓ := ℓ) (π := π) hB hR hu m ok).ib.outE = ECDLP.L79.ibOutIC (u := u) := ⟨rfl, rfl, rfl⟩

end
end ECDLP.L95
end
