import ECDLP.L44_Count

/-!
# L44 / Bij: counting valuations = counting `IntOK` solutions with sign and bit constraints
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst ECDLP.L34 ECDLP.L38

theorem toNat_lt_pow {z : ℤ} {bW : ℕ} (h0 : 0 ≤ z) (h : z < 2 ^ bW) : z.toNat < 2 ^ bW := by
  zify; rw [Int.toNat_of_nonneg h0]; exact_mod_cast h

variable {n K : ℕ} (I : Inst)

open Classical in
/-- **Counting.** -/
theorem count_corr (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool)) (bW : ℕ)
    (hcv0 : ∀ c, 0 ≤ I.cv c) (hcvB : ∀ c, I.cv c < 2 ^ bW)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p) (e : Cn n ≃ Fin K) :
    (univ.filter fun V : Slot n → Fin (2 ^ bW) =>
      (∀ s, ∀ jb ∈ Cl I bW sg xc s, ((V s : Fin _) : ℕ).testBit jb.1 = jb.2) ∧
        ∀ c : Fin K, HV (formF sg (e.symm c)) (fun s => ((V s : Fin _) : ℕ)) = 0).card =
    {t : IntAssign n | IOK I t ∧ SignOK I sg t ∧ XB xc t}.ncard := by
  have hc : ∀ c, (I.cv c).toNat < 2 ^ bW := fun c => toNat_lt_pow (hcv0 c) (hcvB c)
  rw [← Set.ncard_coe_finset]
  symm
  refine Set.ncard_congr
    (fun t ht s => (⟨(Vt I sg t s).toNat, toNat_lt_pow (Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)
      (Vt_lt I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)⟩ : Fin (2 ^ bW))) ?_ ?_ ?_
  · intro t ht
    have hcast : ∀ s, ((((⟨(Vt I sg t s).toNat, toNat_lt_pow (Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)
        (Vt_lt I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)⟩ : Fin (2 ^ bW)) : ℕ) : ℤ)) = Vt I sg t s :=
      fun s => Int.toNat_of_nonneg (Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)
    simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨(Cl_iff I bW sg xc (fun s => (Vt I sg t s).toNat) (fun s => toNat_lt_pow (Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)
      (Vt_lt I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)) hc).2 ⟨fun c => rfl, fun i hi => ?_, ?_⟩, fun c => ?_⟩
    · simp [Vt, tgv, hi]
    · exact ht.2.2
    · rw [HV_eq_HVz]
      have : (fun s => ((((⟨(Vt I sg t s).toNat, toNat_lt_pow (Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)
        (Vt_lt I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s)⟩ : Fin (2 ^ bW)) : ℕ) : ℤ))) = Vt I sg t :=
        funext hcast
      rw [this]
      exact corr_fwd I sg t ht.1 ht.2.1 _
  · intro t t' ht ht' h
    have h1 : ∀ s, Vt I sg t s = Vt I sg t' s := fun s => by
      have := congrArg (fun f => ((f s : Fin _) : ℕ)) h
      simp only at this
      have a := Vt_nonneg I hcv0 bW hcvB hXX sg t ht.1 ht.2.1 s
      have b := Vt_nonneg I hcv0 bW hcvB hXX sg t' ht'.1 ht'.2.1 s
      omega
    rw [← tOf_Vt I sg t, ← tOf_Vt I sg t', funext h1]
  · intro V hV
    simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hV
    obtain ⟨hcl, hform⟩ := hV
    obtain ⟨h1, h2, h3⟩ := (Cl_iff I bW sg xc _ (fun s => (Fin.is_lt _)) hc).1 hcl
    set W : Slot n → ℤ := fun s => (((V s : Fin _) : ℕ) : ℤ) with hW
    have hnn : ∀ s, 0 ≤ W s := fun s => by positivity
    have hk : ∀ c, W (.cst c) = I.cv c := fun c => by
      simp only [hW, h1 c]; exact Int.toNat_of_nonneg (hcv0 c)
    have htg : ∀ i, sg i = .none → W (.tg i) = 0 := fun i hi => by simp [hW, h2 i hi]
    have hz : ∀ c : Cn n, HVz (formF sg c) W = 0 := fun c => by
      have := hform (e c)
      rw [Equiv.symm_apply_apply, HV_eq_HVz] at this
      exact this
    obtain ⟨hI, hS, hWV⟩ := corr_bwd I sg W hnn hk htg hz
    refine ⟨tOf W, ⟨hI, hS, fun i jb hjb => ?_⟩, ?_⟩
    · have := h3 i jb hjb
      simp only [tOf, hW, Int.toNat_natCast]
      exact this
    · funext s
      apply Fin.ext
      show (Vt I sg (tOf W) s).toNat = _
      rw [← hWV]
      simp [hW]

end ECDLP.L44
end
