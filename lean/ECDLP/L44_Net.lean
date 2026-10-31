import ECDLP.L44_Bij

/-!
# L44 / Net: the packed network for L30's integer system

`net_value`: `Net.value` of `gadgetNet N (combine F B) (okC N (Cl ..))` for the family `F c = formF sg (e.symm c)` of
the identities of L30's system (+ range slacks, sign slacks), with pinned constants and `x`-bit constraints,
equals the number of `IntAssign`s with `IntOK`, `SignOK` and `XB`.
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst ECDLP.L34 ECDLP.L35 ECDLP.L38

variable {n K : ℕ} (I : Inst)

/-- the family of identities as a `Fin K`-indexed family -/
def famF (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) : Form (Slot n) := formF sg (e.symm c)

open Classical in
theorem net_value (N : NPar) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool)) (e : Cn n ≃ Fin K)
    (hcv0 : ∀ c, 0 ≤ I.cv c) (hcvB : ∀ c, I.cv c < 2 ^ (N.b * 2 ^ N.k))
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hxc : ∀ i, ∀ jb ∈ xc i, jb.1 < N.b * 2 ^ N.k)
    (B : ℤ) (hB : 0 < B)
    (hBd : ∀ c, ((famF sg e c).mass : ℤ) * ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B)
    (hS : N.SizeOK (combine (famF sg e) B)) (hb : 1 ≤ N.b) {g : ℕ} (eg : Gate (Slot n) N.A ≃ Fin g) :
    (((gadgetNet N (combine (famF sg e) B)
        (okC N (Cl I (N.b * 2 ^ N.k) sg xc))).toForced.toGNet).toNet eg).value =
      (({t : IntAssign n | IOK I t ∧ SignOK I sg t ∧ XB xc t}.ncard : ℕ) : ℤ) := by
  have hC : ∀ s, ∀ jb ∈ Cl I (N.b * 2 ^ N.k) sg xc s, jb.1 < N.b * 2 ^ N.k := by
    intro s jb hjb
    cases s with
    | cst c => simp only [Cl, pinList, List.mem_map, List.mem_range] at hjb
               obtain ⟨j, hj, rfl⟩ := hjb; exact hj
    | tg i =>
      cases hg : sg i
      · simp only [Cl, hg, pinList, List.mem_map, List.mem_range] at hjb
        obtain ⟨j, hj, rfl⟩ := hjb; exact hj
      · simp [Cl, hg] at hjb
      · simp [Cl, hg] at hjb
    | v a => cases a with
      | x i => exact hxc i jb hjb
      | _ => simp [Cl] at hjb
    | sl a => simp [Cl] at hjb
    | u i => simp [Cl] at hjb
  rw [system_value_V N (famF sg e) (Cl I (N.b * 2 ^ N.k) sg xc) hC B hB hBd hS hb eg,
    ← count_corr I sg xc (N.b * 2 ^ N.k) hcv0 hcvB hXX e]
  rfl

end ECDLP.L44
end

#print axioms ECDLP.L44.net_value
