import ECDLP.L38_Compose

/-!
# L44 / Value: from digit assignments to slot *values*

L38's `system_value` counts digit assignments `d : ι → Fin A → Fin h → Fin (2^b)`.  Here we pass to slot values
`V : ι → Fin (2^(b 2^k))` (`V i = numOf` of the digits of slot `i`), and express per-FA-gate checks `ok` as
bit constraints `testBit (V i) j = β` (`okC`).
-/
noncomputable section
namespace ECDLP.L44
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38

section
variable {ι : Type} (N : NPar)

/-- value of the slot with digit vector `u` -/
abbrev vl (u : Fin (2 ^ N.k) → Fin (2 ^ N.b)) : ℕ := N.toPar.val u

theorem vl_lt (u : Fin (2 ^ N.k) → Fin (2 ^ N.b)) : vl N u < 2 ^ (N.b * 2 ^ N.k) := val_lt N.toPar u

theorem dgt_vl (u : Fin (2 ^ N.k) → Fin (2 ^ N.b)) (m : Fin (2 ^ N.k)) :
    dgt N.b (vl N u) m = (u m : ℕ) := by
  unfold vl Par.val
  rw [dgt_numOf N.b (2 ^ N.k) (N.toPar.sq u) (N.toPar.sq_lt u), if_pos m.2]
  simp [Par.sq]

theorem vl_inj {u u' : Fin (2 ^ N.k) → Fin (2 ^ N.b)} (h : vl N u = vl N u') : u = u' := by
  funext m
  apply Fin.ext
  rw [← dgt_vl N u m, ← dgt_vl N u' m, h]

theorem vl_surj (v : ℕ) (hv : v < 2 ^ (N.b * 2 ^ N.k)) : ∃ u, vl N u = v := by
  refine ⟨fun m => ⟨dgt N.b v m, dgt_lt _ _ _⟩, ?_⟩
  have e : ∀ j, N.toPar.sq (fun m : Fin (2 ^ N.k) => (⟨dgt N.b v m, dgt_lt _ _ _⟩ : Fin (2 ^ N.b))) j
      = dgt N.b v j := by
    intro j
    unfold Par.sq
    split_ifs with h
    · rfl
    · exact (dgt_eq_zero_of_lt hv (by omega)).symm
  unfold vl Par.val
  rw [show N.toPar.sq (fun m : Fin (2 ^ N.k) => (⟨dgt N.b v m, dgt_lt _ _ _⟩ : Fin (2 ^ N.b))) = dgt N.b v
    from funext e]
  exact numOf_dgt N.b (2 ^ N.k) v hv

theorem b_pos {j : ℕ} (hj : j < N.b * 2 ^ N.k) : 0 < N.b := by
  rcases Nat.eq_zero_or_pos N.b with h | h
  · rw [h] at hj; simp at hj
  · exact h

theorem div_b_lt {j : ℕ} (hj : j < N.b * 2 ^ N.k) : j / N.b < 2 ^ N.k :=
  (Nat.div_lt_iff_lt_mul (b_pos N hj)).2 (by linarith)

theorem testBit_vl (u : Fin (2 ^ N.k) → Fin (2 ^ N.b)) (j : ℕ) (hj : j < N.b * 2 ^ N.k) :
    (vl N u).testBit j = ((u ⟨j / N.b, div_b_lt N hj⟩ : Fin (2 ^ N.b)) : ℕ).testBit (j % N.b) := by
  have hb : 0 < N.b := b_pos N hj
  have hm : j / N.b < 2 ^ N.k := (Nat.div_lt_iff_lt_mul hb).2 (by linarith)
  have h1 := dgt_vl N u ⟨j / N.b, hm⟩
  unfold dgt at h1
  rw [← h1, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hr : j % N.b < N.b := Nat.mod_lt _ hb
  simp only [hr, decide_true, Bool.true_and]
  congr 1
  have := Nat.div_add_mod j N.b
  omega

end
end ECDLP.L44
end
