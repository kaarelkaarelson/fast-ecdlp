import ECDLP.L65_Bridge

/-!
# L65 / Bridge2: gate count `≤ nodesE r n`, setting length `≤ Sb n`
-/
noncomputable section
namespace ECDLP.L65
open Finset ECDLP.L30 ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L59 ECDLP.L51
  Factoring.Aux

variable {r K : ℕ}

/-- **Node count**: the edge network (any prefix, any numbering) has at most `828 (r+1) X^2` gates. -/
theorem edge_bridge_gates (p n : ℕ) (hn : Nat.size p + 4 ≤ 4 * n) (sg : Fin (r + 1) → Sg) (e : Cn r ≃ Fin K) :
    Fintype.card (CG (Slot r) (UC sg e) (NParE (Nat.size p)).A) ≤ nodesE r n := by
  have h := ECDLP.L63.gates_concrete (n := r) (Nat.size p) sg e
  have hA := A_le_X (Nat.size p) n hn
  have hX := Xs_pos n
  simp only [NParE_A] at h ⊢
  refine h.trans ?_
  unfold nodesE
  have h1 : AP (Nat.size p) * (24 * (r + 1) + 18 * (r + 1) * (11 + AP (Nat.size p))) =
      222 * (r + 1) * AP (Nat.size p) + 18 * (r + 1) * (AP (Nat.size p) * AP (Nat.size p)) := by ring
  rw [h1]
  have h2 : AP (Nat.size p) * AP (Nat.size p) ≤ (3 * Xs n) * (3 * Xs n) := Nat.mul_le_mul hA hA
  have h3 : Xs n ≤ Xs n ^ 2 := by nlinarith
  have h4 : 222 * (r + 1) * AP (Nat.size p) ≤ 222 * (r + 1) * (3 * Xs n) := Nat.mul_le_mul_left _ hA
  have h5 : 18 * (r + 1) * (AP (Nat.size p) * AP (Nat.size p)) ≤ 18 * (r + 1) * ((3 * Xs n) * (3 * Xs n)) :=
    Nat.mul_le_mul_left _ h2
  have h6 : (r + 1) * Xs n ≤ (r + 1) * Xs n ^ 2 := Nat.mul_le_mul_left _ h3
  nlinarith [Nat.zero_le ((r + 1) * Xs n ^ 2)]

/-- **Setting length**: every gate of the edge network has setting at most `19680 X^3 = Sb n` bits. -/
theorem edge_bridge_setting (p n : ℕ) (hn : Nat.size p + 4 ≤ 4 * n) (sg : Fin (r + 1) → Sg) (e : Cn r ≃ Fin K)
    (φ : ∀ c, UC sg e c → Slot r) (F : ∀ c, Form (UC sg e c))
    (ok : Slot r → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)
    (g : CG (Slot r) (UC sg e) (NParE (Nat.size p)).A) :
    settingBits (w := fun _ : Fin K => wP (Nat.size p)) φ F ok g ≤ Sb n := by
  have h := ECDLP.L63.setting_concrete (Nat.size p) sg e φ F ok g
  have hAD := AD_le_X (Nat.size p) n hn
  refine h.trans ?_
  unfold Sb Scn
  omega

end ECDLP.L65
end
