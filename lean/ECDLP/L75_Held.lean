import ECDLP.L75_Shape
import ECDLP.L59_Size
import ECDLP.L68_CarQ
import ECDLP.L64_Edge

/-!
# L75 / Held: shared + held bits

Shared-bits-only weights (`rowsum`) do not bound the number of settings of a cluster of gates.  Weight
`wtH a := rowsum a + freeBits a` (rowsum = shared bits, `freeBits` = bits of the free variable: `b h` for a source,
`0` for the other gates) covers the held bits: `sN a = |settings of a| ≤ 2^(wtH a)` (`sN_le_wtH`), because
`log |setting| ≤ freeBits + inW` (L59 `settingBits_le_inW`) and `inW ≤ rowsum`.
We bound `max wtH` and `Σ wtH` for the explicit parameters of L59 (`held_ineqs`) and in the scale `X` of L65
(`held_ineqs_X`, with `L ≤ 16 X^4`, `A D ≤ 12 X^3` as inputs).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L59 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- shared + held bits of the gate `a` -/
def wtH {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) : ℕ :=
  ∑ b, (((edgeNet (w := w) φ F ok).toGNet).toNet e).cc a b + freeBits N0 (e.symm a)

theorem card_S_eq_sN (m : ℕ) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).S (e.symm a)) = sN (edgeNetM (w := w) φ F ok m) e a := by
  haveI := edge_free_nonempty (w := w) φ F ok m
  exact (Fintype.card_congr ((pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m)
    (edgeEFM φ F ok m) e).e a)).trans (Fintype.card_fin _)

theorem sN_le_wtH (m : ℕ) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    sN (edgeNetM (w := w) φ F ok m) e a ≤ 2 ^ wtH (w := w) φ F ok e a := by
  rw [← card_S_eq_sN (w := w) φ F ok m e a]
  have h1 : Fintype.card ((edgeNetM (w := w) φ F ok m).S (e.symm a)) ≤ 2 ^ settingBits (w := w) φ F ok (e.symm a) :=
    Nat.le_pow_clog one_lt_two _
  have h2 := settingBits_le_inW (w := w) φ F ok (e.symm a)
  have h3 := PForcedW.rowsum_eq (edgeNet (w := w) φ F ok) e a
  refine h1.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold wtH
  omega

theorem rowsum_le_wtH {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    ∑ b, (((edgeNet (w := w) φ F ok).toGNet).toNet e).cc a b ≤ wtH (w := w) φ F ok e a := Nat.le_add_right _ _

theorem sum_freeBits {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∑ a : Fin g, freeBits N0 (e.symm a) = Fintype.card ι * (N0.A * (N0.b * N0.h)) := by
  rw [Fintype.sum_equiv e.symm (fun a => freeBits N0 (e.symm a)) (fun x => freeBits N0 x) (fun _ => rfl)]
  rw [sum_CG (ιc := ιc) (N0 := N0)]
  simp [freeBits, Finset.sum_const, Fintype.card_prod]
  ring

theorem sum_wtH {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∑ a : Fin g, wtH (w := w) φ F ok e a ≤
      Wsum N0 w (fun c => Fintype.card (ιc c)) + Fintype.card ι * (N0.A * (N0.b * N0.h)) := by
  unfold wtH
  rw [Finset.sum_add_distrib, sum_freeBits (ιc := ιc) (N0 := N0) e]
  refine Nat.add_le_add_right ?_ _
  have := edge_total_Wsum (w := w) φ F ok 0 (fun i => edgeEM (w := w) φ F ok 0 i) e
  simpa [cc_edgeM] using this

end

/-- per-gate bound on shared + held bits -/
def WH (occmax nmax L : ℕ) : ℕ := Wm occmax nmax L + 36 * (AP L * DP L)
/-- total bound on shared + held bits -/
def UH (κ nmax m L ιmax : ℕ) : ℕ := Utot κ nmax m L + ιmax * (36 * L)

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c))

/-- **Shared + held bits for the explicit parameters.** -/
theorem held_ineqs (L nmax occmax κ m ιmax : ℕ) (hL : 4 ≤ L)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax) (hK : K ≤ κ * m)
    (hι : Fintype.card ι ≤ ιmax)
    (ok : ι → Fin (NParE L).A → Dg (NParE L) → Prop) (M : ℕ) {g : ℕ} (e : CG ι ιc (NParE L).A ≃ Fin g) :
    (∀ a : Fin g, ∑ b, (((edgeNet (w := fun _ : Fin K => wP L) φ F ok).toGNet).toNet e).cc a b ≤
        wtH (w := fun _ : Fin K => wP L) φ F ok e a) ∧
    (∀ a : Fin g, sN (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) e a ≤
        2 ^ wtH (w := fun _ : Fin K => wP L) φ F ok e a) ∧
    (∀ a : Fin g, wtH (w := fun _ : Fin K => wP L) φ F ok e a ≤ WH occmax nmax L) ∧
    (∑ a : Fin g, wtH (w := fun _ : Fin K => wP L) φ F ok e a ≤ UH κ nmax m L ιmax) := by
  have hw : ∀ c : Fin K, (fun _ : Fin K => wP L) c ≤ 80 := by
    intro c
    have h := M_le L
    have hD := DP_pos L
    exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using h) hD
  have hb : (NParE L).b ≤ 36 * 2 ^ (NParE L).k := bP_le L
  have hDL : 2 ^ (NParE L).k * 2 ^ (NParE L).k ≤ 1 * L := by
    have := D_sq_le L hL; simpa [DP] using this
  have hbh : (NParE L).A * ((NParE L).b * (NParE L).h) ≤ 36 * L := by
    have h1 : (NParE L).A * (NParE L).h = 2 ^ (NParE L).k := (NParE L).hAh
    calc (NParE L).A * ((NParE L).b * (NParE L).h) = (NParE L).b * ((NParE L).A * (NParE L).h) := by ring
      _ = (NParE L).b * 2 ^ (NParE L).k := by rw [h1]
      _ ≤ (36 * 2 ^ (NParE L).k) * 2 ^ (NParE L).k := Nat.mul_le_mul_right _ hb
      _ ≤ 36 * L := by nlinarith
  refine ⟨fun a => rowsum_le_wtH φ F ok e a, fun a => sN_le_wtH φ F ok M e a, fun a => ?_, ?_⟩
  · have h1 : ∑ b, (((edgeNet (w := fun _ : Fin K => wP L) φ F ok).toGNet).toNet e).cc a b ≤ Wm occmax nmax L := by
      refine (rowsum_le φ F ok e a).trans ?_
      have := Bw_le (w := fun _ : Fin K => wP L) φ occmax nmax 36 80 hn hocc hw hb (e.symm a)
      simpa [Wm, DP, mul_comm] using this
    have h2 : freeBits (NParE L) (e.symm a) ≤ 36 * (AP L * DP L) := by
      cases (e.symm a) with
      | gt c g => simp [freeBits]
      | src i s =>
        simp only [freeBits]
        have hhA := h_le_A (NParE L)
        calc (NParE L).b * (NParE L).h ≤ (36 * 2 ^ (NParE L).k) * (NParE L).A := Nat.mul_le_mul hb hhA
          _ = 36 * (AP L * DP L) := by simp [DP]; ring
    unfold wtH WH
    omega
  · refine (sum_wtH φ F ok e).trans ?_
    have h1 := Wsum_le (N0 := NParE L) (w := fun _ : Fin K => wP L) (ιc := ιc) nmax 36 80 κ 1 m L hn hw hb hDL hK
    have h2 : Fintype.card ι * ((NParE L).A * ((NParE L).b * (NParE L).h)) ≤ ιmax * (36 * L) :=
      Nat.mul_le_mul hι hbh
    unfold UH Utot
    have : κ * 1 * (4 * nmax * (36 + 80 + 5) + 12 * (80 + 4)) * m * L = κ * (484 * nmax + 1008) * m * L := by ring
    rw [this] at h1
    omega

/-- The same in the scale `X` of L65: `L ≤ 16 X^4`, `A D ≤ 12 X^3`. -/
theorem held_ineqs_X (L nmax occmax κ m ιmax X : ℕ) (hL : 4 ≤ L)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax) (hK : K ≤ κ * m)
    (hι : Fintype.card ι ≤ ιmax) (hLX : L ≤ 16 * X ^ 4) (hADX : AP L * DP L ≤ 12 * X ^ 3)
    (ok : ι → Fin (NParE L).A → Dg (NParE L) → Prop) (M : ℕ) {g : ℕ} (e : CG ι ιc (NParE L).A ≃ Fin g) :
    (∀ a : Fin g, sN (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) e a ≤
        2 ^ wtH (w := fun _ : Fin K => wP L) φ F ok e a) ∧
    (∀ a : Fin g, wtH (w := fun _ : Fin K => wP L) φ F ok e a ≤
        (12 * ((occmax + 1) * 37 + (nmax + 3) * 84 + 36)) * X ^ 3) ∧
    (∑ a : Fin g, wtH (w := fun _ : Fin K => wP L) φ F ok e a ≤
        (16 * (κ * (484 * nmax + 1008) * m + 36 * ιmax)) * X ^ 4) := by
  obtain ⟨-, h2, h3, h4⟩ := held_ineqs φ F L nmax occmax κ m ιmax hL hn hocc hK hι ok M e
  refine ⟨h2, fun a => (h3 a).trans ?_, h4.trans ?_⟩
  · unfold WH Wm
    calc ((occmax + 1) * 37 + (nmax + 3) * 84) * (AP L * DP L) + 36 * (AP L * DP L)
        = ((occmax + 1) * 37 + (nmax + 3) * 84 + 36) * (AP L * DP L) := by ring
      _ ≤ ((occmax + 1) * 37 + (nmax + 3) * 84 + 36) * (12 * X ^ 3) := Nat.mul_le_mul_left _ hADX
      _ = _ := by ring
  · unfold UH Utot
    calc κ * (484 * nmax + 1008) * m * L + ιmax * (36 * L)
        = (κ * (484 * nmax + 1008) * m + 36 * ιmax) * L := by ring
      _ ≤ (κ * (484 * nmax + 1008) * m + 36 * ιmax) * (16 * X ^ 4) := Nat.mul_le_mul_left _ hLX
      _ = _ := by ring

end
end ECDLP.L75
end
