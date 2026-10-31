import ECDLP.L64_Edge
import ECDLP.L57_Concrete
import ECDLP.L59_Explicit

/-!
# L75 / Shape: the shape parameters `U0`, `P0` of `TopShape` are met by the explicit parameters of L59

`EdgeGateData` (L64) asks, for the uncoarsened gate network `N = (toGNetE (edgeNetM m) E).toNet e`,
* `hmax`: every row sum `∑ b, N.cc a b ≤ wmax`,
* `htot`: `∑ a, ∑ b, N.cc a b ≤ T.U0 (T.sF n)`,
* `hfit`: `(∑ a, ∑ b, N.cc a b) / g' + wmax ≤ T.P0 (T.sF n) g'` for every `g' > 0`.
We prove these with `wmax := Wm` and `U0 := Utot`, `P0 s g' := Utot / g' + Wm` where, for the explicit parameters
`NParE L`, `w = wP L` of L59 (so `b ≤ 36 D`, `w ≤ 80`, `D*D ≤ L`),
`Utot = κ (484 nmax + 1008) m L`, `Wm = ((occmax+1)*37 + (nmax+3)*84) * (A*D)`.
-/
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L59 ECDLP.L64

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- the shared bits of the explicitly coded network are those of `edgeNet` -/
theorem cc_edgeM (m : ℕ) (E : ∀ i, (edgeNetM (w := w) φ F ok m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Msg i)))
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a b : Fin g) :
    ((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b = (((edgeNet (w := w) φ F ok).toGNet).toNet e).cc a b := rfl

theorem edge_rowsum_Bw (m : ℕ) (E : ∀ i, (edgeNetM (w := w) φ F ok m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Msg i)))
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    ∑ b, ((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b ≤ Bw (w := w) φ (e.symm a) := by
  simp_rw [cc_edgeM]
  exact rowsum_le φ F ok e a

theorem edge_total_Wsum (m : ℕ) (E : ∀ i, (edgeNetM (w := w) φ F ok m).Msg i ≃ Fin (Fintype.card ((edgeNetM (w := w) φ F ok m).Msg i)))
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∑ a, ∑ b, ((toGNetE (edgeNetM (w := w) φ F ok m) E).toNet e).cc a b ≤ Wsum N0 w (fun c => Fintype.card (ιc c)) := by
  calc _ ≤ ∑ a : Fin g, Bw (w := w) φ (e.symm a) := sum_le_sum fun a _ => edge_rowsum_Bw φ F ok m E e a
    _ = ∑ x : CG ι ιc N0.A, Bw (w := w) φ x :=
        Fintype.sum_equiv e.symm (fun a => Bw (w := w) φ (e.symm a)) (fun x => Bw (w := w) φ x) (fun _ => rfl)
    _ = _ := sum_Bw φ

end

/-- total shared-bit bound for the explicit parameters -/
def Utot (κ nmax m L : ℕ) : ℕ := κ * (484 * nmax + 1008) * m * L
/-- per-gate shared-bit bound for the explicit parameters -/
def Wm (occmax nmax L : ℕ) : ℕ := ((occmax + 1) * 37 + (nmax + 3) * 84) * (AP L * DP L)

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c))

/-- **The three inequalities of `EdgeGateData` for the explicit parameters of L59**, in terms of the gate network. -/
theorem explicit_ineqs (L nmax occmax κ m : ℕ) (hL : 4 ≤ L)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax) (hK : K ≤ κ * m)
    (ok : ι → Fin (NParE L).A → Dg (NParE L) → Prop) (M : ℕ)
    (E : ∀ i, (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M).Msg i ≃
      Fin (Fintype.card ((edgeNetM (w := fun _ : Fin K => wP L) φ F ok M).Msg i)))
    {g : ℕ} (e : CG ι ιc (NParE L).A ≃ Fin g) :
    (∀ a : Fin g, ∑ b, ((toGNetE (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) E).toNet e).cc a b ≤ Wm occmax nmax L) ∧
    (∑ a : Fin g, ∑ b, ((toGNetE (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) E).toNet e).cc a b ≤ Utot κ nmax m L) := by
  have hw : ∀ c : Fin K, (fun _ : Fin K => wP L) c ≤ 80 := by
    intro c
    have h := M_le L
    have hD := DP_pos L
    exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using h) hD
  have hb : (NParE L).b ≤ 36 * 2 ^ (NParE L).k := bP_le L
  have hDL : 2 ^ (NParE L).k * 2 ^ (NParE L).k ≤ 1 * L := by
    have := D_sq_le L hL; simpa [DP] using this
  refine ⟨fun a => ?_, ?_⟩
  · refine (edge_rowsum_Bw φ F ok M E e a).trans ?_
    have := Bw_le (w := fun _ : Fin K => wP L) φ occmax nmax 36 80 hn hocc hw hb (e.symm a)
    simpa [Wm, DP, mul_comm] using this
  · refine (edge_total_Wsum φ F ok M E e).trans ?_
    have := Wsum_le (N0 := NParE L) (w := fun _ : Fin K => wP L) (ιc := ιc) nmax 36 80 κ 1 m L hn hw hb hDL hK
    refine this.trans (le_of_eq ?_)
    unfold Utot; ring

end

/-- **The `U0`/`P0` obligations.**  Let `T` be any shape with `T.U0 s ≥ Utot` and `T.P0 s g' ≥ Utot/g' + Wm`
(for instance `U0 := Utot`, `P0 s g' := Utot / g' + Wm`).  Then `hmax`, `hfit`, `htot` of `EdgeGateData` hold. -/
theorem shape_ineqs {ι : Type} {K : ℕ} {ιc : Fin K → Type}
    [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
    (F : ∀ c, Form (ιc c))
    (T : TopShape) (n L nmax occmax κ m : ℕ) (hL : 4 ≤ L)
    (hn : ∀ c, Fintype.card (ιc c) ≤ nmax) (hocc : ∀ i, occ (ιc := ιc) φ i ≤ occmax) (hK : K ≤ κ * m)
    (hU : Utot κ nmax m L ≤ T.U0 (T.sF n)) (hP : ∀ g' : ℕ, 0 < g' → Utot κ nmax m L / g' + Wm occmax nmax L ≤ T.P0 (T.sF n) g')
    (ok : ι → Fin (NParE L).A → Dg (NParE L) → Prop) (M : ℕ)
    (E : ∀ i, (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M).Msg i ≃
      Fin (Fintype.card ((edgeNetM (w := fun _ : Fin K => wP L) φ F ok M).Msg i)))
    {g : ℕ} (e : CG ι ιc (NParE L).A ≃ Fin g) :
    (∀ a : Fin g, ∑ b, ((toGNetE (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) E).toNet e).cc a b ≤ Wm occmax nmax L) ∧
    (∀ (g' : ℕ) (_ : 0 < g'), (∑ a : Fin g, ∑ b, ((toGNetE (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) E).toNet e).cc a b) / g' +
        Wm occmax nmax L ≤ T.P0 (T.sF n) g') ∧
    (∑ a : Fin g, ∑ b, ((toGNetE (edgeNetM (w := fun _ : Fin K => wP L) φ F ok M) E).toNet e).cc a b ≤ T.U0 (T.sF n)) := by
  obtain ⟨h1, h2⟩ := explicit_ineqs φ F L nmax occmax κ m hL hn hocc hK ok M E e
  refine ⟨h1, fun g' hg' => ?_, h2.trans hU⟩
  exact (Nat.add_le_add_right (Nat.div_le_div_right h2) _).trans (hP g' hg')

/-- The top-level product `G * P0` with `G^4 ≤ L` (the condition `G·P ≤ O(L)` of the engine). -/
theorem G_P0_le (L nmax occmax κ m G : ℕ) (hL : 4 ≤ L) (hG4 : G ^ 4 ≤ L) :
    G * (Utot κ nmax m L / G + Wm occmax nmax L) ≤
      Utot κ nmax m L + ((occmax + 1) * 37 + (nmax + 3) * 84) * (2 * L) := by
  have hq := quartic_bound (AP L) (DP L) 1 2 G L (AA_eq L) (by simpa using D_sq_le L hL) (by norm_num) hG4
  calc G * (Utot κ nmax m L / G + Wm occmax nmax L)
      = G * (Utot κ nmax m L / G) + G * Wm occmax nmax L := Nat.mul_add _ _ _
    _ ≤ Utot κ nmax m L + ((occmax + 1) * 37 + (nmax + 3) * 84) * (G * (AP L * DP L)) := by
        refine Nat.add_le_add (Nat.mul_div_le _ _) ?_
        unfold Wm; rw [mul_left_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _

end ECDLP.L75
end
