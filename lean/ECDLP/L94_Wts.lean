import ECDLP.L94_Wt
import ECDLP.L94_Sum

/-!
# L94 / Wts: the weights `wtB = Bw + freeBits` satisfy the weight fields of `EdgeCore`

For the real network family (`Slot r`, `UC sg e`, `NParE L`, `wP L`, `phi = Subtype.val`), `L + 4 <= 4 n`:
* `wtB_le_Wm`: every node weight is at most `Wm r n` (`hmax`);
* `sum_wtB_le_Ub`: the total weight is at most `Ub r n = Uc X^4` (`htot`), via the exact count `T = sum_c |slots c| <= 107 r + 83` (L94_Sum);
* `hrow_wtB`, `hheld_wtB`: row sums <= wtB and the setting count <= 2^wtB (`hrow`, `hheld`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L94
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L59 ECDLP.L63 ECDLP.L64 ECDLP.L65
  ECDLP.L68 ECDLP.L73 ECDLP.L44 Slot Cst

section generic
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- row sums are below the weight -/
theorem hrow_wtB {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    ∑ b, (((edgeNet (w := w) φ F ok).toGNet).toNet e).cc a b ≤ wtB φ N0 w (e.symm a) :=
  (ECDLP.L57.rowsum_le φ F ok e a).trans (Nat.le_add_right _ _)

/-- the setting count is below `2^wtB` -/
theorem hheld_wtB (m : ℕ) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) :
    sN (edgeNetM (w := w) φ F ok m) e a ≤ 2 ^ wtB φ N0 w (e.symm a) := by
  refine (ECDLP.L75.sN_le_wtH φ F ok m e a).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold ECDLP.L75.wtH wtB
  have := ECDLP.L57.rowsum_le (w := w) φ F ok e a
  omega

theorem sum_wtB {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ∑ a : Fin g, wtB φ N0 w (e.symm a) =
      Wsum N0 w (fun c => Fintype.card (ιc c)) + Fintype.card ι * (N0.A * (N0.b * N0.h)) := by
  unfold wtB
  rw [Finset.sum_add_distrib, ECDLP.L75.sum_freeBits (ιc := ιc) (N0 := N0) e]
  congr 1
  rw [Fintype.sum_equiv e.symm (fun a => Bw (w := w) φ (e.symm a)) (fun x => Bw (w := w) φ x) (fun _ => rfl)]
  exact sum_Bw φ

end generic

section real
variable {r K : ℕ} (L n : ℕ) (sg : Fin (r + 1) → Sg) (e : Cn r ≃ Fin K)

theorem real_params : (∀ c : Fin K, (fun _ : Fin K => wP L) c ≤ 80) ∧ (NParE L).b ≤ 36 * 2 ^ (NParE L).k ∧
    2 ^ (NParE L).k * 2 ^ (NParE L).k ≤ L + 4 := by
  refine ⟨?_, bP_le L, ?_⟩
  · intro c
    have := M_le L
    have hD := DP_pos L
    simp only
    by_contra hcon
    push Not at hcon
    have : DP L * 81 ≤ DP L * wP L := Nat.mul_le_mul_left _ hcon
    omega
  · have := DD_le L; simpa [NParE_k, DP] using this

theorem wtB_le_Wm (hn : L + 4 ≤ 4 * n) (x : CG (Slot r) (UC sg e) (NParE L).A) :
    wtB (fun c => Subtype.val) (NParE L) (fun _ : Fin K => wP L) x ≤ Wm r n := by
  obtain ⟨hw, hbb, hDL⟩ := real_params (K := K) L
  have hKc : K ≤ 18 * (r + 1) := by rw [card_K e]; omega
  have hnn : ∀ c, Fintype.card (UC sg e c) ≤ 9 := fun c => ECDLP.L63.card_UC_le9 _ e c
  have hocc : ∀ i, occ (ιc := UC sg e) (fun c => Subtype.val) i ≤ 18 * (r + 1) :=
    fun i => (occ_le_K (fun c => Subtype.val) (fun c => Subtype.val_injective) i).trans hKc
  have hAD := AD_le_X L n hn
  have hS := eS_le (NParE L) 36 hbb
  have hAh := (NParE L).hAh
  have hhA := h_le_A (NParE L)
  have hbh : (NParE L).b * (NParE L).h ≤ 36 * ((NParE L).A * 2 ^ (NParE L).k) := by
    calc (NParE L).b * (NParE L).h ≤ (36 * 2 ^ (NParE L).k) * (NParE L).A := Nat.mul_le_mul hbb hhA
      _ = _ := by ring
  have hmax := Bw_le (w := fun _ : Fin K => wP L) (N0 := NParE L) (fun c => Subtype.val)
    (18 * (r + 1)) 9 36 80 hnn hocc hw hbb x
  have hD : 2 ^ (NParE L).k = DP L := rfl
  have hfin : ∀ y : ℕ, y ≤ 1711 * (r + 1) * ((NParE L).A * 2 ^ (NParE L).k) → y ≤ Wm r n := by
    intro y hy
    refine hy.trans ?_
    unfold Wm Wcn
    rw [hD]
    calc 1711 * (r + 1) * (AP L * DP L) ≤ 1711 * (r + 1) * (12 * Xs n ^ 3) := Nat.mul_le_mul_left _ hAD
      _ = _ := by ring
  cases x with
  | src i s =>
    have h1 := hocc i
    apply hfin
    simp only [wtB, Bw, freeBits]
    calc occ (ιc := UC sg e) (fun c => Subtype.val) i * eS (NParE L) + (NParE L).b * (NParE L).h
        ≤ (18 * (r + 1)) * ((36 + 1) * 2 ^ (NParE L).k * (NParE L).A) + 36 * ((NParE L).A * 2 ^ (NParE L).k) :=
          Nat.add_le_add (Nat.mul_le_mul h1 hS) hbh
      _ ≤ 1711 * (r + 1) * ((NParE L).A * 2 ^ (NParE L).k) := by
          have : 1 ≤ (NParE L).A * 2 ^ (NParE L).k := Nat.one_le_iff_ne_zero.2
            (by have := (NParE L).toPar.A_pos; positivity)
          nlinarith [Nat.zero_le r]
  | gt c g =>
    apply hfin
    have := hmax
    simp only [wtB, freeBits, Nat.add_zero]
    refine this.trans ?_
    have : 1 ≤ (NParE L).A * 2 ^ (NParE L).k := Nat.one_le_iff_ne_zero.2
      (by have := (NParE L).toPar.A_pos; positivity)
    nlinarith [Nat.zero_le r]

theorem sum_wtB_le_Ub (hn : L + 4 ≤ 4 * n) {g : ℕ} (eg : CG (Slot r) (UC sg e) (NParE L).A ≃ Fin g) :
    ∑ a : Fin g, wtB (fun c => Subtype.val) (NParE L) (fun _ : Fin K => wP L) (eg.symm a) ≤ Ub r n := by
  obtain ⟨hw, hbb, hDL⟩ := real_params (K := K) L
  have hKe := card_K e
  have hnn : ∀ c, Fintype.card (UC sg e c) ≤ 9 := fun c => ECDLP.L63.card_UC_le9 _ e c
  rw [sum_wtB (fun c => Subtype.val) eg]
  set T := ∑ c : Fin K, Fintype.card (UC sg e c) with hT
  have hWs : Wsum (NParE L) (fun _ : Fin K => wP L) (fun c => Fintype.card (UC sg e c)) ≤
      2 ^ (NParE L).k * 2 ^ (NParE L).k * (484 * T + 1008 * K) := by
    unfold Wsum
    have hc : ∀ c : Fin K, 2 * Fintype.card (UC sg e c) * (NParE L).A * eS (NParE L) +
        2 * Fintype.card (UC sg e c) * (NParE L).A * (NParE L).A * eM (NParE L) (fun _ : Fin K => wP L) c +
        6 * (NParE L).A * (NParE L).A * eM (NParE L) (fun _ : Fin K => wP L) c ≤
        2 ^ (NParE L).k * 2 ^ (NParE L).k * (4 * Fintype.card (UC sg e c) * (36 + 80 + 5) + 12 * (80 + 4)) :=
      fun c => term_bound (NParE L).A (2 ^ (NParE L).k) _ (Fintype.card (UC sg e c)) _ _ 36 80 (hA_dd (NParE L)) le_rfl
        (eS_le (NParE L) 36 hbb) (eM_le (NParE L) (fun _ : Fin K => wP L) 80 hw c)
    refine (sum_le_sum fun c _ => hc c).trans (le_of_eq ?_)
    calc ∑ c : Fin K, 2 ^ (NParE L).k * 2 ^ (NParE L).k * (4 * Fintype.card (UC sg e c) * (36 + 80 + 5) + 12 * (80 + 4))
        = ∑ c : Fin K, (2 ^ (NParE L).k * 2 ^ (NParE L).k * (484 * Fintype.card (UC sg e c)) +
            2 ^ (NParE L).k * 2 ^ (NParE L).k * 1008) := sum_congr rfl fun c _ => by ring
      _ = _ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  have hT107 : T ≤ 107 * r + 83 := sumNc_le sg e
  have hfree : Fintype.card (Slot r) * ((NParE L).A * ((NParE L).b * (NParE L).h)) ≤ (24 * r + 23) * (36 * (L + 4)) := by
    rw [card_Slot]
    refine Nat.mul_le_mul_left _ ?_
    have h1 : (NParE L).A * (NParE L).h = 2 ^ (NParE L).k := (NParE L).hAh
    calc (NParE L).A * ((NParE L).b * (NParE L).h) = (NParE L).b * ((NParE L).A * (NParE L).h) := by ring
      _ = (NParE L).b * 2 ^ (NParE L).k := by rw [h1]
      _ ≤ (36 * 2 ^ (NParE L).k) * 2 ^ (NParE L).k := Nat.mul_le_mul_right _ hbb
      _ ≤ 36 * (L + 4) := by nlinarith
  have hU := Ub_ge r n L hn
  refine le_trans (Nat.add_le_add hWs hfree) ?_
  refine le_trans ?_ hU
  have h1 : 2 ^ (NParE L).k * 2 ^ (NParE L).k * (484 * T + 1008 * K) ≤ (L + 4) * (484 * (107 * r + 83) + 1008 * (18 * r + 12)) := by
    refine le_trans (Nat.mul_le_mul hDL ?_) le_rfl
    rw [hKe]; nlinarith
  nlinarith [Nat.zero_le (r * L), Nat.zero_le r, Nat.zero_le L]

end real
end ECDLP.L94
end
