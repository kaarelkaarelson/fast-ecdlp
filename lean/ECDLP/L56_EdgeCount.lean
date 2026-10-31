import ECDLP.L56_Edge

/-!
# L56 / EdgeCount: `Net.value` of the child-specific-message network = L54's count
-/
noncomputable section
namespace ECDLP.L56
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

open Classical in
theorem checks_E (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) :
    (∀ g, (edgeNet (w := w) φ F ok).W g ((edgeNet (w := w) φ F ok).run x g) = 1) ↔
      (∀ i s, ok i s (dC x i s)) ∧ ∀ c, (NP N0 w c).Holds (F c) ((NP N0 w c).dgOf (dcOf (w := w) φ c (dC x))) := by
  have hu := tvc_eq_uE φ F ok hS hb x
  have hrun : ∀ g, (edgeNet (w := w) φ F ok).run x g = (x g, fun j : {j // j ∈ paC (w := w) φ g} => uE (w := w) φ F x j.1 g) := by
    intro g
    show (x g, fun j : {j // j ∈ paC (w := w) φ g} => (edgeNet (w := w) φ F ok).tvc x j.1 g) = _
    rw [hu]
    rfl
  simp only [hrun]
  have hcar : ∀ c j, (edgeNet (w := w) φ F ok).W (.gt c (Gate.car j)) (x (.gt c (Gate.car j)), fun q => uE (w := w) φ F x q.1 (.gt c (Gate.car j))) =
      WG (NP N0 w c) (fun _ _ _ => True) (Gate.car j)
        (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)) (Gate.car j),
          fun q => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) q.1) := fun c j => rfl
  have hsrc : ∀ i s, (edgeNet (w := w) φ F ok).W (.src i s) (x (.src i s), fun q => uE (w := w) φ F x q.1 (.src i s)) =
      if ok i s (x (.src i s)) then 1 else 0 := fun i s => rfl
  have hgad := fun c => gadget_chk (N0 := N0) (w := w) (ιc := ιc) (K := K) (ι := ι) φ F hS hb x c
  have hnon : ∀ c (g : Gate (ιc c) N0.A), (∀ j, g ≠ Gate.car j) →
      WG (NP N0 w c) (fun _ _ _ => True) g
        (xOf (N := NP N0 w c) (dcOf (w := w) φ c (dC x)) g,
          fun q => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) q.1) = 1 := by
    intro c g hg
    cases g with
    | fa i s => simp [WG]
    | mid k => simp [WG]
    | ib k => simp [WG]
    | car j => exact absurd rfl (hg j)
  constructor
  · intro h
    refine ⟨fun i s => ?_, fun c => (hgad c).1 (fun g => ?_)⟩
    · have := (hsrc i s).symm.trans (h (.src i s))
      by_contra hn
      exact zero_ne_one ((if_neg (show ¬ ok i s (dC x i s) from hn)).symm.trans this)
    · by_cases hc : ∃ j, g = Gate.car j
      · obtain ⟨j, rfl⟩ := hc
        exact (hcar c j).symm.trans (h (.gt c (Gate.car j)))
      · exact hnon c g (fun j hj => hc ⟨j, hj⟩)
  · rintro ⟨h1, h2⟩ g
    cases g with
    | src i s => exact (hsrc i s).trans (if_pos (h1 i s))
    | gt c g =>
      cases g with
      | fa j s => rfl
      | mid k => rfl
      | ib j₁ => rfl
      | car j => exact (hcar c j).trans ((hgad c).2 (h2 c) (Gate.car j))

open Classical in
/-- **Child-specific composition theorem.**  Same value as `ECDLP.L54.comp_value`, with every message a single
ring element / carry / slice. -/
theorem edge_value (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    ((((edgeNet (w := w) φ F ok).toGNet).toNet e).value) =
      ((univ.filter fun d : ι → Fin N0.A → Dg N0 =>
        (∀ i s, ok i s (d i s)) ∧
          ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card : ℤ) := by
  rw [(edgeNet (w := w) φ F ok).pforced_value e (fun g z => WE_01 φ F ok g z)]
  congr 1
  rw [← card_freeC (K := K) (ιc := ιc) (fun d => (∀ i s, ok i s (d i s)) ∧
    ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j))))]
  have hh : ∀ x : (∀ g : CG ι ιc N0.A, CF ι ιc N0 g),
      (∀ g, (edgeNet (w := w) φ F ok).W g ((edgeNet (w := w) φ F ok).run x g) = 1) ↔
      ((∀ i s, ok i s (dC x i s)) ∧ ∀ c, N0.Holds (F c) (N0.dgOf (fun j => dC x (φ c j)))) := by
    intro x
    refine (checks_E φ F ok hS hb x).trans ?_
    have h : (∀ c, (NP N0 w c).Holds (F c) ((NP N0 w c).dgOf (dcOf (w := w) φ c (dC x)))) ↔
        ∀ c, N0.Holds (F c) (N0.dgOf fun j => dC x (φ c j)) :=
      forall_congr' fun c => holds_NP (w := w) c (F c) (fun j s => dC x (φ c j) s)
    exact and_congr Iff.rfl h
  exact card_congr_pred _ _ _ _ hh

end
end ECDLP.L56
end
