import ECDLP.L34_Net

/-!
# L34 / Count: the network's good settings are the solutions of the identity
-/
namespace ECDLP.L34

open Finset Factoring.Aux

variable {ι : Type}

theorem chainZ_car (b : ℕ) (c : ℕ → ℤ) (car : ℕ → ℤ) (hcar : ∀ j, car (j + 1) = (car j + c j) / 2 ^ b) :
    ∀ len s, chainZ b c len s (car s) ↔
      (∀ j, s ≤ j → j < s + len → (2 ^ b : ℤ) ∣ car j + c j) ∧ car (s + len) = 0
  | 0, s => by
      simp only [chainZ, add_zero]
      exact ⟨fun h => ⟨fun j h1 h2 => absurd h2 (by omega), h⟩, fun h => h.2⟩
  | len + 1, s => by
      rw [chainZ, ← hcar, chainZ_car b c car hcar len (s + 1)]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨fun j hj1 hj2 => ?_, by rwa [show s + (len + 1) = s + 1 + len by ring]⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; exact h0
        · exact h1 j h (by omega)
      · rintro ⟨h1, h2⟩
        exact ⟨h1 s le_rfl (by omega), fun j hj1 hj2 => h1 j (by omega) (by omega),
          by rwa [show s + 1 + len = s + (len + 1) by ring]⟩

namespace NPar
variable {N : NPar} (F : Form ι)

theorem coefS_eq (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (j : ℕ) :
    coefS F d j = N.coef F (N.dgOf d) j := by
  unfold coefS Par.coef
  refine N.ibOut_congr (fun r hr => ?_) _
  rw [exA, dif_pos hr]
  unfold ibS
  refine N.midMsg_congr F _ (fun i s hs => ?_) _
  rw [exA, dif_pos hs]
  exact N.faMsgS_eq d i ⟨s, hs⟩ r

theorem T_pos (N : NPar) : 0 < N.A * N.A := Nat.mul_pos N.toPar.A_pos N.toPar.A_pos

/-- the good settings are forced -/
theorem Asg.ext' {a b : Asg ι N} (h1 : a.fa = b.fa) (h2 : a.mid = b.mid) (h3 : a.ib = b.ib)
    (h4 : a.car = b.car) : a = b := by
  cases a; cases b; simp_all

theorem good_pinned {F : Form ι} {a : Asg ι N} (h : Good F a) : a = run F a.fa := by
  have hmid : a.mid = (run F a.fa).mid := by
    funext k₁ i s; exact h.g1 i s k₁
  have hib : a.ib = (run F a.fa).ib := by
    funext j₁ k₁
    rw [h.g2]
    have : (fun i => exA (a.mid k₁ i)) = fun i => exA (fun s : Fin N.A => N.faMsgS (a.fa i s) s k₁) := by
      funext i; rw [hmid]; rfl
    rw [this]; rfl
  have hc1 : ∀ j : Fin (N.A * N.A), (a.car j).1 = coefS F a.fa j := by
    intro j
    rw [h.g3 j, hib]; rfl
  have hcin : ∀ j, j < N.A * N.A → a.cin j = carS N.b (fun j' => (coefS F a.fa j').valMinAbs) j := by
    intro j
    induction j with
    | zero => intro _; exact h.g4a
    | succ j ih =>
        intro hj
        rw [h.g4b j hj, ih (by omega)]
        have : a.cf j = coefS F a.fa j := by
          unfold Asg.cf; rw [dif_pos (by omega)]; exact hc1 ⟨j, by omega⟩
        rw [this]; rfl
  refine Asg.ext' rfl hmid hib ?_
  funext j
  refine Prod.ext (hc1 j) ?_
  have := hcin j j.2
  unfold Asg.cin at this
  rw [dif_pos j.2] at this
  exact this

theorem good_run_iff (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) :
    Good F (run F d) ↔ N.accept F (N.dgOf d) := by
  set c' : ℕ → ℤ := fun j => (coefS F d j).valMinAbs with hc'
  have hcin : ∀ j, j < N.A * N.A → (run F d).cin j = carS N.b c' j := by
    intro j hj; unfold Asg.cin; rw [dif_pos hj]; rfl
  have hcf : ∀ j, j < N.A * N.A → (run F d).cf j = coefS F d j := by
    intro j hj; unfold Asg.cf; rw [dif_pos hj]; rfl
  have hT := N.T_pos
  have hcar : ∀ j, carS N.b c' (j + 1) = (carS N.b c' j + c' j) / 2 ^ N.b := fun j => rfl
  have hacc : N.accept F (N.dgOf d) ↔ chainZ N.b c' (N.A * N.A) 0 (carS N.b c' 0) := by
    unfold Par.accept
    have e1 := chainZ_iff N.b (fun j => (N.coef F (N.dgOf d) j).valMinAbs) (N.A * N.A) 0 0
    have e2 := chainZ_iff N.b c' (N.A * N.A) 0 (carS N.b c' 0)
    have : ∑ j ∈ range (N.A * N.A), (N.coef F (N.dgOf d) (0 + j)).valMinAbs * 2 ^ (N.b * j) =
        ∑ j ∈ range (N.A * N.A), c' (0 + j) * 2 ^ (N.b * j) := by
      refine sum_congr rfl fun j hj => ?_
      rw [zero_add]; show _ = (coefS F d j).valMinAbs * _; rw [coefS_eq]
    change chainZ N.b (fun j => (N.coef F (N.dgOf d) j).valMinAbs) (N.A * N.A) 0 0 ↔ _
    rw [e1, e2, this]; rfl
  rw [hacc, chainZ_car N.b c' (carS N.b c') hcar]
  constructor
  · intro h
    refine ⟨fun j _ hj => ?_, ?_⟩
    · have := h.g4c j (by omega)
      rwa [hcin j (by omega), hcf j (by omega)] at this
    · have := h.g4d
      have h1 : N.A * N.A - 1 + 1 = N.A * N.A := by omega
      rw [hcin _ (by omega), hcf _ (by omega)] at this
      rw [zero_add, ← h1]
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i s k₁ => rfl, fun j₁ k₁ => rfl, fun j => rfl, ?_, ?_, ?_, ?_⟩
    · rw [hcin 0 hT]; rfl
    · intro j hj
      rw [hcin _ hj, hcin _ (by omega), hcf _ (by omega)]; rfl
    · intro j hj
      rw [hcin j hj, hcf j hj]; exact h1 j (Nat.zero_le _) (by omega)
    · have h1' : N.A * N.A - 1 + 1 = N.A * N.A := by omega
      rw [hcin _ (by omega), hcf _ (by omega)]
      rw [zero_add] at h2
      rw [← h1'] at h2
      exact h2

end NPar
end ECDLP.L34
