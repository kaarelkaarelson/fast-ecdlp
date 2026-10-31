import ECDLP.L57_Width
import ECDLP.L56_EFinal

/-!
# L57 / Edge: per-gate widths of `edgeNet`
-/
noncomputable section
namespace ECDLP.L57
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- bits of a slice message plus the shift -/
def eS (N0 : NPar) : ℕ := N0.b * N0.h + 1
/-- bits bound of a ring/carry message of identity `c` (plus the shift) -/
def eM (N0 : NPar) (w : Fin K → ℕ) (c : Fin K) : ℕ := (NP N0 w c).M + 4

/-- edge width bound of the messages sent by a gate -/
def ewid (N0 : NPar) (w : Fin K → ℕ) : CG ι ιc N0.A → ℕ
  | .src _ _ => eS N0
  | .gt c _ => eM N0 w c

theorem clog_le' {n k : ℕ} (h : n ≤ 2 ^ k) : Nat.clog 2 n ≤ k := Nat.clog_le_of_le_pow h

theorem clog_rg_le (c : Fin K) : Nat.clog 2 (Fintype.card (NP N0 w c).Rg) ≤ (NP N0 w c).M + 1 := by
  apply clog_le'
  have h := ZMod.card (2 ^ (NP N0 w c).M + 1)
  rw [show Fintype.card (NP N0 w c).Rg = 2 ^ (NP N0 w c).M + 1 from h]
  have : 1 ≤ 2 ^ (NP N0 w c).M := Nat.one_le_two_pow
  rw [pow_succ]; omega

theorem msg_w_le (g : CG ι ιc N0.A) : (edgeNet (w := w) φ F ok).w g + 1 ≤ ewid N0 w g := by
  cases g with
  | src i s =>
    show Nat.clog 2 (Fintype.card (Dg N0)) + 1 ≤ N0.b * N0.h + 1
    have : Nat.clog 2 (Fintype.card (Dg N0)) ≤ N0.b * N0.h := by
      apply clog_le'
      simp [Dg, ← pow_mul]
    omega
  | gt c g =>
    cases g with
    | fa j s =>
      show Nat.clog 2 (Fintype.card (NP N0 w c).Rg) + 1 ≤ (NP N0 w c).M + 4
      have := clog_rg_le (N0 := N0) (w := w) c; omega
    | mid k =>
      show Nat.clog 2 (Fintype.card (NP N0 w c).Rg) + 1 ≤ (NP N0 w c).M + 4
      have := clog_rg_le (N0 := N0) (w := w) c; omega
    | ib j =>
      show Nat.clog 2 (Fintype.card (NP N0 w c).Rg) + 1 ≤ (NP N0 w c).M + 4
      have := clog_rg_le (N0 := N0) (w := w) c; omega
    | car j =>
      show Nat.clog 2 (Fintype.card (Fin (2 ^ ((NP N0 w c).M + 3)))) + 1 ≤ (NP N0 w c).M + 4
      have : Nat.clog 2 (Fintype.card (Fin (2 ^ ((NP N0 w c).M + 3)))) ≤ (NP N0 w c).M + 3 := by
        apply clog_le'; simp
      omega

/-! ### parents -/

theorem mem_pa_gt {c : Fin K} {g : Gate (ιc c) N0.A} {x : CG ι ιc N0.A}
    (h : x ∈ paC (w := w) φ (CG.gt c g)) :
    (∃ q, q ∈ paG (NP N0 w c) g ∧ x = CG.gt c q) ∨ x ∈ extraPa φ c g := by
  rcases Finset.mem_union.1 h with h | h
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr h

theorem pa_card (g : CG ι ιc N0.A) : (paC (w := w) φ g).card ≤
    match g with
    | .src _ _ => 0
    | .gt c (Gate.fa _ _) => 1
    | .gt c (Gate.mid _) => Fintype.card (ιc c) * N0.A
    | .gt c (Gate.ib _) => N0.A
    | .gt c (Gate.car _) => 2 := by
  cases g with
  | src i s => exact le_of_eq (by rfl)
  | gt c g =>
    cases g with
    | fa j s =>
      show (image (CG.gt c) (∅ : Finset (Gate (ιc c) N0.A)) ∪ {CG.src (φ c j) s}).card ≤ 1
      rw [image_empty, empty_union]; simp
    | mid k =>
      show (image (CG.gt c) (image (fun p : ιc c × Fin N0.A => Gate.fa p.1 p.2) univ) ∪ ∅).card ≤ _
      rw [union_empty]
      refine card_image_le.trans (card_image_le.trans (le_of_eq ?_))
      simp
    | ib j =>
      show (image (CG.gt c) (image (fun k : Fin N0.A => Gate.mid k) univ) ∪ ∅).card ≤ _
      rw [union_empty]
      refine card_image_le.trans (card_image_le.trans (le_of_eq ?_))
      simp
    | car j =>
      show (image (CG.gt c) (insert (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)
        (if h : 0 < j.val then {Gate.car ⟨j.val - 1, by have := j.2; omega⟩} else ∅)) ∪ ∅).card ≤ 2
      rw [union_empty]
      refine card_image_le.trans ((card_insert_le _ _).trans ?_)
      split_ifs <;> simp

/-- all parents' edge widths are bounded -/
theorem pa_wid (g j : CG ι ιc N0.A) (hj : j ∈ paC (w := w) φ g) :
    ewid N0 w j ≤ match g with
      | .src _ _ => 0
      | .gt c (Gate.fa _ _) => eS N0
      | .gt c _ => eM N0 w c := by
  cases g with
  | src i s => exact absurd hj (by simp [paC])
  | gt c g =>
    rcases mem_pa_gt φ hj with ⟨q, hq, rfl⟩ | h
    · cases g with
      | fa j' s => exact absurd hq (by simp [paG])
      | mid k => exact le_rfl
      | ib j' => exact le_rfl
      | car j' => exact le_rfl
    · cases g with
      | fa j' s =>
        have : j = CG.src (φ c j') s := by simpa [extraPa] using h
        subst this; exact le_rfl
      | mid k => exact absurd h (by simp [extraPa])
      | ib j' => exact absurd h (by simp [extraPa])
      | car j' => exact absurd h (by simp [extraPa])

theorem not_mem_paG_fa {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : NPar) (j : ι') (s : Fin N.A)
    (x : Gate ι' N.A) : x ∉ paG N (Gate.fa j s) := by simp [paG]

theorem mem_paG_mid {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : NPar) (k : Fin N.A) (x : Gate ι' N.A) :
    x ∈ paG N (Gate.mid k) ↔ ∃ p : ι' × Fin N.A, x = Gate.fa p.1 p.2 := by
  simp only [paG, mem_image, mem_univ, true_and]
  exact exists_congr fun p => eq_comm

theorem mem_paG_ib {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : NPar) (j : Fin N.A) (x : Gate ι' N.A) :
    x ∈ paG N (Gate.ib j) ↔ ∃ k : Fin N.A, x = Gate.mid k := by
  simp only [paG, mem_image, mem_univ, true_and]
  exact exists_congr fun p => eq_comm

theorem mem_paG_car {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : NPar) (j : Fin (N.A * N.A)) (x : Gate ι' N.A) :
    x ∈ paG N (Gate.car j) ↔ x = Gate.ib ⟨j.val % N.A, Nat.mod_lt _ N.toPar.A_pos⟩ ∨
      ∃ h : 0 < j.val, x = Gate.car ⟨j.val - 1, by have := j.2; omega⟩ := by
  unfold paG
  rw [mem_insert]
  apply or_congr Iff.rfl
  by_cases h : 0 < j.val
  · simp [h]
  · simp [h]

theorem child_gt {c : Fin K} {q : Gate (ιc c) N0.A} {x : CG ι ιc N0.A}
    (hx : CG.gt c q ∈ paC (w := w) φ x) : ∃ g', x = CG.gt c g' ∧ q ∈ paG (NP N0 w c) g' := by
  cases x with
  | src i' s' => exact absurd hx (by simp [paC])
  | gt c' g' =>
    rcases mem_pa_gt φ hx with ⟨q', hq, h⟩ | h
    · injection h with h1 h2
      subst h1
      have h2 := eq_of_heq h2
      subst h2
      exact ⟨g', rfl, hq⟩
    · cases g' <;> simp [extraPa] at h

/-! ### children -/

/-- number of (identity, slot) pairs reading shared slot `i` -/
def occ (i : ι) : ℕ := (univ.filter (fun p : (Σ c : Fin K, ιc c) => φ p.1 p.2 = i)).card

/-- bound on the number of children of a gate -/
def chB : CG ι ιc N0.A → ℕ
  | .src i _ => occ (ιc := ιc) φ i
  | .gt _ (Gate.car _) => 1
  | .gt _ _ => N0.A

theorem chd_le (g : CG ι ιc N0.A) :
    PForcedW.chd (edgeNet (w := w) φ F ok) g ≤ chB φ g := by
  unfold PForcedW.chd
  show (univ.filter fun j => g ∈ paC (w := w) φ j).card ≤ _
  cases g with
  | src i s =>
    have hsub : (univ.filter fun j => CG.src i s ∈ paC (w := w) φ j) ⊆
        (univ.filter (fun p : (Σ c : Fin K, ιc c) => φ p.1 p.2 = i)).image
          (fun p => CG.gt p.1 (Gate.fa p.2 s)) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      cases x with
      | src i' s' => exact absurd hx (by simp [paC])
      | gt c' g' =>
        rcases mem_pa_gt φ hx with ⟨q, hq, h⟩ | h
        · cases h
        · cases g' with
          | fa j' s' =>
            have h2 : (CG.src i s : CG ι ιc N0.A) = CG.src (φ c' j') s' := by simpa [extraPa] using h
            injection h2 with h3 h4
            subst h4
            exact mem_image.2 ⟨⟨c', j'⟩, by simp [h3.symm], rfl⟩
          | mid k => exact absurd h (by simp [extraPa])
          | ib k => exact absurd h (by simp [extraPa])
          | car k => exact absurd h (by simp [extraPa])
    exact (card_le_card hsub).trans card_image_le
  | gt c g =>
    cases g with
    | fa j s =>
      have hsub : (univ.filter fun x => CG.gt c (Gate.fa j s) ∈ paC (w := w) φ x) ⊆
          (univ : Finset (Fin N0.A)).image (fun k => CG.gt c (Gate.mid k)) := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        cases x with
        | src i' s' => exact absurd hx (by simp [paC])
        | gt c' g' =>
          rcases mem_pa_gt φ hx with ⟨q, hq, h⟩ | h
          · injection h with h1 h2
            subst h1
            have h2 := eq_of_heq h2
            subst h2
            cases g' with
            | fa j' s' => exact absurd hq (not_mem_paG_fa _ _ _ _)
            | mid k => exact mem_image.2 ⟨k, mem_univ _, rfl⟩
            | ib k =>
              obtain ⟨k', hk'⟩ := (mem_paG_ib _ _ _).1 hq; cases hk'
            | car k =>
              rcases (mem_paG_car _ _ _).1 hq with hq | ⟨_, hq⟩ <;> cases hq
          · cases g' <;> simp [extraPa] at h
      exact (card_le_card hsub).trans (card_image_le.trans (le_of_eq (by simp [chB])))
    | mid k =>
      have hsub : (univ.filter fun x => CG.gt c (Gate.mid k) ∈ paC (w := w) φ x) ⊆
          (univ : Finset (Fin N0.A)).image (fun j => CG.gt c (Gate.ib j)) := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        obtain ⟨g', rfl, hq⟩ := child_gt φ hx
        cases g' with
        | fa j' s' => exact absurd hq (not_mem_paG_fa _ _ _ _)
        | mid k' => obtain ⟨p, hp⟩ := (mem_paG_mid _ _ _).1 hq; cases hp
        | ib j' => exact mem_image.2 ⟨j', mem_univ _, rfl⟩
        | car j' => rcases (mem_paG_car _ _ _).1 hq with hq | ⟨_, hq⟩ <;> cases hq
      exact (card_le_card hsub).trans (card_image_le.trans (le_of_eq (by simp [chB])))
    | ib j1 =>
      have hsub : (univ.filter fun x => CG.gt c (Gate.ib j1) ∈ paC (w := w) φ x) ⊆
          ((univ : Finset (Fin (N0.A * N0.A))).filter (fun j => j.val % N0.A = j1.val)).image
            (fun j => CG.gt c (Gate.car j)) := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        obtain ⟨g', rfl, hq⟩ := child_gt φ hx
        cases g' with
        | fa j' s' => exact absurd hq (not_mem_paG_fa _ _ _ _)
        | mid k' => obtain ⟨p, hp⟩ := (mem_paG_mid _ _ _).1 hq; cases hp
        | ib j' => obtain ⟨p, hp⟩ := (mem_paG_ib _ _ _).1 hq; cases hp
        | car j' =>
          rcases (mem_paG_car _ _ _).1 hq with hq | ⟨_, hq⟩
          · injection hq with hq
            exact mem_image.2 ⟨j', by simp only [mem_filter, mem_univ, true_and]; rw [hq]; rfl, rfl⟩
          · cases hq
      exact (card_le_card hsub).trans (card_image_le.trans (card_mod_eq_le N0.A j1.val))
    | car j =>
      show _ ≤ 1
      refine card_le_one.2 fun x hx y hy => ?_
      simp only [mem_filter, mem_univ, true_and] at hx hy
      obtain ⟨gx, rfl, hqx⟩ := child_gt φ hx
      obtain ⟨gy, rfl, hqy⟩ := child_gt φ hy
      have key : ∀ g' : Gate (ιc c) N0.A, Gate.car j ∈ paG (NP N0 w c) g' →
          ∃ j' : Fin (N0.A * N0.A), g' = Gate.car j' ∧ j'.val = j.val + 1 := by
        intro g' hq
        cases g' with
        | fa j' s' => exact absurd hq (not_mem_paG_fa _ _ _ _)
        | mid k' => obtain ⟨p, hp⟩ := (mem_paG_mid _ _ _).1 hq; cases hp
        | ib j' => obtain ⟨p, hp⟩ := (mem_paG_ib _ _ _).1 hq; cases hp
        | car j' =>
          rcases (mem_paG_car _ _ _).1 hq with hq | ⟨h0, hq⟩
          · cases hq
          · injection hq with hq
            refine ⟨j', rfl, ?_⟩
            have := congrArg Fin.val hq
            simp only at this; omega
      obtain ⟨jx, rfl, hjx⟩ := key gx hqx
      obtain ⟨jy, rfl, hjy⟩ := key gy hqy
      have : jx = jy := Fin.ext (by omega)
      rw [this]

/-! ### per-gate weight bound -/

/-- bound on the shared bits of a gate -/
def Bw : CG ι ιc N0.A → ℕ
  | .src i _ => occ (ιc := ιc) φ i * eS N0
  | .gt c (Gate.fa _ _) => eS N0 + N0.A * eM N0 w c
  | .gt c (Gate.mid _) => Fintype.card (ιc c) * N0.A * eM N0 w c + N0.A * eM N0 w c
  | .gt c (Gate.ib _) => N0.A * eM N0 w c + N0.A * eM N0 w c
  | .gt c (Gate.car _) => 2 * eM N0 w c + eM N0 w c

theorem inW_le (g : CG ι ιc N0.A) :
    PForcedW.inW (edgeNet (w := w) φ F ok) g ≤
      match g with
      | .src _ _ => 0
      | .gt c (Gate.fa _ _) => eS N0
      | .gt c (Gate.mid _) => Fintype.card (ιc c) * N0.A * eM N0 w c
      | .gt c (Gate.ib _) => N0.A * eM N0 w c
      | .gt c (Gate.car _) => 2 * eM N0 w c := by
  unfold PForcedW.inW
  show ∑ j ∈ paC (w := w) φ g, ((edgeNet (w := w) φ F ok).w j + 1) ≤ _
  have h1 : ∑ j ∈ paC (w := w) φ g, ((edgeNet (w := w) φ F ok).w j + 1) ≤
      ∑ j ∈ paC (w := w) φ g, ewid N0 w j :=
    sum_le_sum fun j _ => msg_w_le (w := w) φ F ok j
  refine h1.trans ?_
  have h2 := pa_card (w := w) φ g
  cases g with
  | src i s => simp [paC]
  | gt c g =>
    have h3 := fun j hj => pa_wid (w := w) φ (CG.gt c g) j hj
    cases g with
    | fa j s =>
      refine (sum_le_card_nsmul _ _ _ h3).trans ?_
      rw [smul_eq_mul]
      exact (Nat.mul_le_mul_right _ h2).trans (le_of_eq (one_mul _))
    | mid k =>
      refine (sum_le_card_nsmul _ _ _ h3).trans ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ h2
    | ib j =>
      refine (sum_le_card_nsmul _ _ _ h3).trans ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ h2
    | car j =>
      refine (sum_le_card_nsmul _ _ _ h3).trans ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ h2

theorem gate_le (g : CG ι ιc N0.A) :
    PForcedW.inW (edgeNet (w := w) φ F ok) g +
      PForcedW.chd (edgeNet (w := w) φ F ok) g * ((edgeNet (w := w) φ F ok).w g + 1) ≤ Bw (w := w) φ g := by
  have h1 := inW_le (w := w) φ F ok g
  have h2 := chd_le (w := w) φ F ok g
  have h3 := msg_w_le (w := w) φ F ok g
  have h4 : PForcedW.chd (edgeNet (w := w) φ F ok) g * ((edgeNet (w := w) φ F ok).w g + 1) ≤
      chB φ g * ewid N0 w g := Nat.mul_le_mul h2 h3
  cases g with
  | src i s => simp only [Bw, chB, ewid] at *; omega
  | gt c g =>
    cases g with
    | fa j s => simp only [Bw, chB, ewid] at *; omega
    | mid k => simp only [Bw, chB, ewid] at *; omega
    | ib j => simp only [Bw, chB, ewid] at *; omega
    | car j => simp only [Bw, chB, ewid] at *; omega

/-! ### total weight in closed form -/

theorem sum_gate {ι' : Type} [Fintype ι'] [DecidableEq ι'] {A : ℕ} (f : Gate ι' A → ℕ) :
    ∑ g, f g = ∑ p : ι' × Fin A, f (Gate.fa p.1 p.2) + (∑ k : Fin A, f (Gate.mid k) +
      (∑ j : Fin A, f (Gate.ib j) + ∑ j : Fin (A * A), f (Gate.car j))) := by
  rw [← (gateEquiv ι' A).symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  rfl

theorem sum_CG (f : CG ι ιc N0.A → ℕ) :
    ∑ g, f g = ∑ p : ι × Fin N0.A, f (CG.src p.1 p.2) + ∑ c : Fin K, ∑ g : Gate (ιc c) N0.A, f (CG.gt c g) := by
  rw [← (cgEquiv ι ιc N0.A).symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma]
  rfl

theorem sum_occ : ∑ i : ι, occ (ιc := ιc) φ i = ∑ c : Fin K, Fintype.card (ιc c) := by
  unfold occ
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : (Σ c : Fin K, ιc c) => φ p.1 p.2)
    (s := univ) (t := univ) (fun _ _ => mem_univ _)]
  simp [Fintype.card_sigma]

/-- the closed form of the total weight `Σ_g Bw g` -/
def Wsum (N0 : NPar) (w : Fin K → ℕ) (nc : Fin K → ℕ) : ℕ :=
  ∑ c : Fin K, (2 * nc c * N0.A * eS N0 + 2 * nc c * N0.A * N0.A * eM N0 w c + 6 * N0.A * N0.A * eM N0 w c)

theorem sum_Bw : ∑ g : CG ι ιc N0.A, Bw (w := w) φ g = Wsum N0 w (fun c => Fintype.card (ιc c)) := by
  rw [sum_CG]
  have h1 : ∑ p : ι × Fin N0.A, Bw (w := w) φ (CG.src p.1 p.2) =
      N0.A * eS N0 * ∑ c : Fin K, Fintype.card (ιc c) := by
    rw [← sum_occ (ιc := ιc) φ, Fintype.sum_prod_type]
    simp only [Bw, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rw [mul_sum]
    refine sum_congr rfl fun i _ => by ring
  rw [h1, mul_sum, ← sum_add_distrib]
  unfold Wsum
  refine sum_congr rfl fun c _ => ?_
  rw [sum_gate]
  simp only [Bw, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_prod]
  ring

end
end ECDLP.L57
end
