import ECDLP.L73_Dec

/-!
# L73 / Par: the parent relation of `edgeNet` in terms of enumeration indices
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (L : Lay ι ιc)
  (φ : ∀ c, ιc c → ι)

/-- gates of block `c` are exactly the indices in its range -/
theorem blockOf (qp : CG ι ιc N0.A) (c : Fin K) (hlo : L.nι * N0.A + L.off N0.A c ≤ L.enum N0.A qp)
    (hhi : (L.enum N0.A qp : ℕ) < L.nι * N0.A + L.off N0.A c + L.blk N0.A c) :
    ∃ g, qp = CG.gt c g ∧ (L.enum N0.A qp : ℕ) = L.nι * N0.A + (L.off N0.A c + (L.gateE N0.A c g : ℕ)) := by
  cases qp with
  | src i s =>
    rw [Lay.enum_src] at hlo
    have := (L.eι i).2
    have := s.2
    exfalso
    have : (L.eι i : ℕ) * N0.A + s < L.nι * N0.A := by nlinarith
    omega
  | gt c' g' =>
    rw [Lay.enum_gt] at hlo hhi
    have hg' := (L.gateE N0.A c' g').2
    have hc : c' = c := by
      by_contra hne
      rcases lt_or_gt_of_ne (show c'.val ≠ c.val from fun h => hne (Fin.ext h)) with h | h
      · have h1 := L.off_mono N0.A (show c'.val + 1 ≤ c.val by omega)
        rw [Lay.off_lt_succ] at h1
        unfold Lay.blk at hg' h1
        omega
      · have h1 := L.off_mono N0.A (show c.val + 1 ≤ c'.val by omega)
        rw [Lay.off_lt_succ] at h1
        omega
    subst hc
    exact ⟨g', rfl, by rw [Lay.enum_gt]⟩

/-- the parent relation as a predicate on indices -/
def PA : CG ι ιc N0.A → ℕ → Prop
  | .src _ _, _ => False
  | .gt c (.fa j s), x => x = L.eι (φ c j) * N0.A + s
  | .gt c (.mid _), x => L.nι * N0.A + L.off N0.A c ≤ x ∧ x < L.nι * N0.A + L.off N0.A c + L.nc c * N0.A
  | .gt c (.ib _), x => L.nι * N0.A + L.off N0.A c + L.nc c * N0.A ≤ x ∧
      x < L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A
  | .gt c (.car j), x => x = L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + j.val % N0.A ∨
      (0 < j.val ∧ x + 1 = L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A + N0.A + j.val)

theorem paG_fa (c : Fin K) (j : ιc c) (s : Fin N0.A) (x : Gate (ιc c) N0.A) :
    x ∈ paG (NP N0 w c) (Gate.fa j s) ↔ False := by
  show x ∈ (∅ : Finset (Gate (ιc c) N0.A)) ↔ False
  simp
theorem paG_mid (c : Fin K) (k : Fin N0.A) (x : Gate (ιc c) N0.A) :
    x ∈ paG (NP N0 w c) (Gate.mid k) ↔ ∃ i s, x = Gate.fa i s := by
  show x ∈ (univ.image (fun p : ιc c × Fin N0.A => Gate.fa p.1 p.2)) ↔ _
  constructor
  · intro h
    obtain ⟨⟨i, s⟩, _, hh⟩ := Finset.mem_image.1 h
    exact ⟨i, s, hh.symm⟩
  · rintro ⟨i, s, rfl⟩
    exact Finset.mem_image.2 ⟨(i, s), mem_univ _, rfl⟩
theorem paG_ib (c : Fin K) (j : Fin N0.A) (x : Gate (ιc c) N0.A) :
    x ∈ paG (NP N0 w c) (Gate.ib j) ↔ ∃ k, x = Gate.mid k := by
  show x ∈ (univ.image (fun k : Fin N0.A => Gate.mid k)) ↔ _
  constructor
  · intro h
    obtain ⟨k, _, hh⟩ := Finset.mem_image.1 h
    exact ⟨k, hh.symm⟩
  · rintro ⟨k, rfl⟩
    exact Finset.mem_image.2 ⟨k, mem_univ _, rfl⟩
theorem paG_car (c : Fin K) (j : Fin (N0.A * N0.A)) (x : Gate (ιc c) N0.A) :
    x ∈ paG (NP N0 w c) (Gate.car j) ↔ x = Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩ ∨
      (0 < j.val ∧ x = Gate.car ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2⟩) := by
  show x ∈ insert (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩)
      (if h : 0 < j.val then {Gate.car ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2⟩} else ∅) ↔ _
  by_cases h : 0 < j.val
  · rw [dif_pos h]
    constructor
    · intro hx
      rcases Finset.mem_insert.1 hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨h, Finset.mem_singleton.1 hx⟩
    · rintro (hx | ⟨_, hx⟩)
      · exact Finset.mem_insert.2 (Or.inl hx)
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hx))
  · rw [dif_neg h]
    constructor
    · intro hx
      rcases Finset.mem_insert.1 hx with hx | hx
      · exact Or.inl hx
      · exact absurd hx (Finset.notMem_empty _)
    · rintro (hx | ⟨h', _⟩)
      · exact Finset.mem_insert.2 (Or.inl hx)
      · exact absurd h' h

theorem mem_paC_iff (c : Fin K) (g : Gate (ιc c) N0.A) (x : CG ι ιc N0.A) :
    x ∈ paC (w := w) φ (CG.gt c g) ↔ (∃ q : Gate (ιc c) N0.A, q ∈ paG (NP N0 w c) g ∧ x = CG.gt c q) ∨ x ∈ extraPa φ c g := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨q, hq, hh⟩ := Finset.mem_image.1 h
      exact Or.inl ⟨q, hq, hh.symm⟩
    · exact Or.inr h
  · rintro (⟨q, hq, rfl⟩ | h)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩)
    · exact Finset.mem_union_right _ h

theorem extra_fa (c : Fin K) (j : ιc c) (s : Fin N0.A) (x : CG ι ιc N0.A) :
    x ∈ extraPa φ c (Gate.fa j s) ↔ x = CG.src (φ c j) s := Finset.mem_singleton
theorem extra_mid (c : Fin K) (k : Fin N0.A) (x : CG ι ιc N0.A) :
    x ∈ extraPa φ c (Gate.mid k) ↔ False := by
  show x ∈ (∅ : Finset (CG ι ιc N0.A)) ↔ False
  simp
theorem extra_ib (c : Fin K) (k : Fin N0.A) (x : CG ι ιc N0.A) :
    x ∈ extraPa φ c (Gate.ib k) ↔ False := by
  show x ∈ (∅ : Finset (CG ι ιc N0.A)) ↔ False
  simp
theorem extra_car (c : Fin K) (k : Fin (N0.A * N0.A)) (x : CG ι ιc N0.A) :
    x ∈ extraPa φ c (Gate.car k) ↔ False := by
  show x ∈ (∅ : Finset (CG ι ιc N0.A)) ↔ False
  simp

theorem pa_iff (qp qc : CG ι ιc N0.A) :
    qp ∈ paC (w := w) φ qc ↔ PA L φ qc (L.enum N0.A qp) := by
  have hA := N0.toPar.A_pos
  cases qc with
  | src i s => simp [paC, PA]
  | gt c g =>
    rw [mem_paC_iff]
    cases g with
    | fa j s =>
      show _ ↔ (L.enum N0.A qp : ℕ) = _
      constructor
      · rintro (⟨q, hq, _⟩ | h)
        · exact absurd ((paG_fa c j s q).1 hq) id
        · rw [(extra_fa φ c j s qp).1 h, Lay.enum_src]
      · intro h
        right
        refine (extra_fa φ c j s qp).2 ?_
        have : L.enum N0.A qp = L.enum N0.A (.src (φ c j) s) := Fin.ext (by rw [h, Lay.enum_src])
        exact (L.enum N0.A).injective this
    | mid k =>
      show _ ↔ _ ∧ _
      constructor
      · rintro (⟨q', hq, rfl⟩ | h)
        · obtain ⟨i, s, rfl⟩ := (paG_mid c k q').1 hq
          rw [Lay.enum_gt, Lay.gateE_fa]
          have := (L.ecc c i).2
          have := s.2
          have : (L.ecc c i : ℕ) * N0.A + s < L.nc c * N0.A := by nlinarith
          constructor <;> omega
        · exact absurd ((extra_mid φ c k qp).1 h) id
      · rintro ⟨h1, h2⟩
        obtain ⟨g, rfl, hg⟩ := blockOf (N0 := N0) L qp c h1 (by unfold Lay.blk; omega)
        left
        cases g with
        | fa i s => exact ⟨_, (paG_mid c k _).2 ⟨i, s, rfl⟩, rfl⟩
        | mid k' => rw [Lay.gateE_mid] at hg; omega
        | ib j' => rw [Lay.gateE_ib] at hg; omega
        | car j' => rw [Lay.gateE_car] at hg; omega
    | ib j =>
      show _ ↔ _ ∧ _
      constructor
      · rintro (⟨q', hq, rfl⟩ | h)
        · obtain ⟨k, rfl⟩ := (paG_ib c j q').1 hq
          rw [Lay.enum_gt, Lay.gateE_mid]
          have := k.2
          constructor <;> omega
        · exact absurd ((extra_ib φ c j qp).1 h) id
      · rintro ⟨h1, h2⟩
        obtain ⟨g, rfl, hg⟩ := blockOf (N0 := N0) L qp c (by omega) (by unfold Lay.blk; omega)
        left
        cases g with
        | fa i s =>
          rw [Lay.gateE_fa] at hg
          have := (L.ecc c i).2
          have := s.2
          have : (L.ecc c i : ℕ) * N0.A + s < L.nc c * N0.A := by nlinarith
          omega
        | mid k' => exact ⟨_, (paG_ib c j _).2 ⟨k', rfl⟩, rfl⟩
        | ib j' => rw [Lay.gateE_ib] at hg; omega
        | car j' => rw [Lay.gateE_car] at hg; omega
    | car j =>
      show _ ↔ _ ∨ _
      constructor
      · rintro (⟨q', hq, rfl⟩ | h)
        · rcases (paG_car c j q').1 hq with rfl | ⟨h0, rfl⟩
          · left
            rw [Lay.enum_gt, Lay.gateE_ib]; simp only [Fin.val_mk]; omega
          · right
            rw [Lay.enum_gt, Lay.gateE_car]
            refine ⟨h0, ?_⟩
            have := j.2
            simp only [Fin.val_mk]
            omega
        · exact absurd ((extra_car φ c j qp).1 h) id
      · rintro (h | ⟨h0, h⟩)
        · obtain ⟨g, rfl, hg⟩ := blockOf (N0 := N0) L qp c (by omega) (by have := Nat.mod_lt j.val hA; unfold Lay.blk; omega)
          left
          have hj : j.val % N0.A < N0.A := Nat.mod_lt _ hA
          cases g with
          | fa i s =>
            rw [Lay.gateE_fa] at hg
            have := (L.ecc c i).2
            have := s.2
            have : (L.ecc c i : ℕ) * N0.A + s < L.nc c * N0.A := by nlinarith
            omega
          | mid k' => rw [Lay.gateE_mid] at hg; omega
          | ib j' =>
            rw [Lay.gateE_ib] at hg
            have : j' = ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩ := Fin.ext (by show (j' : ℕ) = j.val % N0.A; omega)
            subst this
            exact ⟨_, (paG_car c j _).2 (Or.inl rfl), rfl⟩
          | car j' => rw [Lay.gateE_car] at hg; omega
        · have hj := j.2
          obtain ⟨g, rfl, hg⟩ := blockOf (N0 := N0) L qp c (by omega) (by unfold Lay.blk; omega)
          left
          cases g with
          | fa i s =>
            rw [Lay.gateE_fa] at hg
            have := (L.ecc c i).2
            have := s.2
            have : (L.ecc c i : ℕ) * N0.A + s < L.nc c * N0.A := by nlinarith
            omega
          | mid k' => rw [Lay.gateE_mid] at hg; have := k'.2; omega
          | ib j' => rw [Lay.gateE_ib] at hg; have := j'.2; omega
          | car j' =>
            rw [Lay.gateE_car] at hg
            have : j' = ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2⟩ := Fin.ext (by simp; omega)
            subst this
            exact ⟨_, (paG_car c j _).2 (Or.inr ⟨h0, rfl⟩), rfl⟩
end
end ECDLP.L73
end
