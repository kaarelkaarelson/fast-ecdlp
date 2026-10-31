import ECDLP.L30_Chain
import Mathlib.Data.Fintype.Card

/-!
# L30 / Count: solutions of the constraint system = ordered generic decompositions

Field-level statement (witnesses: partial sums `S`, inverses `w`, slopes `l`).
Tuples have length `n + 1` (so `m = n + 1` points); `FB` is the factor-base predicate on
x-coordinates (e.g. `x.val < X` over `ZMod p`).
-/

set_option linter.unusedSectionVars false

namespace ECDLP.L30

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Extension of a finite tuple to `ℕ` by zero. -/
def ext {m : ℕ} {α : Type*} [Zero α] (f : Fin m → α) : ℕ → α :=
  fun i => if h : i < m then f ⟨i, h⟩ else 0

theorem ext_apply {m : ℕ} {α : Type*} [Zero α] (f : Fin m → α) (i : Fin m) :
    ext f (i : ℕ) = f i := by
  simp [ext]

variable {n : ℕ}

/-- Partial sums of the points of a tuple, in `W.Point`
(`psumF P k = Σ_{i ≤ k} P i`, with each `P i` read as an affine point). -/
noncomputable def psumF (P : Fin (n + 1) → F × F) (k : Fin (n + 1)) : W.Point :=
  ∑ i : Fin (n + 1), if i ≤ k then ptOf W (P i) else 0

/-- Genericity of all partial additions of a tuple: for every `k < n`, the partial sum
`P 0 + … + P k` is an affine point whose x-coordinate differs from `x (P (k+1))`. -/
def GenericF (P : Fin (n + 1) → F × F) : Prop :=
  ∀ k : Fin n, psumF W P k.castSucc ≠ 0 ∧ (coord W (psumF W P k.castSucc)).1 ≠ (P k.succ).1

/-- The constraint system (all witnesses explicit): `S 0 = P 0`, one generic-addition constraint
block per `k < n`, and `S n = R`. -/
def Constraints (P S : Fin (n + 1) → F × F) (w l : Fin n → F) (R : F × F) : Prop :=
  S 0 = P 0 ∧
  (∀ k : Fin n, StepC W (S k.castSucc).1 (S k.castSucc).2 (P k.succ).1 (P k.succ).2 (w k) (l k)
    (S k.succ).1 (S k.succ).2) ∧
  S (Fin.last n) = R

theorem psumF_eq (P : Fin (n + 1) → F × F) (k : Fin (n + 1)) :
    psumF W P k = psum (QP W (ext P)) k := by
  unfold psumF psum
  have h1 : (∑ i : Fin (n + 1), if i ≤ k then ptOf W (P i) else 0) =
      ∑ i : Fin (n + 1), (fun j : ℕ => if j ≤ (k : ℕ) then QP W (ext P) j else 0) (i : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ≤ k
    · have h' : (i : ℕ) ≤ (k : ℕ) := h
      simp [h, h', QP, ext_apply]
    · have h' : ¬ (i : ℕ) ≤ (k : ℕ) := h
      simp [h, h']
  rw [h1, Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ (k : ℕ) then QP W (ext P) j else 0)
    (n + 1), ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  have := k.isLt
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem genericF_iff (P : Fin (n + 1) → F × F) :
    GenericF W P ↔ Generic W (ext P) n := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    have e1 : psumF W P (Fin.castSucc ⟨k, hk⟩) = psum (QP W (ext P)) k := by
      rw [psumF_eq]; rfl
    have e2 : (P (Fin.succ ⟨k, hk⟩)) = ext P (k + 1) := by
      have := ext_apply P (Fin.succ ⟨k, hk⟩)
      rw [← this]; rfl
    rw [e1, e2] at this
    exact this
  · intro h k
    have := h k k.isLt
    have e1 : psumF W P (Fin.castSucc k) = psum (QP W (ext P)) k := by
      rw [psumF_eq]; rfl
    have e2 : (P (Fin.succ k)) = ext P (k + 1) := by
      have := ext_apply P (Fin.succ k)
      rw [← this]; simp
    rw [e1, e2]
    exact this

theorem constraints_iff (P S : Fin (n + 1) → F × F) (w l : Fin n → F) (R : F × F) :
    Constraints W P S w l R ↔
      Chain W (ext P) (ext S) (ext w) (ext l) n ∧ ext S n = R := by
  have eS : ∀ k : Fin n, ext S (k : ℕ) = S k.castSucc := fun k => by
    have := ext_apply S k.castSucc; simpa using this
  have eS' : ∀ k : Fin n, ext S ((k : ℕ) + 1) = S k.succ := fun k => by
    have := ext_apply S k.succ; simpa using this
  have eP' : ∀ k : Fin n, ext P ((k : ℕ) + 1) = P k.succ := fun k => by
    have := ext_apply P k.succ; simpa using this
  have ew : ∀ k : Fin n, ext w (k : ℕ) = w k := fun k => ext_apply w k
  have el : ∀ k : Fin n, ext l (k : ℕ) = l k := fun k => ext_apply l k
  have e0S : ext S 0 = S 0 := by simpa using ext_apply S 0
  have e0P : ext P 0 = P 0 := by simpa using ext_apply P 0
  have enS : ext S n = S (Fin.last n) := by simpa using ext_apply S (Fin.last n)
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨by rw [e0S, e0P, h0], fun k hk => ?_⟩, by rw [enS, h2]⟩
    have := h1 ⟨k, hk⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at this
    have a := eS ⟨k, hk⟩
    have b := eS' ⟨k, hk⟩
    have c := eP' ⟨k, hk⟩
    have d := ew ⟨k, hk⟩
    have e := el ⟨k, hk⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at a b c d e
    rw [a, b, c, d, e]
    exact this
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨by rw [← e0S, ← e0P, h0], fun k => ?_, by rw [← enS, h2]⟩
    have := h1 k k.isLt
    rw [eS k, eS' k, eP' k, ew k, el k] at this
    exact this

theorem chain_congr_iff {P S S' : ℕ → F × F} {w l w' l' : ℕ → F} {n : ℕ}
    (hS : ∀ k ≤ n, S' k = S k) (hw : ∀ k < n, w' k = w k) (hl : ∀ k < n, l' k = l k) :
    Chain W P S' w' l' n ↔ Chain W P S w l n := by
  unfold Chain
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨by rw [← hS 0 (Nat.zero_le _)]; exact h0, fun k hk => ?_⟩
    have := h k hk
    rwa [hS k hk.le, hS (k + 1) hk, hw k hk, hl k hk] at this
  · rintro ⟨h0, h⟩
    refine ⟨by rw [hS 0 (Nat.zero_le _)]; exact h0, fun k hk => ?_⟩
    have := h k hk
    rwa [← hS k hk.le, ← hS (k + 1) hk, ← hw k hk, ← hl k hk] at this

theorem nat_ns {P : Fin (n + 1) → F × F} (h : ∀ i, W.Nonsingular (P i).1 (P i).2) :
    ∀ i ≤ n, W.Nonsingular (ext P i).1 (ext P i).2 := by
  intro i hi
  have := h ⟨i, by omega⟩
  simpa [ext, show i < n + 1 by omega] using this

/-- The set of all constraint-satisfying tuples with their witnesses and with every `x_i` in the
factor base. -/
noncomputable def SolSet [Fintype F] (FB : F → Prop) (R : F × F) (n : ℕ) :
    Finset ((Fin (n + 1) → F × F) × (Fin (n + 1) → F × F) × (Fin n → F) × (Fin n → F)) := by
  classical
  exact Finset.univ.filter fun t =>
    (∀ i, W.Nonsingular (t.1 i).1 (t.1 i).2 ∧ FB (t.1 i).1) ∧
      Constraints W t.1 t.2.1 t.2.2.1 t.2.2.2 R

/-- The set of ordered generic factor-base tuples with sum `R`. -/
noncomputable def GenSet [Fintype F] (FB : F → Prop) (R : F × F) (n : ℕ) :
    Finset (Fin (n + 1) → F × F) := by
  classical
  exact Finset.univ.filter fun P =>
    (∀ i, W.Nonsingular (P i).1 (P i).2 ∧ FB (P i).1) ∧ GenericF W P ∧
      psumF W P (Fin.last n) = ptOf W R

/-- **field level**.** For a finite field and nonsingular `R`, the number of
(tuple, witnesses) satisfying the constraint system with all `x_i` in the factor base equals the
number of ordered generic factor-base tuples with sum `R`. -/
theorem card_sol_eq_card_gen [Fintype F] (FB : F → Prop) {R : F × F}
    (hR : W.Nonsingular R.1 R.2) (n : ℕ) :
    (SolSet W FB R n).card = (GenSet W FB R n).card := by
  classical
  apply Finset.card_bij (fun t _ => t.1)
  · -- maps into
    intro t ht
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨hns, hc⟩ := ht
    simp only [GenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hns, ?_⟩
    have hns' := nat_ns W (fun i => (hns i).1)
    obtain ⟨hch, hn⟩ := (constraints_iff W _ _ _ _ _).1 hc
    refine ⟨(genericF_iff W _).2 (chain_generic hns' hch), ?_⟩
    have := (chain_iff (n := n) (R := R) hns' hR).1 ⟨_, _, _, hch, hn⟩
    rw [psumF_eq]
    simpa using this.2
  · -- injective
    intro t ht t' ht' h
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    obtain ⟨hns, hc⟩ := ht
    obtain ⟨hns2, hc'⟩ := ht'
    obtain ⟨P, S, w, l⟩ := t
    obtain ⟨P', S', w', l'⟩ := t'
    change P = P' at h
    subst h
    have hns' := nat_ns W (fun i => (hns i).1)
    obtain ⟨hch, -⟩ := (constraints_iff W _ _ _ _ _).1 hc
    obtain ⟨hch', -⟩ := (constraints_iff W _ _ _ _ _).1 hc'
    obtain ⟨u1, u2⟩ := chain_unique hns' hch hch'
    have hS : S = S' := by
      funext i
      have := u1 i (by have := i.isLt; omega)
      simpa [ext_apply] using this
    have hw : w = w' := by
      funext k
      have := (u2 k k.isLt).1
      simpa [ext_apply] using this
    have hl : l = l' := by
      funext k
      have := (u2 k k.isLt).2
      simpa [ext_apply] using this
    subst hS hw hl
    rfl
  · -- surjective
    intro P hP
    simp only [GenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨hns, hg, hsum⟩ := hP
    have hns' := nat_ns W (fun i => (hns i).1)
    have hG := (genericF_iff W P).1 hg
    have hch := chain_complete hns' hG
    refine ⟨(P, fun i => canS W (ext P) i, fun k => canW W (ext P) k,
      fun k => canL W (ext P) k), ?_, rfl⟩
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hns, ?_⟩
    rw [constraints_iff]
    refine ⟨?_, ?_⟩
    · refine ((chain_congr_iff W (n := n) ?_ ?_ ?_).2 hch)
      · intro k hk
        simp [ext, show k < n + 1 by omega]
      · intro k hk
        simp [ext, hk]
      · intro k hk
        simp [ext, hk]
    · have : ext (fun i : Fin (n + 1) => canS W (ext P) i) n = canS W (ext P) n := by
        simp [ext]
      rw [this]
      simp only [canS]
      have h3 := psumF_eq W P (Fin.last n)
      rw [hsum, Fin.val_last] at h3
      rw [← h3]
      exact coord_ptOf hR

end ECDLP.L30
