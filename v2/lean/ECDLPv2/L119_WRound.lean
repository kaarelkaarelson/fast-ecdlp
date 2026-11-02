import Mathlib
import ECDLPv2.L114_Round
import ECDLPv2.L119_WGen

set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L119

open ECDLP.L114 Finset

section round
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}

/-- the data of a round (functions of the transcript) with its row relations. -/
structure RoundSpecW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (f s Nd : ℕ) (O : Type*) where
  FB : Fin f → G
  Orc : List O → G → O
  shift : ℤ → List O → G
  Acc : List O → Prop
  pos : List O → (Fin f ⊕ Fin s → Fin Nd)
  Ttop : List O → Matrix (Fin f) (Fin f) ℤ
  Rint : List O → Matrix (Fin s) (Fin f) ℤ
  pos_inj : ∀ w, Acc w → Function.Injective (pos w)
  row_rel : ∀ (ν : ℤ) (a : Fin Nd → (Fin k → ZMod N)),
    Acc (trans (evG V hN) Orc (shift ν) [] Nd a) →
    ∀ i, ∑ F, relMat (Ttop (trans (evG V hN) Orc (shift ν) [] Nd a))
      (Rint (trans (evG V hN) Orc (shift ν) [] Nd a)) ν i F • FB F =
      evG V hN (a (pos (trans (evG V hN) Orc (shift ν) [] Nd a) i))


end round

section prime
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma-gen interface: among `s` independent uniform elements of the local relation lattice `K`, the
number of tuples that fail to generate `K` is at most a `1/D` fraction.  (Paper Lemma `gen`:
`D ≈ ℓ^{s-3}/2`.  Left as a named hypothesis in this lane.) -/
def GenBoundW {k : ℕ} (q : ℕ) [NeZero q] (K : AddSubgroup (Fin k → ZMod q)) (s D : ℕ) : Prop := by
  classical
  exact ((Fintype.piFinset (fun _ : Fin s => (univ.filter (fun x : Fin k → ZMod q => x ∈ K)))).filter
    (fun m => ¬ AddSubgroup.closure (Set.range m) = K)).card * D ≤ (Fintype.card K) ^ s

/-- goodness of the lattice phase at the prime power `q i`: the `s` lattice vectors generate `Rel_ℓ`. -/
def GoodAtW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (R : RoundSpecW V hN f s Nd O)
    (q : ι → ℕ) (i : ι) (hq : q i * cofac q i = N) (ν : ℤ) (a : Fin Nd → (Fin k → ZMod N)) : Prop :=
  AddSubgroup.closure (Set.range (combHom (rho (Dvd.intro _ hq))
      (kerMat (q i) (R.Ttop (trans (evG V hN) R.Orc (R.shift ν) [] Nd a))
        (R.Rint (trans (evG V hN) R.Orc (R.shift ν) [] Nd a)) ν)
      (fun r => a (R.pos (trans (evG V hN) R.Orc (R.shift ν) [] Nd a) r)))) =
    (evL V hN hq).ker

open Classical in
/-- **Fibrewise failure bound.**  On every fibre `{a | ev ∘ a = y}` on which the event `cond`
(acceptance + invertible planted block mod `q i`) holds, the lattice phase at `q i` fails to generate
`Rel_ℓ` for at most a `1/D` fraction of the tag-tuples. -/
theorem good_fibre_boundW {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0)
    (R : RoundSpecW V hN f s Nd O)
    (hsurj : Function.Surjective (evG V hN))
    (q : ι → ℕ) (i : ι) [NeZero (q i)] (hq : q i * cofac q i = N) (hcop : Nat.Coprime (cofac q i) (q i))
    (D : ℕ) (hGen : GenBoundW (q i) (evL V hN hq).ker s D) (ν : ℤ)
    (cond : (Fin Nd → (Fin k → ZMod N)) → Prop)
    (hc : ∀ a, cond a → R.Acc (trans (evG V hN) R.Orc (R.shift ν) [] Nd a) ∧
      IsUnit (((R.Ttop (trans (evG V hN) R.Orc (R.shift ν) [] Nd a) -
        Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod (q i)))).det)) :
    ∀ y : Fin Nd → G, (∃ a : Fin Nd → (Fin k → ZMod N),
        (fun t => evG V hN (a t)) = y ∧ cond a) →
      (univ.filter (fun a : Fin Nd → (Fin k → ZMod N) =>
        (fun t => evG V hN (a t)) = y ∧
          ¬ GoodAtW V hN R q i hq ν a)).card * D ≤
      (univ.filter (fun a : Fin Nd → (Fin k → ZMod N) =>
        (fun t => evG V hN (a t)) = y)).card := by
  rintro y ⟨a0, ha0, hc0⟩
  obtain ⟨hAcc, hB⟩ := hc a0 hc0
  set w0 := trans (evG V hN) R.Orc (R.shift ν) [] Nd a0 with hw0
  have hw : ∀ a : Fin Nd → (Fin k → ZMod N), (fun t => evG V hN (a t)) = y →
      trans (evG V hN) R.Orc (R.shift ν) [] Nd a = w0 := by
    intro a ha
    exact trans_eq_of_ev_eq _ _ _ _ _ _ _ (fun t => (congrFun ha t).trans (congrFun ha0 t).symm)
  have hrow : ∀ r, ∑ F, relMat (R.Ttop w0) (R.Rint w0) ν r F • R.FB F = y (R.pos w0 r) := by
    intro r
    rw [hw0, R.row_rel ν a0 hAcc r, ← congrFun ha0]
  obtain ⟨c, e1, e2⟩ := phase_genW V hN hq hcop hsurj R.FB (R.Ttop w0) (R.Rint w0) ν hB
    (R.pos w0) (R.pos_inj w0 hAcc) y hrow
    (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL V hN hq).ker)
  have k1 : (univ.filter (fun a : Fin Nd → (Fin k → ZMod N) =>
        (fun t => evG V hN (a t)) = y)).card =
      c * (Fintype.card ((evL V hN hq).ker)) ^ s := by
    rw [← e1]; congr 1; ext a; simp only [mem_filter, mem_univ, true_and]; exact funext_iff
  have k2 : (univ.filter (fun a : Fin Nd → (Fin k → ZMod N) =>
        (fun t => evG V hN (a t)) = y ∧ ¬ GoodAtW V hN R q i hq ν a)).card =
      c * ((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin k → ZMod (q i) => x ∈ (evL V hN hq).ker)))).filter
          (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL V hN hq).ker)).card := by
    rw [← e2]; congr 1; ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun t => congrFun h1 t, ?_⟩
      rw [GoodAtW, hw a h1] at h2; exact h2
    · rintro ⟨h1, h2⟩
      have h1' : (fun t => evG V hN (a t)) = y := funext h1
      refine ⟨h1', ?_⟩
      rw [GoodAtW, hw a h1']; exact h2
  rw [k1, k2]
  have := hGen
  unfold GenBoundW at this
  calc _ = c * (((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin k → ZMod (q i) => x ∈ (evL V hN hq).ker)))).filter
          (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL V hN hq).ker)).card * D) := by ring
    _ ≤ _ := Nat.mul_le_mul_left c (by convert this)

end prime
end ECDLP.L119
