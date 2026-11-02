import Mathlib
import ECDLPv2.L114_Crt
import ECDLPv2.L114_Trans
import ECDLPv2.L114_Plant
import ECDLPv2.L114_Gen
import ECDLPv2.L114_Comb

/-!
# L114 / Round: one round of the planted-diagonal algorithm, as a finite probability space

Probability space: `ν ∈ [0, ν₀)` uniform and the tag sequence `a : Fin Nd → (Z/N)^4` uniform
(all counts are cardinalities of finite sets, never measures).  The *oracle* is an arbitrary function
`Orc : List O → G → O` of the history (stateful, adaptive); draw `t` presents the point
`R_t = ev(a_t) + shift ν (history)` (the planted `ν • F_i`, or `0`).

`RoundSpec` packages what the algorithm does with the transcript: acceptance event `Acc`, positions
`pos` of the accepted draws, and the integer relation matrix `[T' - νI ; R]` read off the answers,
subject to the *row relations* `row_rel` (each accepted row is a true relation; for the planted rows this
is `R - ν F_i`, see `planted_row_rel`).
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L114

open Finset

section round
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}

/-- the transcript depends on the tags only through `ev ∘ a`. -/
theorem trans_eq_of_ev_eq {A : Type*} [AddCommGroup A] (ev : A →+ G) (Orc : List O → G → O)
    (c : List O → G) :
    ∀ (n : ℕ) (h : List O) (a a' : Fin n → A), (∀ t, ev (a t) = ev (a' t)) →
      trans ev Orc c h n a = trans ev Orc c h n a' := by
  intro n
  induction n with
  | zero => intro h a a' _; simp [trans]
  | succ n ih =>
    intro h a a' haa
    simp only [trans]
    rw [haa 0]
    congr 1
    exact ih _ _ _ (fun t => haa t.succ)

/-- the data of a round (functions of the transcript) with its row relations. -/
structure RoundSpec (V : Fin 4 → G) (hN : ∀ g : G, N • g = 0) (f s Nd : ℕ) (O : Type*) where
  FB : Fin f → G
  Orc : List O → G → O
  shift : ℤ → List O → G
  Acc : List O → Prop
  pos : List O → (Fin f ⊕ Fin s → Fin Nd)
  Ttop : List O → Matrix (Fin f) (Fin f) ℤ
  Rint : List O → Matrix (Fin s) (Fin f) ℤ
  pos_inj : ∀ w, Acc w → Function.Injective (pos w)
  row_rel : ∀ (ν : ℤ) (a : Fin Nd → (Fin 4 → ZMod N)),
    Acc (trans (evG V hN) Orc (shift ν) [] Nd a) →
    ∀ i, ∑ F, relMat (Ttop (trans (evG V hN) Orc (shift ν) [] Nd a))
      (Rint (trans (evG V hN) Orc (shift ν) [] Nd a)) ν i F • FB F =
      evG V hN (a (pos (trans (evG V hN) Orc (shift ν) [] Nd a) i))

/-- relation of a planted row: the oracle's decomposition `R = ∑ FB(t_j)` of `R = ev a + ν F_k`
gives the row `mult(t) - ν e_k` with value `ev a`. -/
theorem planted_row_rel {m : ℕ} (FB : Fin f → G) (t : Fin m → Fin f) (k : Fin f) (ν : ℤ) :
    ∑ F, (multRow t F - ν * (if k = F then 1 else 0)) • FB F = (∑ j, FB (t j)) - ν • FB k := by
  simp only [sub_smul, Finset.sum_sub_distrib, row_of_decomp FB t, mul_smul, ite_smul, one_smul, zero_smul]
  simp

end round

section prime
variable {G : Type*} [AddCommGroup G] {N f s Nd : ℕ} [NeZero N] {O : Type*}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma-gen interface: among `s` independent uniform elements of the local relation lattice `K`, the
number of tuples that fail to generate `K` is at most a `1/D` fraction.  (Paper Lemma `gen`:
`D ≈ ℓ^{s-3}/2`.  Left as a named hypothesis in this lane.) -/
def GenBound (q : ℕ) [NeZero q] (K : AddSubgroup (Fin 4 → ZMod q)) (s D : ℕ) : Prop := by
  classical
  exact ((Fintype.piFinset (fun _ : Fin s => (univ.filter (fun x : Fin 4 → ZMod q => x ∈ K)))).filter
    (fun m => ¬ AddSubgroup.closure (Set.range m) = K)).card * D ≤ (Fintype.card K) ^ s

/-- goodness of the lattice phase at the prime power `q i`: the `s` lattice vectors generate `Rel_ℓ`. -/
def GoodAt (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0) (R : RoundSpec ![H1, H2, P, Q] hN f s Nd O)
    (q : ι → ℕ) (i : ι) (hq : q i * cofac q i = N) (ν : ℤ) (a : Fin Nd → (Fin 4 → ZMod N)) : Prop :=
  AddSubgroup.closure (Set.range (combHom (rho (Dvd.intro _ hq))
      (kerMat (q i) (R.Ttop (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a))
        (R.Rint (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a)) ν)
      (fun r => a (R.pos (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a) r)))) =
    (evL ![H1, H2, P, Q] hN hq).ker

open Classical in
/-- **Fibrewise failure bound.**  On every fibre `{a | ev ∘ a = y}` on which the event `cond`
(acceptance + invertible planted block mod `q i`) holds, the lattice phase at `q i` fails to generate
`Rel_ℓ` for at most a `1/D` fraction of the tag-tuples. -/
theorem good_fibre_bound (H1 H2 P Q : G) (hN : ∀ g : G, N • g = 0)
    (R : RoundSpec ![H1, H2, P, Q] hN f s Nd O)
    (hsurj : Function.Surjective (evG ![H1, H2, P, Q] hN))
    (q : ι → ℕ) (i : ι) [NeZero (q i)] (hq : q i * cofac q i = N) (hcop : Nat.Coprime (cofac q i) (q i))
    (D : ℕ) (hGen : GenBound (q i) (evL ![H1, H2, P, Q] hN hq).ker s D) (ν : ℤ)
    (cond : (Fin Nd → (Fin 4 → ZMod N)) → Prop)
    (hc : ∀ a, cond a → R.Acc (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a) ∧
      IsUnit (((R.Ttop (trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a) -
        Matrix.scalar (Fin f) ν).map (Int.castRingHom (ZMod (q i)))).det)) :
    ∀ y : Fin Nd → G, (∃ a : Fin Nd → (Fin 4 → ZMod N),
        (fun t => evG ![H1, H2, P, Q] hN (a t)) = y ∧ cond a) →
      (univ.filter (fun a : Fin Nd → (Fin 4 → ZMod N) =>
        (fun t => evG ![H1, H2, P, Q] hN (a t)) = y ∧
          ¬ GoodAt H1 H2 P Q hN R q i hq ν a)).card * D ≤
      (univ.filter (fun a : Fin Nd → (Fin 4 → ZMod N) =>
        (fun t => evG ![H1, H2, P, Q] hN (a t)) = y)).card := by
  rintro y ⟨a0, ha0, hc0⟩
  obtain ⟨hAcc, hB⟩ := hc a0 hc0
  set w0 := trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a0 with hw0
  have hw : ∀ a : Fin Nd → (Fin 4 → ZMod N), (fun t => evG ![H1, H2, P, Q] hN (a t)) = y →
      trans (evG ![H1, H2, P, Q] hN) R.Orc (R.shift ν) [] Nd a = w0 := by
    intro a ha
    exact trans_eq_of_ev_eq _ _ _ _ _ _ _ (fun t => (congrFun ha t).trans (congrFun ha0 t).symm)
  have hrow : ∀ r, ∑ F, relMat (R.Ttop w0) (R.Rint w0) ν r F • R.FB F = y (R.pos w0 r) := by
    intro r
    rw [hw0, R.row_rel ν a0 hAcc r, ← congrFun ha0]
  obtain ⟨c, e1, e2⟩ := phase_gen H1 H2 P Q hN hq hcop hsurj R.FB (R.Ttop w0) (R.Rint w0) ν hB
    (R.pos w0) (R.pos_inj w0 hAcc) y hrow
    (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL ![H1, H2, P, Q] hN hq).ker)
  have k1 : (univ.filter (fun a : Fin Nd → (Fin 4 → ZMod N) =>
        (fun t => evG ![H1, H2, P, Q] hN (a t)) = y)).card =
      c * (Fintype.card ((evL ![H1, H2, P, Q] hN hq).ker)) ^ s := by
    rw [← e1]; congr 1; ext a; simp only [mem_filter, mem_univ, true_and]; exact funext_iff
  have k2 : (univ.filter (fun a : Fin Nd → (Fin 4 → ZMod N) =>
        (fun t => evG ![H1, H2, P, Q] hN (a t)) = y ∧ ¬ GoodAt H1 H2 P Q hN R q i hq ν a)).card =
      c * ((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin 4 → ZMod (q i) => x ∈ (evL ![H1, H2, P, Q] hN hq).ker)))).filter
          (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL ![H1, H2, P, Q] hN hq).ker)).card := by
    rw [← e2]; congr 1; ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun t => congrFun h1 t, ?_⟩
      rw [GoodAt, hw a h1] at h2; exact h2
    · rintro ⟨h1, h2⟩
      have h1' : (fun t => evG ![H1, H2, P, Q] hN (a t)) = y := funext h1
      refine ⟨h1', ?_⟩
      rw [GoodAt, hw a h1']; exact h2
  rw [k1, k2]
  have := hGen
  unfold GenBound at this
  calc _ = c * (((Fintype.piFinset (fun _ : Fin s => (univ.filter
          (fun x : Fin 4 → ZMod (q i) => x ∈ (evL ![H1, H2, P, Q] hN hq).ker)))).filter
          (fun m => ¬ AddSubgroup.closure (Set.range m) = (evL ![H1, H2, P, Q] hN hq).ker)).card * D) := by ring
    _ ≤ _ := Nat.mul_le_mul_left c (by convert this)
end prime
end ECDLP.L114
