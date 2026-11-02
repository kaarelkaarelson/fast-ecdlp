import Mathlib
import ECDLPv2.L114_Round
import ECDLPv2.L119_WRound

/-!
# L116 / Row: the row relations of the algorithm's matrix are *proved*, not assumed

L114 packaged the round as a `RoundSpecW` whose field `row_rel` (each accepted row `r` of the relation matrix
satisfies `∑_F M_{rF} • FB_F = ev (a_{pos r})`) was a hypothesis.  Here we build the `RoundSpecW` from the
algorithm's actual description and *prove* `row_rel`:

* the oracle answers with an object `o : O` carrying (via `dec`) a decomposition `t : Fin m → Fin f` of the
  presented point into factor-base points, sound whenever `dec o = some t` (`hOrc`);
* draw `d < f` is planted: it presents `ev (a_d) + ν • FB d`; later draws present `ev (a_d)`
  (`plantedShift`, a function of the history length only, so the oracle may be stateful/adaptive);
* the accepted rows are read off the transcript: row `r` is the multiplicity vector of the decomposition
  in the answer at draw `pos w r` (`rowDec`), planted rows `inl i` at draw `i`, ordinary rows at draws `≥ f`.
-/
set_option linter.unusedSectionVars false
set_option linter.deprecated false
namespace ECDLP.L119

open ECDLP.L114 Finset

local notation "tr" => ECDLP.L114.trans

section trans_get
variable {A G O : Type*} [AddCommGroup A] [AddCommGroup G]

theorem trans_length (ev : A →+ G) (Orc : List O → G → O) (c : List O → G) :
    ∀ (n : ℕ) (h : List O) (a : Fin n → A), (ECDLP.L114.trans ev Orc c h n a).length = n := by
  intro n
  induction n with
  | zero => intro h a; simp [ECDLP.L114.trans]
  | succ n ih => intro h a; simp [ECDLP.L114.trans, ih]

/-- the `d`-th answer of the transcript is the oracle's reply to the `d`-th presented point, given the
previous answers. -/
theorem trans_get (ev : A →+ G) (Orc : List O → G → O) (c : List O → G) :
    ∀ (n : ℕ) (h : List O) (a : Fin n → A) (d : Fin n),
      (ECDLP.L114.trans ev Orc c h n a)[(d : ℕ)]? =
        some (Orc (h ++ (ECDLP.L114.trans ev Orc c h n a).take d)
          (ev (a d) + c (h ++ (ECDLP.L114.trans ev Orc c h n a).take d))) := by
  intro n
  induction n with
  | zero => intro h a d; exact d.elim0
  | succ n ih =>
    intro h a d
    refine Fin.cases ?_ (fun k => ?_) d
    · simp [ECDLP.L114.trans]
    · have := ih (h ++ [Orc h (ev (a 0) + c h)]) (Fin.tail a) k
      simp only [ECDLP.L114.trans, Fin.val_succ, List.getElem?_cons_succ, List.take_succ_cons]
      rw [this]
      simp [Fin.tail]

end trans_get

section build
variable {G : Type*} [AddCommGroup G] {N f s Nd m : ℕ} [NeZero N] {O : Type*}

/-- the planted shift: `ν • FB (idx h)` while `idx h < f`, `0` afterwards, where `idx h` is the number of rows
collected so far (a function of the history; with `idx = length` this is "draw `d` is planted for `d < f`"). -/
def plantedShift (FB : Fin f → G) (idx : List O → ℕ) (ν : ℤ) (h : List O) : G :=
  if hh : idx h < f then ν • FB ⟨idx h, hh⟩ else 0

/-- the decomposition carried by the answer at draw `pos w r`. -/
def rowDec (dec : O → Option (Fin m → Fin f)) (t0 : Fin m → Fin f) (w : List O) (d : ℕ) : Fin m → Fin f :=
  ((w[d]?).bind dec).getD t0

/-- **The algorithm's round, with proved row relations.**  `pos` gives the draw index of every row
(planted rows at their own draw `i`, ordinary rows at draws `≥ f`); `Acc` implies every row's answer carries a
decomposition. -/
def mkSpec {k : ℕ} (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (FB : Fin f → G) (idx : List O → ℕ) (Orc : List O → G → O)
    (dec : O → Option (Fin m → Fin f)) (t0 : Fin m → Fin f)
    (hOrc : ∀ (h : List O) (R : G) (t : Fin m → Fin f), dec (Orc h R) = some t → ∑ j, FB (t j) = R)
    (Acc : List O → Prop) (pos : List O → (Fin f ⊕ Fin s → Fin Nd))
    (hAcc : ∀ w, Acc w → ∀ r, ∃ t, (w[(pos w r : ℕ)]?).bind dec = some t)
    (hinl : ∀ w, Acc w → ∀ i : Fin f, idx (w.take (pos w (Sum.inl i))) = i)
    (hinr : ∀ w, Acc w → ∀ j : Fin s, f ≤ idx (w.take (pos w (Sum.inr j))))
    (pos_inj : ∀ w, Acc w → Function.Injective (pos w)) :
    RoundSpecW V hN f s Nd O where
  FB := FB
  Orc := Orc
  shift := fun ν h => plantedShift FB idx ν h
  Acc := Acc
  pos := pos
  Ttop := fun w => Matrix.of fun i F => multRow (rowDec dec t0 w (pos w (Sum.inl i))) F
  Rint := fun w => Matrix.of fun j F => multRow (rowDec dec t0 w (pos w (Sum.inr j))) F
  pos_inj := pos_inj
  row_rel := by
    intro ν a hacc r
    set ev := evG V hN with hev
    set w := ECDLP.L114.trans ev Orc (plantedShift FB idx ν) [] Nd a with hw
    have hlen' : w.length = Nd := trans_length ev Orc (plantedShift FB idx ν) Nd [] a
    set d := pos w r with hd
    obtain ⟨t, ht⟩ := hAcc w hacc r
    rw [← hd] at ht
    have hget := trans_get ev Orc (plantedShift FB idx ν) Nd [] a d
    rw [← hw] at hget
    simp only [List.nil_append] at hget
    rw [hget] at ht
    simp only [Option.bind_some] at ht
    have hsum := hOrc _ _ t ht
    have hrd : rowDec dec t0 w d = t := by
      unfold rowDec; rw [hget]; simp [ht]
    cases r with
    | inl i =>
      have hdi : idx (w.take d) = i := hinl w hacc i
      have hsh : plantedShift FB idx ν (w.take d) = ν • FB i := by
        unfold plantedShift
        rw [dif_pos (by rw [hdi]; exact i.2)]
        congr 2
        exact Fin.ext hdi
      rw [hsh] at hsum
      have hcoef : ∀ F, relMat (Matrix.of fun i F => multRow (rowDec dec t0 w (pos w (Sum.inl i))) F)
            (Matrix.of fun j F => multRow (rowDec dec t0 w (pos w (Sum.inr j))) F) ν (Sum.inl i) F =
          multRow t F - ν * (if i = F then 1 else 0) := by
        intro F
        simp [relMat, Matrix.fromRows_apply_inl, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.intCast_apply, ← hd, hrd]
      simp_rw [hcoef]
      rw [planted_row_rel FB t i ν, hsum]
      abel
    | inr j =>
      have hge : f ≤ idx (w.take d) := hinr w hacc j
      have hsh : plantedShift FB idx ν (w.take d) = 0 := by
        unfold plantedShift
        rw [dif_neg (by omega)]
      rw [hsh, add_zero] at hsum
      have hcoef : ∀ F, relMat (Matrix.of fun i F => multRow (rowDec dec t0 w (pos w (Sum.inl i))) F)
            (Matrix.of fun j F => multRow (rowDec dec t0 w (pos w (Sum.inr j))) F) ν (Sum.inr j) F =
          multRow t F := by
        intro F
        simp [relMat, Matrix.fromRows_apply_inr, ← hd, hrd]
      simp_rw [hcoef]
      rw [row_of_decomp FB t, hsum]

end build
end ECDLP.L119
