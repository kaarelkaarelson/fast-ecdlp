import ECDLP.L85_B_Syn
import ECDLP.L86_RealC
import ECDLP.L83_Kinds
import ECDLP.L83_Depth
import ECDLP.L84_NoRdC

/-!
# L91 / Base: the syntactic predicate `Sy` (binders `>= 10`, variables `< 990`, array reads only as `0 < rd`) with closure lemmas
`Sy e := Ex.BGe 10 e /\ VB 990 e /\ RdN false e`.  All closure lemmas are conditional rewrite rules, so `simp [Sy_*]` proves `Sy` of
a concrete expression built from the combinators.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex

def Sy (e : Ex) : Prop := Ex.BGe 10 e ∧ VB 990 e ∧ RdN false e

theorem RdN_true_of_false : ∀ e : Ex, RdN false e → RdN true e
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .rd _ i, h => ⟨rfl, h.2⟩
  | .add _ _, h => h
  | .sub _ _, h => h
  | .mul _ _, h => h
  | .div _ _, h => h
  | .mod _ _, h => h
  | .ifLt _ _ _ _, h => h
  | .lett _ _ _, h => h
  | .sum _ _ _ _, h => h
  | .prod _ _ _ _, h => h
  | .blk _ _, h => h
  | .iter _ _ _ _ _, h => h

@[simp] theorem Sy_lit (k : ℕ) : Sy (.lit k) := ⟨trivial, trivial, trivial⟩
theorem Sy_var {x : ℕ} (h : x < 990) : Sy (.var x) := ⟨trivial, h, trivial⟩
theorem Sy_add {e f : Ex} (h1 : Sy e) (h2 : Sy f) : Sy (.add e f) := ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_sub {e f : Ex} (h1 : Sy e) (h2 : Sy f) : Sy (.sub e f) := ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_mul {e f : Ex} (h1 : Sy e) (h2 : Sy f) : Sy (.mul e f) := ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_div {e f : Ex} (h1 : Sy e) (h2 : Sy f) : Sy (.div e f) := ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_mod {e f : Ex} (h1 : Sy e) (h2 : Sy f) : Sy (.mod e f) := ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_ifLt {e f g h : Ex} (h1 : Sy e) (h2 : Sy f) (h3 : Sy g) (h4 : Sy h) : Sy (.ifLt e f g h) :=
  ⟨⟨h1.1, h2.1, h3.1, h4.1⟩, ⟨h1.2.1, h2.2.1, h3.2.1, h4.2.1⟩,
    ⟨h1.2.2, RdN_true_of_false _ h2.2.2 |> fun x => by
      cases hz : isZ e
      · exact h2.2.2
      · exact x, h3.2.2, h4.2.2⟩⟩
theorem Sy_lett {x : ℕ} {e b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h1 : Sy e) (h2 : Sy b) : Sy (.lett x e b) :=
  ⟨⟨hx1, h1.1, h2.1⟩, ⟨hx2, h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
theorem Sy_sum {x : ℕ} {n m b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h1 : Sy n) (h2 : Sy m) (h3 : Sy b) : Sy (.sum x n m b) :=
  ⟨⟨hx1, h1.1, h2.1, h3.1⟩, ⟨hx2, h1.2.1, h2.2.1, h3.2.1⟩, ⟨h1.2.2, h2.2.2, h3.2.2⟩⟩
theorem Sy_prod {x : ℕ} {n m b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h1 : Sy n) (h2 : Sy m) (h3 : Sy b) : Sy (.prod x n m b) :=
  ⟨⟨hx1, h1.1, h2.1, h3.1⟩, ⟨hx2, h1.2.1, h2.2.1, h3.2.1⟩, ⟨h1.2.2, h2.2.2, h3.2.2⟩⟩
theorem Sy_iter {x y : ℕ} {n i b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (hy1 : 10 ≤ y) (hy2 : y < 990) (h1 : Sy n) (h2 : Sy i)
    (h3 : Sy b) : Sy (.iter x y n i b) :=
  ⟨⟨hx1, hy1, h1.1, h2.1, h3.1⟩, ⟨hx2, hy2, h1.2.1, h2.2.1, h3.2.1⟩, ⟨h1.2.2, h2.2.2, h3.2.2⟩⟩
theorem Sy_bitRd {a : ℕ} {i : Ex} (h : Sy i) : Sy (bitRd a i) :=
  ⟨⟨trivial, h.1, trivial, trivial⟩, ⟨trivial, h.2.1, trivial, trivial⟩, ⟨trivial, ⟨rfl, h.2.2⟩, trivial, trivial⟩⟩
theorem Sy_nsum {x : ℕ} {n b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h1 : Sy n) (h3 : Sy b) : Sy (nsum x n b) :=
  Sy_sum hx1 hx2 h1 (Sy_lit 0) h3
theorem Sy_nprod {x : ℕ} {n b : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h1 : Sy n) (h3 : Sy b) : Sy (nprod x n b) :=
  Sy_prod hx1 hx2 h1 (Sy_lit 0) h3
theorem Sy_pow2 {x : ℕ} {e : Ex} (hx1 : 10 ≤ x) (hx2 : x < 990) (h : Sy e) : Sy (pow2 x e) :=
  Sy_prod hx1 hx2 h (Sy_lit 0) (Sy_lit 2)
theorem Sy_ifEq {e f g h : Ex} (h1 : Sy e) (h2 : Sy f) (h3 : Sy g) (h4 : Sy h) : Sy (ifEq e f g h) :=
  Sy_ifLt h1 h2 h4 (Sy_ifLt h2 h1 h4 h3)


theorem Sy_tabX {e : Ex} (he : Sy e) : ∀ (vs : List Ex) (k : ℕ), (∀ y ∈ vs, Sy y) → Sy (ECDLP.L83.tabX e k vs)
  | [], k, _ => by simp [ECDLP.L83.tabX]
  | y :: vs, k, h => by
    simp only [ECDLP.L83.tabX]
    exact Sy_ifLt he (Sy_lit _) (h y (by simp)) (Sy_tabX he vs (k + 1) (fun z hz => h z (by simp [hz])))

theorem Sy_lits (l : List ℕ) : ∀ y ∈ ECDLP.L83.lits l, Sy y := by
  intro y hy
  simp only [ECDLP.L83.lits, List.mem_map] at hy
  obtain ⟨k, -, rfl⟩ := hy
  exact Sy_lit k

theorem Sy_aff {cv : ℕ} (h : cv < 990) (k m : ℕ) : Sy (ECDLP.L83.aff cv k m) :=
  Sy_sub (Sy_add (Sy_var h) (Sy_lit _)) (Sy_lit _)


theorem Sy_ifLt_rd {a : ℕ} {i g h : Ex} (hi : Sy i) (hg : Sy g) (hh : Sy h) : Sy (.ifLt (.lit 0) (.rd a i) g h) :=
  ⟨⟨trivial, hi.1, hg.1, hh.1⟩, ⟨trivial, hi.2.1, hg.2.1, hh.2.1⟩, ⟨trivial, ⟨rfl, hi.2.2⟩, hg.2.2, hh.2.2⟩⟩

macro "sy" : tactic => `(tactic| simp (maxDischargeDepth := 150) [Sy_var, Sy_add, Sy_sub, Sy_mul, Sy_div, Sy_mod, Sy_ifLt_rd, Sy_ifLt,
  Sy_lett, Sy_sum, Sy_prod, Sy_iter, Sy_bitRd, Sy_nsum, Sy_nprod, Sy_pow2, Sy_ifEq, Sy_tabX, Sy_lits, Sy_aff, *])

end ECDLP.L91
end
