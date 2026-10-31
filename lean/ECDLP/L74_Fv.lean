import FactoringAux.EngineBound
import ECDLP.L68_PEx0

/-!
# L74 / Fv: value bounds depend only on the free variables; free variables of `digE`
-/
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Factoring.Aux Ex

/-- `Bdd` depends only on the free variables. -/
theorem bdd_congr {V : ℕ} (A : ℕ → ℕ → ℕ) : ∀ (e : Ex) (s : ℕ → Prop) (σ σ' : ℕ → ℕ),
    (∀ y, s y → σ y = σ' y) → FV s e → (Bdd V σ A e ↔ Bdd V σ' A e)
  | lit _, _, _, _, _, _ => Iff.rfl
  | var x, _, _, _, h, hv => by simp only [Bdd, h x hv]
  | rd a i, s, σ, σ', h, hv => by
      have h1 := (FV_congr A i s σ σ' h hv).1
      have := bdd_congr (V := V) A i s σ σ' h hv
      simp only [Bdd, h1, this]
  | add e f, s, σ, σ', h, hv | mul e f, s, σ, σ', h, hv => by
      have h1 := (FV_congr A e s σ σ' h hv.1).1
      have h3 := (FV_congr A f s σ σ' h hv.2).1
      have := bdd_congr (V := V) A e s σ σ' h hv.1
      have := bdd_congr (V := V) A f s σ σ' h hv.2
      simp only [Bdd, h1, h3, *]
  | sub e f, s, σ, σ', h, hv | div e f, s, σ, σ', h, hv | mod e f, s, σ, σ', h, hv => by
      have := bdd_congr (V := V) A e s σ σ' h hv.1
      have := bdd_congr (V := V) A f s σ σ' h hv.2
      simp only [Bdd, *]
  | ifLt e f u v, s, σ, σ', h, hv => by
      have h1 := (FV_congr A e s σ σ' h hv.1).1
      have h3 := (FV_congr A f s σ σ' h hv.2.1).1
      have := bdd_congr (V := V) A e s σ σ' h hv.1
      have := bdd_congr (V := V) A f s σ σ' h hv.2.1
      have := bdd_congr (V := V) A u s σ σ' h hv.2.2.1
      have := bdd_congr (V := V) A v s σ σ' h hv.2.2.2
      simp only [Bdd, h1, h3, *]
  | lett x e b, s, σ, σ', h, hv => by
      have h1 := (FV_congr A e s σ σ' h hv.1).1
      have he := bdd_congr (V := V) A e s σ σ' h hv.1
      have h4 := bdd_congr (V := V) A b _ _ _ (agree_upd h x (eval σ A e)) hv.2
      show (Bdd V σ A e ∧ Bdd V (Function.update σ x (eval σ A e)) A b) ↔
        (Bdd V σ' A e ∧ Bdd V (Function.update σ' x (eval σ' A e)) A b)
      rw [← h1]
      exact and_congr he h4
  | sum x n m b, s, σ, σ', h, hv | prod x n m b, s, σ, σ', h, hv => by
      have h1 := (FV_congr A n s σ σ' h hv.1).1
      have h3 := (FV_congr A m s σ σ' h hv.2.1).1
      have hn := bdd_congr (V := V) A n s σ σ' h hv.1
      have hm := bdd_congr (V := V) A m s σ σ' h hv.2.1
      have hb : ∀ j, (Bdd V (Function.update σ x j) A b ↔ Bdd V (Function.update σ' x j) A b) :=
        fun j => bdd_congr (V := V) A b _ _ _ (agree_upd h x j) hv.2.2
      have hbe : ∀ j, eval (Function.update σ x j) A b = eval (Function.update σ' x j) A b :=
        fun j => (FV_congr A b _ _ _ (agree_upd h x j) hv.2.2).1
      simp only [Bdd, h1, h3, hn, hm, hb, hbe]
  | blk _ e, s, σ, σ', h, hv => bdd_congr (V := V) A e s σ σ' h hv
  | iter x y n i b, s, σ, σ', h, hv => by
      have h1 := (FV_congr A n s σ σ' h hv.1).1
      have h3 := (FV_congr A i s σ σ' h hv.2.1).1
      have hn := bdd_congr (V := V) A n s σ σ' h hv.1
      have hi := bdd_congr (V := V) A i s σ σ' h hv.2.1
      have hbe : ∀ j v, eval (Function.update (Function.update σ x j) y v) A b =
            eval (Function.update (Function.update σ' x j) y v) A b :=
        fun j v => (FV_congr A b _ _ _ (agree_upd (agree_upd h x j) y v) hv.2.2).1
      have hb : ∀ j v, (Bdd V (Function.update (Function.update σ x j) y v) A b ↔
            Bdd V (Function.update (Function.update σ' x j) y v) A b) :=
        fun j v => bdd_congr (V := V) A b _ _ _ (agree_upd (agree_upd h x j) y v) hv.2.2
      simp only [Bdd, h1, h3, hn, hi, hbe, hb]

/-- `σ'` agrees with `σ` on the slots below `u` and on `u+3 .. vs-1` (the slots that the local expressions never write) -/
def Agr (u vs : ℕ) (σ σ' : ℕ → ℕ) : Prop := ∀ y, (y < u ∨ (u + 2 < y ∧ y < vs)) → σ' y = σ y

theorem Agr.refl' {u vs : ℕ} {σ : ℕ → ℕ} : Agr u vs σ σ := fun _ _ => rfl

theorem Agr.upd {u vs : ℕ} {σ σ' : ℕ → ℕ} (h : Agr u vs σ σ') {x : ℕ} (hx : ¬ (x < u ∨ (u + 2 < x ∧ x < vs)))
    (v : ℕ) : Agr u vs σ (Function.update σ' x v) := fun y hy => by
  rw [Function.update_of_ne (by intro h'; subst h'; exact hx hy)]; exact h y hy

section dig
open ECDLP.L68 ECDLP.L56
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : ECDLP.L56.PForced (ZMod m) ι} {e : ι ≃ Fin g} {u : ℕ}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) P e u)

/-- the free variables of the digit expression (given those of the three node expressions it uses) -/
theorem fv_digE {t : ℕ} (hu : u + 10 ≤ t) (hnf : Ex.FV (· < t) X.nfE) (hnm : Ex.FV (· < t) X.nmE)
    (hpar : Ex.FV (· < t) X.parE) {fr tt : ℕ} (hfr : fr < t) (htt : tt < t) :
    Ex.FV (· < t) (digE X fr tt) := by
  have h1 : ∀ (b : Ex), Ex.FV (· < t) b → ∀ x, x < t → Ex.FV (· < t) (un1 X x b) := by
    intro b hb x hx
    exact ⟨hx, Ex.FV_mono (fun y hy => Or.inl hy) b hb⟩
  have h2 : ∀ p c, p < t → c < t → Ex.FV (· < t) (par2 X p c) := by
    intro p c hp hc
    simp only [par2, Ex.FV]
    exact ⟨hp, Or.inl hc, Ex.FV_mono (fun y hy => Or.inl (Or.inl hy)) _ hpar⟩
  have h3 : ∀ fr, fr < t → Ex.FV (· < t) (nAE X fr) := by
    intro fr hfr
    exact ⟨trivial, h2 _ _ (by omega) hfr, h1 _ hnm _ (by omega), trivial⟩
  have h4 : Ex.FV (· < t) (ppE X fr tt) :=
    ⟨htt, trivial, Ex.FV_mono (fun y hy => Or.inl hy) _ (h3 fr hfr)⟩
  exact ⟨⟨⟨(show u + 2 < t by omega), h1 _ hnf _ hfr⟩, h4⟩, h1 _ hnm _ htt⟩

end dig

end ECDLP.L74
end
