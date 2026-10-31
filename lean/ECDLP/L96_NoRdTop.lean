import ECDLP.L96_Glue
import ECDLP.L89_Clamp

/-!
# L96 / NoRdTop: the five `E` expressions of a `PEx` read no array in `a`, given the same for the seven fields of the `PEx`
(the `NoRd` analogue of L91's `PSy`; generic in `u`), and for the clamp.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56

section
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι}
  {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))} {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))}
  {e : ι ≃ Fin g} {hF : ∀ i, Nonempty (P.Free i)} {u : ℕ} {a : ℕ → Prop}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- the fields of a `PEx` read no array in `a` -/
structure PNoRd (a : ℕ → Prop) : Prop where
  g : NoRd a X.gE
  nf : NoRd a X.nfE
  nm : NoRd a X.nmE
  w : NoRd a X.wE
  par : NoRd a X.parE
  out : NoRd a X.outE
  wt : NoRd a X.wtE

variable {X}

theorem NoRd_par2 (hX : PNoRd X a) (p c : ℕ) : NoRd a (par2 X p c) := by
  simp [par2, NoRd, hX.par]
theorem NoRd_un1 {t : ℕ} {body : Ex} (hb : NoRd a body) : NoRd a (un1 X t body) := by
  simp [un1, NoRd, hb]
theorem NoRd_nAE (hX : PNoRd X a) (fr : ℕ) : NoRd a (nAE X fr) := by
  have h1 := NoRd_par2 hX (u + 8) fr
  have h2 := NoRd_un1 (X := X) (t := u + 8) hX.nm
  simp [nAE, NoRd, h1, h2]
theorem NoRd_ppE (hX : PNoRd X a) (fr tt : ℕ) : NoRd a (ppE X fr tt) := by
  have := NoRd_nAE hX fr
  simp [ppE, nprod, NoRd, this]
theorem NoRd_digE64 (hX : PNoRd X a) (fr tt : ℕ) : NoRd a (ECDLP.L64.digE X fr tt) := by
  have h1 := NoRd_ppE hX fr tt
  have h2 := NoRd_un1 (X := X) (t := fr) hX.nf
  have h3 := NoRd_un1 (X := X) (t := tt) hX.nm
  simp [ECDLP.L64.digE, NoRd, h1, h2, h3]
theorem NoRd_mMsg (hX : PNoRd X a) (fr tt : ℕ) : NoRd a (mMsg X fr tt) := by
  have h1 := NoRd_digE64 hX fr tt
  have h2 := NoRd_par2 hX tt fr
  have h3 := NoRd_par2 hX fr tt
  simp [mMsg, NoRd, h1, h2, h3, hX.out]
theorem NoRd_szEx (hX : PNoRd X a) : NoRd a (szEx X) := by
  have h1 := NoRd_nAE hX u
  have h2 := NoRd_un1 (X := X) (t := u) hX.nf
  simp [szEx, nprod, NoRd, h1, h2, hX.g]
theorem NoRd_WEx (hX : PNoRd X a) : NoRd a (WEx X) := by
  simp [WEx, NoRd, hX.wt]
theorem NoRd_cEx (hX : PNoRd X a) : NoRd a (cEx X) := by
  have h1 := NoRd_par2 hX (u + 1) u
  have h2 := NoRd_par2 hX u (u + 1)
  have h3 := NoRd_un1 (X := X) (t := u + 1) hX.w
  have h4 := NoRd_un1 (X := X) (t := u) hX.w
  simp [cEx, NoRd, h1, h2, h3, h4]
theorem NoRd_msgTest {mE cE : Ex} (hm : NoRd a mE) (hc : NoRd a cE) (vq x : ℕ) :
    NoRd a (ECDLP.L64.msgTest mE cE vq x) := by
  simp [ECDLP.L64.msgTest, ifEq, pow2, NoRd, hm, hc]

/-- the five expressions of `edge_nrep` -/
def Efields (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) : NEx :=
  ⟨szEx X, WEx X, cEx X, msgTest (mMsg X u (u + 1)) (cEx X) (u + 3) (u + 9),
    msgTest (mMsg X (u + 1) u) (cEx X) (u + 3) (u + 9)⟩

/-- the node-count expression of a `PEx` -/
def gOf (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u) : Ex := X.gE

theorem NoRd_gOf (hX : PNoRd X a) : NoRd a (gOf X) := hX.g

theorem NoRd_Efields (hX : PNoRd X a) :
    NoRd a (Efields X).sz ∧ NoRd a (Efields X).W ∧ NoRd a (Efields X).c ∧ NoRd a (Efields X).l ∧ NoRd a (Efields X).r :=
  ⟨NoRd_szEx hX, NoRd_WEx hX, NoRd_cEx hX,
    NoRd_msgTest (NoRd_mMsg hX u (u + 1)) (NoRd_cEx hX) _ _, NoRd_msgTest (NoRd_mMsg hX (u + 1) u) (NoRd_cEx hX) _ _⟩

/-- the clamp changes `outE` to `outE % nm`; if the fields are `NoRd`, so are those of the clamped `PEx` -/
theorem pnoRd_clamp (hu : B ≤ u) (hX : PNoRd X a) : PNoRd (ECDLP.L89.clampPEx X hu) a := by
  refine ⟨hX.g, hX.nf, hX.nm, hX.w, hX.par, ?_, hX.wt⟩
  have := NoRd_un1 (X := X) (t := u + 5) hX.nm
  simp [ECDLP.L89.clampPEx, ECDLP.L89.clampE, NoRd, this, hX.out]

end
end ECDLP.L96
end
