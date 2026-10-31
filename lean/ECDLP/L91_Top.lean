import ECDLP.L91_Disp

/-!
# L91 / Top: `Sy` and the depth fields for the five E expressions `szEx, WEx, cEx, msgTest ..` of an L64 `PEx` at `u = 16`
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex

section
open ECDLP.L64 ECDLP.L56
variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι}
  {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))} {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))}
  {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)]
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e 16)

/-- the fields of a `PEx` are `Sy` -/
structure PSy : Prop where
  g : Sy X.gE
  nf : Sy X.nfE
  nm : Sy X.nmE
  w : Sy X.wE
  par : Sy X.parE
  out : Sy X.outE
  wt : Sy X.wtE

variable {X}

theorem Sy_par2 (hX : PSy X) {p c : ℕ} (hp : p < 990) (hc : c < 990) : Sy (par2 X p c) := by
  have := hX.par
  simp only [par2]; sy
theorem Sy_un1 {t : ℕ} {body : Ex} (ht : t < 990) (hb : Sy body) : Sy (un1 X t body) := by
  simp only [un1]; sy
theorem Sy_nAE (hX : PSy X) {fr : ℕ} (h : fr < 990) : Sy (nAE X fr) := by
  have := hX.nm
  have := Sy_par2 hX (p := 24) (c := fr) (by norm_num) h
  simp only [nAE, un1]; sy
theorem Sy_ppE (hX : PSy X) {fr tt : ℕ} (h : fr < 990) (h2 : tt < 990) : Sy (ppE X fr tt) := by
  have := Sy_nAE hX h
  simp only [ppE, nprod]; sy
theorem Sy_digE64 (hX : PSy X) {fr tt : ℕ} (h : fr < 990) (h2 : tt < 990) : Sy (ECDLP.L64.digE X fr tt) := by
  have := Sy_ppE hX h h2
  have := hX.nf; have := hX.nm
  simp only [ECDLP.L64.digE, un1]; sy
theorem Sy_mMsg (hX : PSy X) {fr tt : ℕ} (h : fr < 990) (h2 : tt < 990) : Sy (mMsg X fr tt) := by
  have := Sy_digE64 hX h h2
  have := Sy_par2 hX h2 h
  have := Sy_par2 hX h h2
  have := hX.out
  simp only [mMsg]; sy
theorem Sy_szEx (hX : PSy X) : Sy (szEx X) := by
  have := Sy_nAE hX (fr := 16) (by norm_num)
  have := hX.g; have := hX.nf
  simp only [szEx, un1, nprod]; sy
theorem Sy_WEx (hX : PSy X) : Sy (WEx X) := by
  have := hX.wt
  simp only [WEx]; sy
theorem Sy_cEx (hX : PSy X) : Sy (cEx X) := by
  have := Sy_par2 hX (p := 17) (c := 16) (by norm_num) (by norm_num)
  have := Sy_par2 hX (p := 16) (c := 17) (by norm_num) (by norm_num)
  have := hX.w
  simp only [cEx, un1]; sy
theorem Sy_msgTest (hX : PSy X) {mE cE : Ex} (hm : Sy mE) (hc : Sy cE) {vq x : ℕ} (hq : vq < 990) (hx1 : 10 ≤ x) (hx : x < 990) :
    Sy (ECDLP.L64.msgTest mE cE vq x) := by
  simp only [ECDLP.L64.msgTest]; sy

end
end ECDLP.L91
end
