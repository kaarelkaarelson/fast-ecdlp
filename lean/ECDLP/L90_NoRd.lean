import ECDLP.L83_Kinds
import ECDLP.L84_NoRdC
import ECDLP.L90_Real

/-!
# L90 / NoRd: array-3 independence (indeed: no read of arrays `3` or `>= 12`) of ALL L83 expressions

`Out b := b = 3 \/ 12 <= b` (L84).  `NoRd Out` for `pE, szE, jm1E, prel, AEx, hEx, pbEx, bEx, MEx, ncEx, phiEx, nEx, lEx, rEx, negEx, epsEx`, then
`instNoRd_real : InstNoRd Out (instEx ..)`, `NoRd_phiExInst`, `NoRd_dispatchReal'` (L84's `NoRd_dispatchC` for `kindsReal'`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L90
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 Slot Cst
open ECDLP.L84 ECDLP.L83

section
variable (n u : ℕ) {a : ℕ → Prop}

theorem NoRd_pE : NoRd Out pE := NoRd_valE_lay 0 920 921 (by simp [Out])

theorem NoRd_szE : NoRd Out (szE u) := by
  simp [szE, nsum, pow2, pw2, NoRd, NoRd_pE]

theorem NoRd_log2E (x : Ex) (hx : NoRd Out x) : NoRd Out (log2E u x) := by
  simp [log2E, nsum, pow2, pw2, NoRd, hx]

theorem NoRd_jm1E : NoRd Out (jm1E u) := by
  have := NoRd_log2E u (.var (u + 63)) trivial
  simp only [jm1E, NoRd, and_true]; exact this

theorem NoRd_prel (body : Ex) (hb : NoRd Out body) : NoRd Out (prel u body) := by
  simp [prel, NoRd, NoRd_szE, NoRd_jm1E, pow2, pw2, hb]

theorem NoRd_AEx : NoRd Out (AEx u) := NoRd_prel u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_hEx : NoRd Out (hEx u) := NoRd_prel u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_pbEx : NoRd Out (pbEx u) := NoRd_prel u _ (by simp [pow2, pw2, NoRd])
theorem NoRd_bEx : NoRd Out (bEx u) := NoRd_prel u _ (by simp [NoRd])
theorem NoRd_MEx : NoRd Out (MEx u) := NoRd_prel u _ (by simp [NoRd])

theorem NoRd_sgcEx (cv : ℕ) : NoRd Out (sgcEx n cv) := NoRd_sgE _ (by simp [NoRd])

theorem NoRd_famChain (cv : ℕ) {rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn : Ex}
    (h1 : NoRd a rg) (h2 : NoRd a ue) (h3 : NoRd a cu) (h4 : NoRd a s0x) (h5 : NoRd a s0y) (h6 : NoRd a srx)
    (h7 : NoRd a sry) (h8 : NoRd a e0) (h9 : NoRd a e1) (h10 : NoRd a e2) (h11 : NoRd a e3) (h12 : NoRd a sn) :
    NoRd a (famChain n cv rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn) := by
  simp [famChain, NoRd, *]

theorem NoRd_tabX (e : Ex) (he : NoRd a e) : ∀ (vs : List Ex) (k : ℕ), (∀ v ∈ vs, NoRd a v) → NoRd a (tabX e k vs)
  | [], k, _ => by simp [tabX, NoRd]
  | y :: vs, k, h => by
    simp only [tabX, NoRd]
    exact ⟨he, trivial, h y (by simp), NoRd_tabX e he vs (k + 1) (fun v hv => h v (by simp [hv]))⟩

theorem NoRd_ifLt {e f x y : Ex} (h1 : NoRd a e) (h2 : NoRd a f) (h3 : NoRd a x) (h4 : NoRd a y) :
    NoRd a (.ifLt e f x y) := ⟨h1, h2, h3, h4⟩

theorem NoRd_aff (cv k m : ℕ) : NoRd a (aff cv k m) := by simp [aff, NoRd]

theorem NoRd_lits (l : List ℕ) : ∀ v ∈ lits l, NoRd a v := by
  intro v hv; simp [lits] at hv; obtain ⟨x, _, rfl⟩ := hv; simp [NoRd]

theorem NoRd_ncEx : NoRd Out (ncEx n u) := by
  simp only [ncEx]
  refine NoRd_famChain n _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [NoRd, NoRd_sgcEx]

theorem NoRd_nEx (cv : ℕ) : NoRd Out (nEx n cv) := by
  simp only [nEx]
  refine NoRd_famChain n _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [NoRd, NoRd_sgcEx]

theorem NoRd_lEx (cv tv : ℕ) : NoRd Out (lEx n cv tv) := by
  simp only [lEx]
  refine NoRd_famChain n _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact NoRd_tabX _ (by simp [NoRd]) _ _ (NoRd_lits _)

theorem NoRd_rEx (cv tv : ℕ) : NoRd Out (rEx n cv tv) := by
  simp only [rEx]
  refine NoRd_famChain n _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact NoRd_tabX _ (by simp [NoRd]) _ _ (NoRd_lits _)

theorem NoRd_negEx (cv tv : ℕ) : NoRd Out (negEx n cv tv) := by
  have hv : NoRd Out (Ex.var tv) := trivial
  have key : ∀ l : List ℕ, NoRd Out (tabX (Ex.var tv) 0 (lits l)) := fun l => NoRd_tabX _ hv _ 0 (NoRd_lits _)
  simp only [negEx]
  exact NoRd_famChain n _ (key _) (key _) (key _) (key _) (key _) (key _) (key _) (key _) (key _) (key _) (key _)
    (NoRd_ifLt (NoRd_sgcEx n cv) trivial (key _) (key _))

theorem NoRd_epsEx (cv tv : ℕ) : NoRd Out (epsEx n cv tv u) := by
  simp [epsEx, NoRd, NoRd_negEx, pow2, pw2, NoRd_MEx]

theorem NoRd_phiEx (cv ev : ℕ) : NoRd Out (phiEx n cv ev) := by
  have hv : NoRd Out (Ex.var ev) := trivial
  have bnd : NoRd Out (bndE n cv) := by simp [bndE, NoRd]
  have key : ∀ (l : List Ex), (∀ v ∈ l, NoRd Out v) → NoRd Out (tabX (Ex.var ev) 0 l) := fun l hl => NoRd_tabX _ hv l 0 hl
  simp only [phiEx]
  refine NoRd_famChain n _ (key _ ?_) (key _ ?_) (key _ ?_) (key _ ?_) (key _ ?_) (key _ ?_) (key _ ?_) (key _ ?_)
    (key _ ?_) (key _ ?_) (key _ ?_) (NoRd_ifLt (NoRd_sgcEx n cv) trivial (key _ ?_) (key _ ?_)) <;>
    simp [NoRd, aff, bnd]

end

section real
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) {u : ℕ} (hu : B ≤ u)

/-- **`InstNoRd` of the real instance**: none of the instance expressions reads array `3` or an array `>= 12`. -/
theorem instNoRd_real : InstNoRd Out (instEx (n := n) (ℓ := ℓ) (π := π) u hB hR) :=
  ⟨trivial, trivial, NoRd_AEx u, NoRd_hEx u, NoRd_pbEx u, NoRd_bEx u, NoRd_ncEx n u, NoRd_MEx u⟩

theorem NoRd_phiExInst : NoRd Out (phiExInst (n := n) (ℓ := ℓ) (π := π) u hB hR).phiE := NoRd_phiEx n _ _

/-- `NoRd_dispatchC` of L84 for `kindsC'` (the weakened `hne`) -/
theorem NoRd_dispatchC' {m : ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
    [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
    {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop}
    {L : Lay ι ιc} {I : InstEx L N0 w B Ctx A u} {Ph : PhiEx L φ B Ctx A u}
    (hI : InstNoRd Out I) (hP : NoRd Out Ph.phiE)
    (hM1 : ∀ c : Fin K, 1 ≤ (NP N0 w c).M) (hne : ∀ c : Fin K, 0 < L.nc c ∨ (F c).n = 0) (hw1 : ∀ c, 1 ≤ w c)
    (nE epsE lE rE : Ex)
    (hnFV : Ex.FV (· < u + 42) nE) (hεFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) epsE)
    (hlFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) lE) (hrFV : Ex.FV (fun y => y < u + 42 ∨ y = u + 43) rE)
    (hn : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → Ex.eval σ' A nE = (F c).n)
    (heps : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Rp (Function.update σ' (u + 43) t) A epsE (((F c).ε ⟨t, ht⟩ : ℤ) : (NP N0 w c).Rg))
    (hl : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A lE = (L.ecc c ((F c).l ⟨t, ht⟩) : ℕ))
    (hr : ∀ σ₀, Ctx σ₀ → ∀ (σ' : ℕ → ℕ), Ag B σ₀ σ' → ∀ (c : Fin K), σ' (u + 15) = c.val → ∀ t (ht : t < (F c).n),
      Ex.eval (Function.update σ' (u + 43) t) A rE = (L.ecc c ((F c).r ⟨t, ht⟩) : ℕ))
    (hnN : NoRd Out nE) (heN : NoRd Out epsE) (hlN : NoRd Out lE) (hrN : NoRd Out rE)
    (Sw : SrcWt (w := w) (pex0 (F := F) (ok := ok) (m := m) I Ph hu)) (hs : NoRd Out Sw.srcE) :
    NoRd Out (outEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu)
        (kindsC' (F := F) (ok := ok) (m := m) I Ph hu hM1 hne hw1 nE epsE lE rE hnFV hεFV hlFV hrFV hn heps hl hr)) ∧
      NoRd Out (wtEx I (pex0 (F := F) (ok := ok) (m := m) I Ph hu) Sw) := by
  have hX := XNoRd_pex0 (F := F) (ok := ok) (m := m) (hu := hu) hI hP
  refine ⟨NoRd_outEx hI hX _ ?_ ?_ ?_, NoRd_wtEx hI hX Sw hs⟩
  · exact NoRd_guardE (NoRd_faKindEC (NoRd_phiWrap hP))
  · exact NoRd_guardE (NoRd_midKindEC hnN heN hlN hrN)
  · exact NoRd_ibOutIC

/-- **the real dispatch reads neither array 3 nor an array >= 12** (the source-weight expression `Sw.srcE` being the only remaining hypothesis;
for L81's `srcE u (badE u n)` it is L84's `NoRd_srcE`). -/
theorem NoRd_dispatchReal' (m : ℕ) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu))
    (hs : NoRd Out Sw.srcE) :
    NoRd Out (outEx (instEx (n := n) (ℓ := ℓ) (π := π) u hB hR)
        (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu)
        (kindsReal' (ℓ := ℓ) (π := π) hB hR hu m ok)) ∧
      NoRd Out (wtEx (instEx (n := n) (ℓ := ℓ) (π := π) u hB hR)
        (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) u hB hR) (phiExInst u hB hR) hu) Sw) :=
  NoRd_dispatchC' hu (instNoRd_real hB hR) (NoRd_phiExInst hB hR) (fun c => M_pos c) (hne_real (sgR n ℓ π))
    (fun c => wP_pos _) (nEx n (u + 15)) (epsEx n (u + 15) (u + 43) u) (lEx n (u + 15) (u + 43)) (rEx n (u + 15) (u + 43))
    (fv_nEx _ n (u + 15) (by omega) (by omega))
    (fv_epsEx n (u + 15) (u + 43) u _ (by omega) (by omega) (by omega))
    (fv_lEx _ n (u + 15) (u + 43) (by omega) (by omega)) (fv_rEx _ n (u + 15) (u + 43) (by omega) (by omega))
    (hn_real hB hR hu) (heps_real hB hR hu) (hl_real hB hR hu) (hr_real hB hR hu)
    (NoRd_nEx n _) (NoRd_epsEx n _ _ u) (NoRd_lEx n _ _) (NoRd_rEx n _ _) Sw hs

end real
end ECDLP.L90
end
