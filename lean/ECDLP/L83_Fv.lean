import ECDLP.L83_Orc
import ECDLP.L79_Fv

/-!
# L83 / Fv: free-variable facts (`InstFV`, `phiE`, and the four mid oracles) and depths
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1600000
noncomputable section
namespace ECDLP.L83
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 Slot Cst

theorem fv_valE (s : ℕ → Prop) (h0 : s 0) (t : ℕ) : Ex.FV s (valE (.var 0) t 920 921) := by
  simp only [valE, nbitW, bitRd, Ex.FV]
  simp [h0]

theorem fv_sgE (s : ℕ → Prop) (h0 : s 0) (i : Ex) (hi : Ex.FV s i) : Ex.FV s (ECDLP.L76.sgE lay72 i) := by
  have hl : Ex.FV s lay72.ellE := fv_valE s h0 10
  have hp : Ex.FV s lay72.piE := fv_valE s h0 9
  simp only [ECDLP.L76.sgE, ECDLP.L76.pidx, Ex.FV]
  simp [hl, hp, hi]

theorem fv_tabX (s : ℕ → Prop) (e : Ex) (he : Ex.FV s e) : ∀ (vs : List Ex) (k : ℕ), (∀ y ∈ vs, Ex.FV s y) → Ex.FV s (tabX e k vs)
  | [], k, _ => by simp [tabX, Ex.FV]
  | y :: vs, k, h => by
    simp only [tabX, Ex.FV]
    exact ⟨he, trivial, h y (by simp), fv_tabX s e he vs (k + 1) (fun z hz => h z (by simp [hz]))⟩

theorem fv_lits (s : ℕ → Prop) (l : List ℕ) : ∀ y ∈ lits l, Ex.FV s y := by
  intro y hy; simp only [lits, List.mem_map] at hy; obtain ⟨k, -, rfl⟩ := hy; trivial

theorem fv_aff (s : ℕ → Prop) (cv k m : ℕ) (h : s cv) : Ex.FV s (aff cv k m) := by
  simp [aff, Ex.FV, h]

theorem fv_famChain (s : ℕ → Prop) (n cv : ℕ) (hc : s cv) {rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn : Ex}
    (h1 : Ex.FV s rg) (h2 : Ex.FV s ue) (h3 : Ex.FV s cu) (h4 : Ex.FV s s0x) (h5 : Ex.FV s s0y) (h6 : Ex.FV s srx)
    (h7 : Ex.FV s sry) (h8 : Ex.FV s e0) (h9 : Ex.FV s e1) (h10 : Ex.FV s e2) (h11 : Ex.FV s e3) (h12 : Ex.FV s sn) :
    Ex.FV s (famChain n cv rg ue cu s0x s0y srx sry e0 e1 e2 e3 sn) := by
  simp only [famChain, Ex.FV]
  simp [hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem fv_sgcEx (s : ℕ → Prop) (n cv : ℕ) (h0 : s 0) (hc : s cv) : Ex.FV s (sgcEx n cv) :=
  fv_sgE s h0 _ (by simp [Ex.FV, hc])

theorem fv_nEx (s : ℕ → Prop) (n cv : ℕ) (h0 : s 0) (hc : s cv) : Ex.FV s (nEx n cv) := by
  refine fv_famChain s n cv hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try trivial
  simp only [Ex.FV]; exact ⟨trivial, fv_sgcEx s n cv h0 hc, trivial, trivial⟩

theorem fv_tab (s : ℕ → Prop) (tv : ℕ) (ht : s tv) (l : List ℕ) : Ex.FV s (tabX (.var tv) 0 (lits l)) :=
  fv_tabX s (.var tv) ht _ _ (fv_lits s l)

theorem fv_lEx (s : ℕ → Prop) (n cv tv : ℕ) (hc : s cv) (ht : s tv) : Ex.FV s (lEx n cv tv) := by
  simp only [lEx]
  exact fv_famChain s n cv hc (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _)
    (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _)

theorem fv_rEx (s : ℕ → Prop) (n cv tv : ℕ) (hc : s cv) (ht : s tv) : Ex.FV s (rEx n cv tv) := by
  simp only [rEx]
  exact fv_famChain s n cv hc (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _)
    (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _)

theorem fv_negEx (s : ℕ → Prop) (n cv tv : ℕ) (h0 : s 0) (hc : s cv) (ht : s tv) : Ex.FV s (negEx n cv tv) := by
  simp only [negEx]
  refine fv_famChain s n cv hc (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _)
    (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) (fv_tab s tv ht _) ?_
  simp only [Ex.FV]
  exact ⟨fv_sgcEx s n cv h0 hc, trivial, fv_tab s tv ht _, fv_tab s tv ht _⟩

theorem fv_szE (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (szE u) := by
  have := fv_valE s h0 0
  simp only [szE, pE, nsum, pow2, Ex.FV]
  simp [h0, this]
theorem fv_log2E (u : ℕ) (s : ℕ → Prop) (x : Ex) (hx : Ex.FV s x) : Ex.FV s (log2E u x) := by
  have := Ex.FV_mono (s := s) (s' := fun y => s y ∨ y = u + 60) (fun y hy => Or.inl hy) x hx
  simp only [log2E, nsum, pow2, Ex.FV]
  simp [hx, this]
theorem fv_prel (u : ℕ) (s : ℕ → Prop) (h0 : s 0) (body : Ex)
    (hb : Ex.FV (fun y => (((((s y ∨ y = u + 63) ∨ y = u + 64) ∨ y = u + 65) ∨ y = u + 66) ∨ y = u + 67)) body) :
    Ex.FV s (prel u body) := by
  have h1 := fv_szE u s h0
  have h2 : Ex.FV (fun y => s y ∨ y = u + 63) (jm1E u) := by
    have := fv_log2E u (fun y => s y ∨ y = u + 63) (.var (u + 63)) (by simp [Ex.FV])
    simp only [jm1E, Ex.FV]
    simp [this]
  simp only [prel, Ex.FV]
  refine ⟨h1, h2, ?_, ?_, ?_, hb⟩
  all_goals simp [pow2, Ex.FV]

theorem fv_AEx (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (AEx u) :=
  fv_prel u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_hEx (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (hEx u) :=
  fv_prel u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_pbEx (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (pbEx u) :=
  fv_prel u s h0 _ (by simp [pow2, Ex.FV])
theorem fv_bEx (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (bEx u) :=
  fv_prel u s h0 _ (by simp [Ex.FV])
theorem fv_MEx (u : ℕ) (s : ℕ → Prop) (h0 : s 0) : Ex.FV s (MEx u) :=
  fv_prel u s h0 _ (by simp [Ex.FV])

theorem fv_ncEx (n u : ℕ) (s : ℕ → Prop) (h0 : s 0) (hc : s (u + 22)) : Ex.FV s (ncEx n u) := by
  simp only [ncEx]
  refine fv_famChain s n (u + 22) hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try trivial
  simp only [Ex.FV]; exact ⟨trivial, fv_sgcEx s n (u + 22) h0 hc, trivial, trivial⟩

theorem fv_epsEx (n cv tv u : ℕ) (s : ℕ → Prop) (h0 : s 0) (hc : s cv) (ht : s tv) : Ex.FV s (epsEx n cv tv u) := by
  have h1 := fv_negEx s n cv tv h0 hc ht
  have h2 := fv_MEx u s h0
  simp only [epsEx, pow2, Ex.FV]
  simp [h1, h2]

theorem fv_phiEx (n cv ev : ℕ) (s : ℕ → Prop) (h0 : s 0) (hc : s cv) (he : s ev) : Ex.FV s (phiEx n cv ev) := by
  have hb : Ex.FV s (bndE n cv) := by simp [bndE, Ex.FV, hc]
  have ha : ∀ k m, Ex.FV s (aff cv k m) := fun k m => fv_aff s cv k m hc
  have hl : ∀ k : ℕ, Ex.FV s (Ex.lit k) := fun k => trivial
  have hT : ∀ l : List Ex, (∀ y ∈ l, Ex.FV s y) → Ex.FV s (tabX (.var ev) 0 l) := fun l h => fv_tabX s (.var ev) he l 0 h
  have hall : ∀ l : List Ex, (∀ y ∈ l, (∃ k m, y = aff cv k m) ∨ (∃ k, y = Ex.lit k) ∨ y = bndE n cv) → Ex.FV s (tabX (.var ev) 0 l) := by
    intro l h
    refine hT l fun y hy => ?_
    rcases h y hy with ⟨k, m, rfl⟩ | ⟨k, rfl⟩ | rfl
    exacts [ha k m, hl k, hb]
  simp only [phiEx]
  refine fv_famChain s n cv hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (apply hall; intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
       rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact Or.inl ⟨_, _, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr rfl))
    | skip
  simp only [Ex.FV]
  exact ⟨fv_sgcEx s n cv h0 hc, trivial, hall _ (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl | rfl <;> first | exact Or.inl ⟨_, _, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩)),
    hall _ (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl | rfl <;> first | exact Or.inl ⟨_, _, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩))⟩

end ECDLP.L83
end
