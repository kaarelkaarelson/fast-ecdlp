import ECDLP.L64_Edge
import ECDLP.L85_A_Shape

/-!
# L69 / Bdd: value bounds (Rudich's `NBdd`) for the network expressions built from gate-level expressions

`PExB X V`: the value bounds of the seven gate-level expressions of `PEx` (every value met in their evaluation is
`≤ V`), with the numeric facts that make the derived expressions (`szEx`, `WEx`, `cEx`, `mMsg`, `msgTest`) bounded:
each gate's setting count `≤ V`, each edge width has `2^c ≤ V`, node widths `+1 ≤ V`.  `nbdd_netEx`: then
`NBdd V B σ₀ A (NVars.std u) (netEx X) g` (the analogue of Rudich's `mul_nbdd`).
-/
noncomputable section
namespace ECDLP.L85A
set_option linter.unusedSectionVars false
variable {DB : ℕ} [Fact (100 ≤ DB)]
open Factoring.Aux Finset Ex SB ECDLP.L56 ECDLP.L64 UCost85

section
theorem nfN_pos' {m g : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PForced (ZMod m) ι) (e : ι ≃ Fin g)
    [∀ i, Nonempty (P.Free i)] (a : ℕ) : 0 < nfN P e a := by
  unfold nfN; split_ifs
  · exact Fintype.card_pos
  · exact Nat.one_pos

theorem pp_le_sN {m g : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PForced (ZMod m) ι) (e : ι ≃ Fin g)
    [∀ i, Nonempty (P.Free i)] (a : ℕ) : pp (nA P e a) g ≤ sN P e a :=
  Nat.le_mul_of_pos_right _ (nfN_pos' P e a)

theorem le_pp_of_pos {f : ℕ → ℕ} (hf : ∀ i, 0 < f i) : ∀ {n j : ℕ}, j < n → f j ≤ pp f n
  | 0, j, h => absurd h (by omega)
  | n + 1, j, h => by
      simp only [pp]
      rcases Nat.lt_or_ge j n with h' | h'
      · exact le_trans (le_pp_of_pos hf h') (Nat.le_mul_of_pos_right _ (hf n))
      · obtain rfl : j = n := by omega
        exact Nat.le_mul_of_pos_left _ (pp_pos fun i _ => hf i)


end

section
variable {m B g : ℕ} {σ₀ : ℕ → ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PForced (ZMod m) ι} {E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))}
  {EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i))} {e : ι ≃ Fin g} [hF : ∀ i, Nonempty (P.Free i)] {u : ℕ}
  (X : PEx (B := B) (Ctx := Ctx) (A := A) P E EF e u)

/-- **The value bounds of the gate-level expressions** (and the numeric facts), for the bound `V`. -/
structure PExB (V : ℕ) : Prop where
  hV : 8 ≤ V
  hgV : g ≤ V
  hsN : ∀ a : ℕ, sN P e a ≤ V
  hcV : ∀ a b : Fin g, 2 ^ (toGNetE P E).c (e.symm a) (e.symm b) ≤ V
  hwV : ∀ i, P.w i + 1 ≤ V
  bg : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Bdd V σ A X.gE
  bnf : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nfE
  bnm : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.nmE
  bw : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ k : Fin g, σ (u + 4) = k → Bdd V σ A X.wE
  bpar : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ p c : Fin g, σ (u + 5) = p → σ (u + 6) = c → Bdd V σ A X.parE
  bout : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, σ (u + 5) = a → σ (u + 6) = b → σ (u + 7) ≤ V →
    Bdd V σ A X.outE ∧ eval σ A X.outE + 1 ≤ V
  bwt : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ a : Fin g, σ (u + 4) = a → σ (u + 7) ≤ V → Bdd V σ A X.wtE

variable {V : ℕ} (H : PExB X V) {σ : ℕ → ℕ}
variable (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include H hu hC hσ

theorem slotV {t : ℕ} {k : Fin g} (hk : σ t = k) : σ t ≤ V := by rw [hk]; exact le_trans k.2.le H.hgV

theorem bdd_par2 {p c : ℕ} (hc : c ≠ u + 5) {pk ck : Fin g} (hp : σ p = pk) (hcv : σ c = ck) :
    Bdd V σ A (par2 X p c) := by
  have hcv' : Function.update σ (u + 5) (σ p) c = ck := by rw [Function.update_of_ne hc]; exact hcv
  refine ⟨slotV X H hu hC hσ hp, ?_, ?_⟩
  · show Function.update σ (u + 5) (σ p) c ≤ V
    rw [hcv']; exact le_trans ck.2.le H.hgV
  · exact H.bpar σ₀ hC _ ((hσ.upd (by omega) _).upd (by omega) _) pk ck (by simp [Ex.eval, hp])
      (by simp [Ex.eval, hcv'])

theorem bdd_un1 {t : ℕ} {k : Fin g} (hk : σ t = k) {body : Ex}
    (hb : Bdd V (Function.update σ (u + 4) (σ t)) A body) : Bdd V σ A (un1 X t body) :=
  ⟨slotV X H hu hC hσ hk, hb⟩

theorem bdd_nf {t : ℕ} {k : Fin g} (hk : σ t = k) : Bdd V σ A (un1 X t X.nfE) :=
  bdd_un1 X H hu hC hσ hk (H.bnf σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk]))

theorem bdd_nm {t : ℕ} {k : Fin g} (hk : σ t = k) : Bdd V σ A (un1 X t X.nmE) :=
  bdd_un1 X H hu hC hσ hk (H.bnm σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk]))

theorem bdd_w {t : ℕ} {k : Fin g} (hk : σ t = k) : Bdd V σ A (un1 X t X.wE) :=
  bdd_un1 X H hu hC hσ hk (H.bw σ₀ hC _ (hσ.upd (by omega) _) k (by simp [hk]))

theorem bdd_nAE {fr : ℕ} (hfr : fr < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ (u + 8) = k) :
    Bdd V σ A (nAE X fr) :=
  B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := u + 8) (c := fr) (by omega) hk ha)
    (fun _ => bdd_nm X H hu hC hσ (t := u + 8) hk) (fun _ => B_lit (by have := H.hV; omega))

theorem pp_nA_le {fr : ℕ} (hfr : fr < u + 4) {a : Fin g} (ha : σ fr = a) {j : ℕ} (hj : j ≤ g) :
    pp (fun i => eval (Function.update σ (u + 8) i) A (nAE X fr)) j ≤ V := by
  have h1 : pp (fun i => eval (Function.update σ (u + 8) i) A (nAE X fr)) j = pp (nA P e a) j := by
    refine pp_congr fun i hi => ?_
    have hig : i < g := lt_of_lt_of_le hi hj
    exact eval_nAE X hu hC (hσ.upd (show B ≤ u + 8 by omega) i) hfr (a := a) (k := ⟨i, hig⟩)
      (by simp [Function.update_apply, ha]; omega) (by simp)
  rw [h1]
  exact le_trans (pp_mono_le (fun i => nA_pos P e a i) hj) (le_trans (pp_le_sN P e a) (by
    have := H.hsN a.1; simpa using this))

theorem bdd_ppE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a) (hk : σ tt = k) :
    Bdd V σ A (ppE X fr tt) := by
  refine B_nprodV (B_var (slotV X H hu hC hσ hk)) (fun j hj => ?_) (fun j hj => ?_)
  · have hjk : j < g := lt_trans (by simpa [Ex.eval, hk] using hj) k.2
    exact bdd_nAE X H hu (hC) (hσ.upd (show B ≤ u + 8 by omega) j) hfr (a := a) (k := ⟨j, hjk⟩)
      (by simp [Function.update_apply, ha]; omega) (by simp)
  · have : j ≤ k := by simpa [Ex.eval, hk] using hj
    exact pp_nA_le X H hu hC hσ hfr ha (le_trans this k.2.le)

theorem bdd_szEx {a : Fin g} (ha : σ u = a) : Bdd V σ A (szEx X) := by
  have hgE := X.hg σ₀ hC σ hσ
  refine ⟨B_nprodV (H.bg σ₀ hC σ hσ) (fun j hj => ?_) (fun j hj => ?_), bdd_nf X H hu hC hσ ha, ?_⟩
  · have hjg : j < g := by rw [hgE] at hj; exact hj
    exact bdd_nAE X H hu hC (hσ.upd (show B ≤ u + 8 by omega) j) (fr := u) (by omega) (a := a) (k := ⟨j, hjg⟩)
      (by simp [Function.update_apply, ha]) (by simp)
  · rw [hgE] at hj
    exact pp_nA_le X H hu hC hσ (fr := u) (by omega) ha hj
  · have := eval_szEx X hu hC hσ ha
    simp only [szEx, Ex.eval] at this ⊢
    rw [this]; exact H.hsN a.1

theorem bdd_digE {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) (hz : σ (u + 2) ≤ V) : Bdd V σ A (digE X fr tt) :=
  B_mod (B_div (B_div (B_var hz) (bdd_nf X H hu hC hσ ha)) (bdd_ppE X H hu hC hσ hfr htt ha hk))
    (bdd_nm X H hu hC hσ hk)

theorem digE_lt_nm {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a k : Fin g} (ha : σ fr = a)
    (hk : σ tt = k) : eval σ A (digE X fr tt) < Fintype.card (P.Msg (e.symm k)) := by
  simp only [digE, Ex.eval]
  rw [eval_nm X hu hC hσ hk]
  exact Nat.mod_lt _ (Fintype.card_pos)

theorem bdd_mMsg {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a b : Fin g} (ha : σ fr = a)
    (hb : σ tt = b) (hz : σ (u + 2) ≤ V) : Bdd V σ A (mMsg X fr tt) := by
  have hne : fr ≠ tt ∨ True := Or.inr trivial
  refine B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := tt) (c := fr) (by omega) hb ha) ?_ ?_
  · intro h1
    have h1' : e.symm b ∈ P.pa (e.symm a) := by
      by_contra hn
      rw [eval_par2 X hu hC hσ (p := tt) (c := fr) (by omega) hb ha, if_neg hn] at h1
      simp [Ex.eval] at h1
    refine B_add (bdd_digE X H hu hC hσ hfr htt ha hb hz) (B_lit (by have := H.hV; omega)) ?_
    have h2 := digE_lt_nm X H hu hC hσ hfr htt ha hb
    rw [← nA_par P e h1'] at h2
    have h3 : nA P e a b ≤ pp (nA P e a) g := le_pp_of_pos (fun i => nA_pos P e a i) b.2
    have h4 := H.hsN a.1
    have h5 := pp_le_sN P e a.1
    simp only [Ex.eval]
    omega
  · intro h1
    refine B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := fr) (c := tt) (by omega) ha hb) ?_
      (fun _ => B_lit (by have := H.hV; omega))
    intro h2
    have e1 : (Function.update σ (u + 5) (σ fr)) tt = σ tt := Function.update_of_ne (by omega) _ _
    have e2 : (Function.update (Function.update σ (u + 5) (σ fr)) (u + 6) (σ tt)) (u + 2) = σ (u + 2) := by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hB := H.bout σ₀ hC _ (((hσ.upd (show B ≤ u + 5 by omega) (σ fr)).upd (show B ≤ u + 6 by omega) (σ tt)).upd
        (show B ≤ u + 7 by omega) (σ (u + 2))) a b (by simp [Function.update_apply, ha])
      (by simp [Function.update_apply, hb]) (by simp [Function.update_apply]; exact hz)
    have hfa : σ fr ≤ V := by rw [ha]; exact le_trans a.2.le H.hgV
    have hfb : σ tt ≤ V := by rw [hb]; exact le_trans b.2.le H.hgV
    refine B_add ⟨B_var hfa, B_var ?_, B_var ?_, ?_⟩ (B_lit (by have := H.hV; omega)) ?_
    · show (Function.update σ (u + 5) (σ fr)) tt ≤ V
      rw [e1]; exact hfb
    · show (Function.update (Function.update σ (u + 5) (σ fr)) (u + 6) ((Function.update σ (u + 5) (σ fr)) tt)) (u + 2) ≤ V
      rw [e1, e2]; exact hz
    · show Bdd V (Function.update (Function.update (Function.update σ (u + 5) (σ fr)) (u + 6)
        ((Function.update σ (u + 5) (σ fr)) tt)) (u + 7) ((Function.update (Function.update σ (u + 5) (σ fr)) (u + 6)
        ((Function.update σ (u + 5) (σ fr)) tt)) (u + 2))) A X.outE
      rw [e1, e2]; exact hB.1
    · have := hB.2
      simp only [Ex.eval]
      show eval (Function.update (Function.update (Function.update σ (u + 5) (σ fr)) (u + 6)
        ((Function.update σ (u + 5) (σ fr)) tt)) (u + 7) ((Function.update (Function.update σ (u + 5) (σ fr)) (u + 6)
        ((Function.update σ (u + 5) (σ fr)) tt)) (u + 2))) A X.outE + 1 ≤ V
      rw [e1, e2]; exact this

theorem bdd_WEx {a : Fin g} (ha : σ u = a) (hz : σ (u + 2) ≤ V) : Bdd V σ A (WEx X) := by
  have e2 : (Function.update σ (u + 4) (σ u)) (u + 2) = σ (u + 2) := Function.update_of_ne (by omega) _ _
  refine ⟨B_var (by rw [ha]; exact le_trans a.2.le H.hgV), B_var ?_, ?_⟩
  · show (Function.update σ (u + 4) (σ u)) (u + 2) ≤ V
    rw [e2]; exact hz
  · show Bdd V (Function.update (Function.update σ (u + 4) (σ u)) (u + 7)
      ((Function.update σ (u + 4) (σ u)) (u + 2))) A X.wtE
    rw [e2]
    exact H.bwt σ₀ hC _ ((hσ.upd (show B ≤ u + 4 by omega) _).upd (show B ≤ u + 7 by omega) _) a
      (by simp [Function.update_apply, ha]) (by simp [Function.update_apply]; exact hz)

theorem bdd_cEx {a b : Fin g} (ha : σ u = a) (hb : σ (u + 1) = b) : Bdd V σ A (cEx X) := by
  refine B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := u + 1) (c := u) (by omega) hb ha) ?_ ?_
  · intro _
    refine B_add (bdd_w X H hu hC hσ (t := u + 1) hb) (B_lit (by have := H.hV; omega)) ?_
    simp only [Ex.eval]
    rw [eval_w X hu hC hσ hb]
    exact H.hwV _
  · intro _
    refine B_ifLt' (B_lit (Nat.zero_le V)) (bdd_par2 X H hu hC hσ (p := u) (c := u + 1) (by omega) ha hb) ?_
      (fun _ => B_lit (by have := H.hV; omega))
    intro _
    refine B_add (bdd_w X H hu hC hσ (t := u) ha) (B_lit (by have := H.hV; omega)) ?_
    simp only [Ex.eval]
    rw [eval_w X hu hC hσ ha]
    exact H.hwV _

theorem bdd_msgTest {fr tt : ℕ} (hfr : fr < u + 4) (htt : tt < u + 4) {a b : Fin g} (ha : σ u = a)
    (hb : σ (u + 1) = b) (hz : σ (u + 2) ≤ V)
    (hq : σ (u + 3) ≤ V) (hmm : Bdd V σ A (mMsg X fr tt)) :
    Bdd V σ A (msgTest (mMsg X fr tt) (cEx X) (u + 3) (u + 9)) := by
  have hc := bdd_cEx X H hu hC hσ ha hb
  refine B_ifEq' hmm (B_mod (B_var hq) (B_pow2 hc (by have := H.hV; omega) ?_))
    (fun _ => B_lit (by have := H.hV; omega)) (fun _ => B_lit (by have := H.hV; omega))
  rw [eval_cEx X hu hC hσ ha hb]
  exact H.hcV a b

/-- **Value bounds of the network expressions of a forced gate network** (analogue of Rudich's `mul_nbdd`). -/
theorem nbdd_netEx : NBdd V B σ₀ A (NVars.std u) (netEx X) g where
  sz σ hσ ha := bdd_szEx X H hu hC hσ (a := ⟨σ u, ha⟩) rfl
  W σ hσ ha hz := bdd_WEx X H hu hC hσ (a := ⟨σ u, ha⟩) rfl hz
  c σ hσ hab hb := bdd_cEx X H hu hC hσ (a := ⟨σ u, lt_trans hab hb⟩) (b := ⟨σ (u + 1), hb⟩) rfl rfl
  l σ hσ hab hb hz hq := bdd_msgTest X H hu hC hσ (fr := u) (tt := u + 1) (by omega) (by omega)
    (a := ⟨σ u, lt_trans hab hb⟩) (b := ⟨σ (u + 1), hb⟩) rfl rfl hz hq
    (bdd_mMsg X H hu hC hσ (by omega) (by omega) (a := ⟨σ u, lt_trans hab hb⟩) (b := ⟨σ (u + 1), hb⟩) rfl rfl hz)
  r σ hσ hab hb hz hq := bdd_msgTest X H hu hC hσ (fr := u + 1) (tt := u) (by omega) (by omega)
    (a := ⟨σ u, lt_trans hab hb⟩) (b := ⟨σ (u + 1), hb⟩) rfl rfl hz hq
    (bdd_mMsg X H hu hC hσ (by omega) (by omega) (a := ⟨σ (u + 1), hb⟩) (b := ⟨σ u, lt_trans hab hb⟩) rfl rfl hz)

end
end ECDLP.L85A
end
