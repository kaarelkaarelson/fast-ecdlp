import ECDLP.L104_Eng

/-!
# L104 / Engine: `EngVal'` and `EngCostF` for the real engine from the frame-restricted core `EdgeCoreF`
-/
noncomputable section
namespace ECDLP.L104
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L59 ECDLP.L64
  ECDLP.L44 ECDLP.L51 ECDLP.L65 ECDLP.L70 Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L80 ECDLP.L84 ECDLP.L85B ECDLP.L88 ECDLP.L61 ECDLP
  ECDLP.L93 ECDLP.L92 ECDLP.L72 ECDLP.L60 Computability

/-- value link of the network of a frame memory with `len >= T1 r` (L88 `EdgeNetValue` for `EdgeCoreF`) -/
def EdgeNetValueF (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE) : Prop :=
  ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s → ∀ m, 1 < m →
    (((C.D m (redInp x τ).len 0 s.ar).inner.value : ZMod m)) = ((Zc (r + 1) x τ : ℕ) : ZMod m)

theorem edgeNetValueF_of_core (r : ℕ) (hr : 1 ≤ r) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} {E : NEx} {gE btE : Ex}
    (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE) (H : RealRep r E gE)
    (hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      P (redInp x τ).len s.ar) :
    EdgeNetValueF r C := by
  classical
  intro x τ hG hT s hF m hm
  have hPs := hPfr x τ hG hT s hF
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  set n := (redInp (p, a, b, xR, yR, π) τ).len with hn
  have hctx := ctx0_ok m n 0
  obtain ⟨K, e, g, eg, Em, EF, hrepR, hgR⟩ := H p a b xR yR π τ hG s hF m hm _ hctx
  have hrepC := (C.fields m n 0 s.ar hPs).rep _ hm (Nat.zero_le _) hctx
  have hgC := ((C.fields m n 0 s.ar hPs).clh _ hm (Nat.zero_le _) hctx).hgE _ (Ag.refl _ _)
  have hgg : (C.D m n 0 s.ar).gI = g := by rw [← hgC, ← hgR _ (Ag.refl _ _)]
  have hpar := parOK_explicit (K := K) p (a % p) (b % p) (xR % p) (yR % p) r (hG.1.pos)
    (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) (Nat.mod_lt _ hG.1.pos) τ e
  obtain ⟨hb1, -, -, hS⟩ := hpar
  have hval := rNet_value r p (a % p) (b % p) (xR % p) (yR % p) τ e m hm eg Em hS hb1
  have hcnt := edgeCount_real_eq_Zc r hr p a b xR yR π τ hG e
  rw [hcnt] at hval
  rw [← hval]
  generalize C.D m n 0 s.ar = D at hrepC hgg ⊢
  obtain ⟨gI, inner, κ, wt⟩ := D
  simp only at hgg hrepC ⊢
  subst hgg
  exact value_eq_of_nrep (VOk.std (by norm_num)) hrepC hrepR


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem engVal'_longHF (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE)
    (hnet : EdgeNetValueF r C)
    (hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      P (redInp x τ).len s.ar) :
    EngValGe r (T1 r) (engCmd r E gE btE) := by
  have : Fact (100 ≤ 200) := ECDLP.L85.fact200
  intro x τ hg hT s hF'
  obtain ⟨hF, hA⟩ := hF'
  have h0 : s.sc 0 = (redInp x τ).len := hF.1
  have h2 : s.sc 2 = 0 := hF.2.1
  have hlen : 1 ≤ (redInp x τ).len := by unfold EdgeInp.len; omega
  have hkn : s.sc 2 < s.sc 0 := by omega
  have hD : s.ar 1 (s.sc 2) = 0 := by rw [h2]; exact hA
  have hcx : (if 1 / 2 ^ s.sc 2 = numCells (s.ar 1) (s.sc 2) (s.sc 0 - s.sc 2) then 1 else 0) = 0 := by
    rw [h2, h0]; exact c1_zero_of_cell0 _ _ hlen hA
  have hPs : P (s.sc 0) s.ar := by rw [h0]; exact hPfr x τ hg hT s hF
  have := ECDLP.L104B.uniCF_val' (ECDLP.L104A.topIfaceF_edgeH r hPc hPn C) (ECDLP.L104A.shapeDataF_edgeH r hPc hPn C) s hPs
    (cnt := Zc (r + 1) x τ) hkn hD hcx
    (by rw [h0]; exact zc_lt_len r x τ hg (le_trans (le_max_left _ _) hT))
    (fun m hm => by
      rw [h0, h2]
      exact hnet x τ hg hT s hF m hm)
  have e : engCmd r E gE btE = uniC (ECDLP.L85A.UP' (ECDLP.L85B.edgeL0v r) (ECDLP.L85B.searchMv E gE btE) (ECDLP.L85B.tabMv E gE btE)) := rfl
  rw [e, this]

theorem engCost_longHF (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE)
    (hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      P (redInp x τ).len s.ar) :
    ∃ c : ℕ, ∀ (V : ℕ) (x : Inst) (τ : List Bool), Good (r + 1) x τ → (edgeFamily r).UniReq V (redInp x τ).len →
      T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn' r (redInp x τ) s →
      (Cmd.run (engCmd r E gE btE) s).2 ≤ c * (V + 1) ^ (24 * 200 + 8) := by
  haveI : Fact (100 ≤ 200) := ECDLP.L85.fact200
  obtain ⟨c, h⟩ := ECDLP.L104A.uniCF_cost' (ECDLP.L104A.topIfaceF_edgeH r hPc hPn C) (famH_spec r)
  refine ⟨c, fun V x τ hg hU hT s hF => ?_⟩
  have h0 : s.sc 0 = (redInp x τ).len := hF.1.1
  have h2 : s.sc 2 = 0 := hF.1.2.1
  have hlen : 1 ≤ (redInp x τ).len := by unfold EdgeInp.len; omega
  have hn : 4 * Uc r ^ 4 ≤ (redInp x τ).len := le_trans (le_max_right _ _) hT
  refine h V s (by rw [h0]; exact hPfr x τ hg hT s hF.1) (by omega) ?_
  rw [h0]
  exact uniReq_famH hU (V_ge_Ub hn hU)

theorem engFullHF_val (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE)
    (hnet : EdgeNetValueF r C)
    (hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      P (redInp x τ).len s.ar) :
    EngVal' r (engFullH r E gE btE) :=
  engBr_val r (T1 r) _ (engVal'_longHF r hPc hPn C hnet hPfr)

theorem engFullHF_cost (r : ℕ) {P : ℕ → (ℕ → ℕ → ℕ) → Prop} (hPc : ∀ n A A', (∀ a, a ≠ 3 → A' a = A a) → P n A → P n A')
    (hPn : ∀ n A, P n A → P n (normA A)) {E : NEx} {gE btE : Ex} (C : ECDLP.L96.EdgeCoreF P 200 r E gE btE)
    (hPfr : ∀ (x : Inst) (τ : List Bool), Good (r + 1) x τ → T1 r ≤ (redInp x τ).len → ∀ s : St, FrameIn r (redInp x τ) s →
      P (redInp x τ).len s.ar) :
    EngCostF r (engFullH r E gE btE) := by
  obtain ⟨c, h⟩ := engCost_longHF r hPc hPn C hPfr
  exact engBrF_cost r (T1 r) _ c _ h

end ECDLP.L104
end
