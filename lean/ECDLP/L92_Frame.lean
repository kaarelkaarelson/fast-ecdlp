import ECDLP.L80_Final
import ECDLP.L88_Eng

/-!
# L92 / Frame: `FrameIn'` (L80's `FrameIn` plus `array 1, cell 0 = 0`), the frame writer `frameW'` that establishes it,
and the restated oracle (`oraC'`, `oracle_spec'`) and engine-value predicate (`EngVal'`).

L88 found: the counting command's divisor-1 correction is `[A 1 0 != 0 and a = 0]`, so `EngVal` for the real engine needs
cell `0` of array `1` to be `0`.  `frameW' S = frameW S ; A[S+1][0] := 0` (one `wr`; the cell `0` is not read by any `numCells _ 1 _`).
-/
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L71 ECDLP.L76 ECDLP.L77 ECDLP.L60 ECDLP.L80 Factoring.Aux Factoring.Aux.Copied
  Factoring.Aux.Copied.PLib Computability

/-- L80's `FrameIn` plus cell `0` of array `1` is `0` -/
def FrameIn' (r : ℕ) (i : EdgeInp) (s : St) : Prop := FrameIn r i s ∧ s.ar 1 0 = 0

/-- the frame writer with the extra zeroing of `A[S+1][0]` (scalar `S+2` is `0` at that point) -/
def frameW' (S : ℕ) : Cmd := .seq (frameW S) (.wr (S + 1) (S + 2) 0 (S + 2))

theorem frameW'_rng (S : ℕ) (hS : 1400 ≤ S) : Rng 10 (S + 2) 3 (S + 11) (frameW' S) :=
  Rng.seq (frameW_rng S hS) (Rng.wr (by omega))

theorem numCells_update_zero (f : ℕ → ℕ) (v n : ℕ) : numCells (Function.update f 0 v) 1 n = numCells f 1 n := by
  unfold numCells
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Function.update_of_ne (by omega)]

theorem reads72n_update1 {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ} (v : ℕ)
    (h : Reads72n σ A p a b X xR yR π ℓ bW) :
    Reads72n σ (Function.update A 1 (Function.update (A 1) 0 v)) p a b X xR yR π ℓ bW := by
  have e : ∀ c, c ≠ 1 → Function.update A 1 (Function.update (A 1) 0 v) c = A c := fun c hc => Function.update_of_ne hc _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by omega)]; exact h.hp
  · rw [Function.update_self, numCells_update_zero]; exact h.ha
  · rw [e 2 (by omega)]; exact h.hb
  · rw [e 4 (by omega)]; exact h.hxR
  · rw [e 5 (by omega)]; exact h.hyR
  · rw [e 7 (by omega)]; exact h.hOp
  · rw [e 8 (by omega)]; exact h.hX
  · rw [e 9 (by omega)]; exact h.hlen
  · rw [e 10 (by omega)]; exact h.hl
  · rw [e 11 (by omega)]; exact h.hbW
  · intro q hq; rw [e 6 (by omega)]; exact h.hpi q hq

/-- the run of `frameW' S`: the run of `frameW S` followed by the write of cell `0` of array `S+1` -/
theorem run_frameW'_state (S : ℕ) (s : St) :
    Cmd.run (frameW' S) s = (((Cmd.run (frameW S) s).1).setAr (S + 1) ((Cmd.run (frameW S) s).1.sc (S + 2) + 0)
      ((Cmd.run (frameW S) s).1.sc (S + 2)), (Cmd.run (frameW S) s).2 + 1 + 1) := by
  simp only [frameW', Cmd.run_seq, Cmd.run_wr]

theorem unshift_frame_wr (S : ℕ) (q : St) (hs2 : q.sc (S + 2) = 0) :
    unshift S (q.setAr (S + 1) (q.sc (S + 2) + 0) (q.sc (S + 2))) = ⟨(unshift S q).sc, Function.update (unshift S q).ar 1
      (Function.update ((unshift S q).ar 1) 0 0)⟩ := by
  simp only [hs2, add_zero]
  rw [unshift_setAr]
  apply St.ext
  · rfl
  · funext c
    simp only [St.setAr, St.putAr, unshift_ar]

set_option maxHeartbeats 4000000 in
theorem frameW'_run (S : ℕ) (hS : 1400 ≤ S) (s : St) (W p a b x y X : ℕ) (τ : List Bool)
    (hW : s.sc 710 = W) (h30 : V (s.ar 30) W = p) (h21 : V (s.ar 21) W = a) (h22 : V (s.ar 22) W = b)
    (h23 : V (s.ar 23) W = x) (h24 : V (s.ar 24) W = y) (h47 : V (s.ar 47) W = X) (h56 : V (s.ar 56) W = 2 * (p * p))
    (h782 : s.sc 782 = Nat.size X) (hsc2 : s.sc 2 = τ.length) (hτ : ∀ j, j < τ.length → s.ar 1 j = ECDLP.L61.bitN (τ.getD j false))
    (h2 : 2 ≤ Nat.size p) (hab : a ≠ 0 ∨ b ≠ 0) (hap : a < p) (hbp : b < p) (hxp : x < p) (hyp : y < p) (hXp : X ≤ p) :
    let r := Cmd.run (frameW' S) s
    Reads72n (unshift S r.1).sc (unshift S r.1).ar p a b X x y τ (Nat.size X) (ECDLP.L72.bWof (Nat.size p)) ∧
    (unshift S r.1).sc 0 = Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + τ.length + 1 ∧
    (unshift S r.1).sc 2 = 0 ∧ (unshift S r.1).ar 1 0 = 0 ∧ r.2 ≤ 10000 * (W + τ.length + 2) ^ 2 + 2 := by
  intro r
  obtain ⟨f1, f2, f3, f4⟩ := frameW_run S hS s W p a b x y X τ hW h30 h21 h22 h23 h24 h47 h56 h782 hsc2 hτ h2 hab hap hbp hxp hyp hXp
  generalize hq : Cmd.run (frameW S) s = q at f1 f2 f3 f4
  have hr : r = (q.1.setAr (S + 1) (q.1.sc (S + 2) + 0) (q.1.sc (S + 2)), q.2 + 1 + 1) := by
    have := run_frameW'_state S s
    rw [hq] at this; exact this
  have hs2 : q.1.sc (S + 2) = 0 := f3
  have hun : unshift S r.1 = ⟨(unshift S q.1).sc, Function.update (unshift S q.1).ar 1
      (Function.update ((unshift S q.1).ar 1) 0 0)⟩ := by
    rw [hr]; exact unshift_frame_wr S q.1 hs2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hun]; exact reads72n_update1 0 f1
  · rw [hun]; exact f2
  · rw [hun]; exact f3
  · rw [hun]; simp
  · rw [hr]; simp only; omega

set_option maxHeartbeats 4000000 in
theorem pre_frame' (r S : ℕ) (hS : 1400 ≤ S) (x : Inst) (τ : List Bool) (st : St) (hconf : Conf x τ st)
    (hgood : Good (r + 1) x τ) :
    let s2 := Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st
    FrameIn' r (redInp x τ) (unshift S s2.1) ∧ s2.2 ≤ PB (r + 1) (encB x).length + 2 ∧
    s2.1.ar 0 = st.ar 0 ∧ s2.1.ar 1 = st.ar 1 := by
  intro s2
  obtain ⟨hF, hcost, h0, h1⟩ := pre_frame r S hS x τ st hconf hgood
  generalize hX : Cmd.run (checkC (r + 1)) st = X
  generalize hY : Cmd.run (frameW S) X.1 = Y
  have hs2 : Cmd.run (.seq (checkC (r + 1)) (frameW S)) st = (Y.1, X.2 + Y.2 + 1) := by
    simp only [Cmd.run_seq, hX, hY]
  rw [hs2] at hF hcost h0 h1
  simp only at hF hcost h0 h1
  have hs2' : Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st =
      (Y.1.setAr (S + 1) (Y.1.sc (S + 2) + 0) (Y.1.sc (S + 2)), X.2 + (Y.2 + 1 + 1) + 1) := by
    have := run_frameW'_state S X.1
    simp only [Cmd.run_seq, hX, this, hY]
  have hz : Y.1.sc (S + 2) = 0 := by
    have := hF.2.1
    exact this
  have hun := unshift_frame_wr S Y.1 hz
  change FrameIn' r (redInp x τ) (unshift S (Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st).1) ∧
    (Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st).2 ≤ PB (r + 1) (encB x).length + 2 ∧
    (Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st).1.ar 0 = st.ar 0 ∧
    (Cmd.run (.seq (checkC (r + 1)) (frameW' S)) st).1.ar 1 = st.ar 1
  rw [hs2']
  rw [hun]
  refine ⟨⟨⟨hF.1, hF.2.1, reads72n_update1 0 hF.2.2⟩, by simp⟩, by omega, ?_, ?_⟩
  · rw [← h0]; simp [St.setAr, St.putAr, Function.update_of_ne (show (0 : ℕ) ≠ S + 1 by omega)]
  · rw [← h1]; simp [St.setAr, St.putAr, Function.update_of_ne (show (1 : ℕ) ≠ S + 1 by omega)]

end ECDLP.L92
