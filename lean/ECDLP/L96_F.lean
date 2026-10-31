import ECDLP.L96_Hyp

/-!
# L96 / F: the FRAME-RESTRICTED core `EdgeCoreF` -- what the real network satisfies without any off-frame hypothesis

`EdgeCoreF P DB r E gE btE`: `EdgeCore` with the fields `hgI .. bnd` required only on memories `A` with `P n A` (and `hcong` for all).
`edgeCoreF_real2 r hr`: `EdgeCoreF (fun n A => Fr r n (zero3 A)) 200 r (Ereal2 r) (gEreal2 r) (btReal2 r)` -- NO `OffFrame`.
`frameIn_fr`: the memory of every `Good` `FrameIn` call state satisfies `Fr r len (zero3 s.ar)`.
So the real network satisfies every `EdgeCore` field at every actual engine call; the only missing step is to carry the invariant `P`
through L85's `ShapeData`/`TopIface` chain (see REPORT: `OffFrame` is NOT dischargeable, `bnd` fails on memories with huge `numCells`).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L96
open Finset Factoring.Aux Ex ECDLP.L84 ECDLP.L64 ECDLP.L56 ECDLP.L73 ECDLP.L83 ECDLP.L81 ECDLP.L89 ECDLP.L80
  ECDLP.L65 ECDLP.L70 ECDLP.L59 ECDLP.L54 ECDLP.L44 ECDLP.L58 ECDLP.L34 ECDLP.L35 ECDLP.L51 ECDLP.L85B ECDLP.L57

/-- `EdgeCore` restricted to the memories satisfying `P` -/
structure EdgeCoreF (P : ℕ → (ℕ → ℕ → ℕ) → Prop) (DB r : ℕ) (E : NEx) (gE btE : Ex) where
  syn : ExSyn DB E gE btE
  D : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → WNet m
  hcong : ∀ m n k A A', (∀ a, a ≠ 3 → A' a = A a) → D m n k A' = D m n k A
  fields : ∀ m n k A, P n A → FieldsAt r E gE btE m n k A (D m n k A)

open Classical in
/-- the network assigned to `(m, n, k, A)`: the frame network if `A` is a frame, else a fixed default -/
def DrealF (r : ℕ) : ∀ m n k : ℕ, (ℕ → ℕ → ℕ) → WNet m :=
  fun m n k A => if h : Fr r n (zero3 A) then fN r (Classical.choose h) m else fN r ⟨1, 0, 0, 0, 0, []⟩ m

open Classical in
/-- **The real network as a frame-restricted `EdgeCore 200`** (repaired instance, clamped dispatch).  Only `r + 1 <= 2^19000` (for `BN`). -/
def edgeCoreF_real2 (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) :
    EdgeCoreF (fun n A => Fr r n (zero3 A)) 200 r (Ereal2 r) (gEreal2 r) (btReal2 r) where
  syn := exSyn_real2 r
  D := DrealF r
  hcong m n k A A' h := by
    have := zero3_eq_of_agree h
    show (if h : Fr r n (zero3 A') then _ else _) = (if h : Fr r n (zero3 A) then _ else _)
    simp only [this]
  fields m n k A hA := by
    apply FieldsAt.of_zero3 (noRdAll_real2 r)
    unfold DrealF
    rw [dif_pos hA]
    exact frame_fields r (Classical.choose hA) m (frameRep_real2 r) (hbtE_real2 r) (wtBnd_real r)
      (frameBnd_real2 r (bddHyps_real r hr)) n k (zero3 A) (zero3_clear A) (Classical.choose_spec hA)

theorem reads72n_zero3 {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
    (h : Reads72n σ A p a b X xR yR π ℓ bW) : Reads72n σ (zero3 A) p a b X xR yR π ℓ bW where
  hp := by simpa [zero3] using h.hp
  ha := by simpa [zero3] using h.ha
  hb := by simpa [zero3] using h.hb
  hxR := by simpa [zero3] using h.hxR
  hyR := by simpa [zero3] using h.hyR
  hOp := by simpa [zero3] using h.hOp
  hX := by simpa [zero3] using h.hX
  hlen := by simpa [zero3] using h.hlen
  hl := by simpa [zero3] using h.hl
  hbW := by simpa [zero3] using h.hbW
  hpi := by intro q hq; simpa [zero3] using h.hpi q hq

/-- **every actual engine call is a frame**: a `Good` instance with a `FrameIn` state has `Fr r len (zero3 s.ar)` -/
theorem frameIn_fr (r : ℕ) (x : Inst) (τ : List Bool) (hG : Good (r + 1) x τ) (s : Factoring.Aux.Copied.PLib.St)
    (hF : FrameIn r (redInp x τ) s) : Fr r (s.sc 0) (zero3 s.ar) := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  obtain ⟨hF0, hF2, hRd⟩ := hF
  have hodd : p % 2 = 1 := odd_of_good r (p, a, b, xR, yR, π) τ hG
  have hp := hG.1
  have hp0 : 0 < p := hp.pos
  refine ⟨⟨p, a % p, b % p, xR % p, yR % p, τ⟩, hp0, hodd, Nat.mod_lt _ hp0, Nat.mod_lt _ hp0, Nat.mod_lt _ hp0,
    Nat.mod_lt _ hp0, ?_, ?_, ?_, ?_⟩
  · rw [hF0]; simp only [redInp, EdgeInp.len]; omega
  · exact reads72n_zero3 (reads72n_congr0 hRd rfl)
  · rw [hF0]; simp only [redInp, EdgeInp.len]; omega
  · show 2 ≤ Nat.size p
    by_contra hcon
    have h1 : Nat.size p ≤ 1 := by omega
    have h2 : p < 2 ^ 1 := Nat.size_le.1 h1
    have := hp.two_le
    omega

end ECDLP.L96
end
