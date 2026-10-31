import ECDLP.L92_Look

/-!
# L92 / LookOk: correctness of the lookup command on `FrameIn'` states with `len < T0`
-/
noncomputable section
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L80 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the coordinates of a point (`(0,0)` for the point at infinity), as in `strings` -/
def xyP {p : ℕ} (W : WeierstrassCurve (ZMod p)) : W.toAffine.Point → ZMod p × ZMod p
  | .zero => (0, 0)
  | .some x y _ => (x, y)

/-- `strings` with the curve data given as `ZMod p` values -/
def SO (m p : ℕ) (hp : p.Prime) (A Bc X Y : ZMod p) (π : List Bool) : Set (List Bool) :=
  haveI := Fact.mk hp
  let W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, A, Bc⟩
  let B := sInf {B | p ≤ B ^ m}
  let xy : W.toAffine.Point → ZMod p × ZMod p := xyP W
  let str (P : Fin m → W.toAffine.Point) : List Bool := (List.ofFn fun i =>
    (List.range (Nat.size B)).reverse.map (fun j => (xy (P i)).1.val.testBit j) ++
      [decide ((p - 1) / 2 < (xy (P i)).2.val)]).flatten
  {s | W.Δ ≠ 0 ∧ ∃ P : Fin m → W.toAffine.Point, str P = s ∧ π <+: s ∧
    (∀ i, P i ≠ 0 ∧ (xy (P i)).1.val < B) ∧
    (∀ k : Fin m, 0 < k.val → let S := ((List.ofFn P).take k).sum
      S ≠ 0 ∧ (xy S).1 ≠ (xy (P k)).1) ∧
    (List.ofFn P).sum ≠ 0 ∧ xy (List.ofFn P).sum = (X, Y)}

theorem strings_eq_SO (m p a b x y : ℕ) (π : List Bool) :
    ECDLP.strings m (p, a, b, x, y, π) =
      if hp : p.Prime then SO m p hp (a : ZMod p) (b : ZMod p) (x : ZMod p) (y : ZMod p) π else ∅ := by
  unfold ECDLP.strings
  by_cases hp : p.Prime
  · simp only [dif_pos hp]; rfl
  · simp only [dif_neg hp]

theorem strings_red (m p a b x y : ℕ) (π : List Bool) :
    ECDLP.strings m (p, a % p, b % p, x % p, y % p, π) = ECDLP.strings m (p, a, b, x, y, π) := by
  rw [strings_eq_SO, strings_eq_SO]
  by_cases hp : p.Prime
  · simp only [dif_pos hp, ZMod.natCast_mod]
  · simp only [dif_neg hp]

theorem Zc_red (m p a b x y : ℕ) (π τ : List Bool) :
    Zc m (p, a % p, b % p, x % p, y % p, π) τ = Zc m (p, a, b, x, y, π) τ := by
  unfold Zc withPre
  simp only
  rw [strings_red]

/-- the lookup command: a decision tree for each length `< T0` -/
def lookCmd (m T0 : ℕ) : Cmd := dispatch (fun ℓ => dtree (probesL ℓ) (tabAns m ℓ)) T0

theorem look_spec (r T0 : ℕ) (x : Inst) (τ : List Bool) (s : St) (hF : FrameIn r (redInp x τ) s)
    (hlen : (redInp x τ).len < T0) (hτ : τ.length ≤ (redInp x τ).len) :
    (Cmd.run (lookCmd (r + 1) T0) s).1.sc 3 =
      (open Classical in if 0 < Zc (r + 1) x τ then 0 else 1) ∧ (Cmd.run (lookCmd (r + 1) T0) s).2 ≤ 38 * T0 + 1 := by
  classical
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hs0 : s.sc 0 = (redInp (p, a, b, xR, yR, π) τ).len := hF.1
  have hd := dispatch_run (fun ℓ => dtree (probesL ℓ) (tabAns (r + 1) ℓ))
    (fun ℓ st => tabAns (r + 1) ℓ (probeBits st (probesL ℓ))) T0 (35 * T0 + 1)
    (fun ℓ st hℓ => by
      refine ⟨(dtree_run _ _ st).1, le_trans (dtree_run _ _ st).2 ?_⟩
      rw [length_probesL]; omega)
    (fun ℓ st v => rfl) T0 s le_rfl (by omega)
  unfold lookCmd
  refine ⟨?_, by omega⟩
  rw [hd.1]
  -- decode
  have hR := hF.2.2
  simp only [redInp] at hR hs0
  set ℓ := s.sc 0 with hℓ
  have hdec := decode_probes s ℓ
  have hlenπ : numCells (s.ar 9) 1 ℓ = τ.length := by rw [hℓ]; exact hR.hlen
  have hπ : ((List.range ℓ).map fun j => decide (s.ar 6 (1 + j) ≠ 0)).take (numCells (s.ar 9) 1 ℓ) = τ := by
    rw [hlenπ]
    have hτl : τ.length ≤ ℓ := by
      rw [hs0]; simp only [EdgeInp.len] at hτ ⊢; simpa [redInp, EdgeInp.len] using hτ
    apply List.ext_getElem
    · simp [List.length_take, hτl]
    · intro j h1 h2
      have hj : j < τ.length := h2
      rw [List.getElem_take, List.getElem_map, List.getElem_range]
      have := hR.hpi j hj
      rw [Nat.add_comm 1 j]
      by_cases hb : τ[j] = true
      · simp [hb] at this ⊢; exact this
      · have hb' : τ[j] = false := by simpa using hb
        simp [hb'] at this ⊢; exact this
  unfold tabAns
  rw [hdec, hπ]
  have e0 : numCells (s.ar 0) 1 ℓ = p := hR.hp
  have e1 : numCells (s.ar 1) 1 ℓ = a % p := hR.ha
  have e2 : numCells (s.ar 2) 1 ℓ = b % p := hR.hb
  have e4 : numCells (s.ar 4) 1 ℓ = xR % p := hR.hxR
  have e5 : numCells (s.ar 5) 1 ℓ = yR % p := hR.hyR
  simp only [e0, e1, e2, e4, e5]
  have := Zc_red (r + 1) p a b xR yR [] τ
  have h2 : Zc (r + 1) (p, a, b, xR, yR, []) τ = Zc (r + 1) (p, a, b, xR, yR, π) τ := by
    unfold Zc withPre; rfl
  rw [this, h2]

end ECDLP.L92
end
