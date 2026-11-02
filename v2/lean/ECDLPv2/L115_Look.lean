import ECDLP.L92_Eng
import ECDLP.L92_Count
import ECDLP.L92_LookOk

/-!
# L115 / Look: the counting table for short inputs
`tabCnt m ℓ` is L92's `tabAns` with the COUNT `Zc` as the leaf (instead of the bit `[Zc = 0]`); `lookCnt` is L92's `lookCmd` with these leaves.
`lookCnt_spec` : on a `FrameIn` state with `len < T0`, scalar `3 = Zc (r+1) x τ`, within `38 T0 + 1` steps (same proof as `look_spec`).
`zc_short` : `Zc < 2^(r (len+1) + 1)` (from L92 `count_le`), the width of the binary conversion.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L115
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L80 ECDLP.L92 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def tabCnt (m ℓ : ℕ) (bs : List Bool) : ℕ :=
  let d := decode ℓ bs
  Zc m (d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, []) d.2.2.2.2.2

def lookCnt (m T0 : ℕ) : Cmd := dispatch (fun ℓ => dtree (probesL ℓ) (tabCnt m ℓ)) T0

theorem lookCnt_spec (r T0 : ℕ) (x : Inst) (τ : List Bool) (s : St) (hF : FrameIn r (redInp x τ) s)
    (hlen : (redInp x τ).len < T0) (hτ : τ.length ≤ (redInp x τ).len) :
    (Cmd.run (lookCnt (r + 1) T0) s).1.sc 3 = Zc (r + 1) x τ ∧ (Cmd.run (lookCnt (r + 1) T0) s).2 ≤ 38 * T0 + 1 := by
  classical
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hs0 : s.sc 0 = (redInp (p, a, b, xR, yR, π) τ).len := hF.1
  have hd := dispatch_run (fun ℓ => dtree (probesL ℓ) (tabCnt (r + 1) ℓ))
    (fun ℓ st => tabCnt (r + 1) ℓ (probeBits st (probesL ℓ))) T0 (35 * T0 + 1)
    (fun ℓ st hℓ => by
      refine ⟨(dtree_run _ _ st).1, le_trans (dtree_run _ _ st).2 ?_⟩
      rw [length_probesL]; omega)
    (fun ℓ st v => rfl) T0 s le_rfl (by omega)
  unfold lookCnt
  refine ⟨?_, by omega⟩
  rw [hd.1]
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
  unfold tabCnt
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

theorem zc_short (r : ℕ) (x : Inst) (τ : List Bool) (hg : Good (r + 1) x τ) :
    Zc (r + 1) x τ < 2 ^ (r * ((redInp x τ).len + 1) + 1) := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have hp : p.Prime := hg.1
  have hZ : Zc (r + 1) (p, a, b, xR, yR, π) τ ≤ (sInf {B | p ≤ B ^ (r + 1)} * 2) ^ r := by
    unfold Zc withPre
    simp only
    rw [strings_eq_SO, dif_pos hp]
    exact count_le r p hp _ _ _ _ τ
  have hB : sInf {B | p ≤ B ^ (r + 1)} ≤ p := sInf_le_prime (r + 1) p
  have hp2 : p < 2 ^ Nat.size p := Nat.lt_size_self p
  have hsz : Nat.size p ≤ (redInp (p, a, b, xR, yR, π) τ).len := by
    simp only [redInp, ECDLP.L65.EdgeInp.len]; omega
  have h1 : sInf {B | p ≤ B ^ (r + 1)} * 2 ≤ 2 ^ (Nat.size p + 1) := by rw [pow_succ]; omega
  calc Zc (r + 1) (p, a, b, xR, yR, π) τ ≤ (sInf {B | p ≤ B ^ (r + 1)} * 2) ^ r := hZ
    _ ≤ (2 ^ (Nat.size p + 1)) ^ r := Nat.pow_le_pow_left h1 r
    _ = 2 ^ ((Nat.size p + 1) * r) := by rw [← pow_mul]
    _ < 2 ^ (r * ((redInp (p, a, b, xR, yR, π) τ).len + 1) + 1) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        nlinarith

end ECDLP.L115
end
