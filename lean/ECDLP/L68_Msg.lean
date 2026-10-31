import ECDLP.L68_Ring
import ECDLP.L68_Car
import ECDLP.L56_Edge

/-!
# L68 / Msg: the fa / mid / ib messages of the gadget as `Ex` expressions (N-level)

`rp_faMsgS`, `rp_midMsg`, `rp_ibOut` : with `q = 2^M + 1` in slot `vq`, `A` in slot `vA`,
`Rp` = the expression evaluates to the `ZMod.val` of the message `faMsgS` / `midMsg` / `ibOut` of L34 / L38.
-/
noncomputable section
namespace ECDLP.L68
open Finset Factoring.Aux Ex ECDLP.L34

section
variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem q_gt (N : NPar) (hM : 1 ≤ N.M) : 2 < 2 ^ N.M + 1 := by
  have : 2 ^ 1 ≤ 2 ^ N.M := Nat.pow_le_pow_right (by norm_num) hM
  omega

/-- `faMsgS`: root `2^w`, digit body `u` (reads the loop variable `x1`) -/
theorem rp_faMsgS (N : NPar) (hM : 1 ≤ N.M) {vq vA x1 : ℕ} (hq : σ vq = 2 ^ N.M + 1) (hvq : vq < x1) (hvA : vA < x1)
    (hA : σ vA = N.A) {e0 r k u : Ex} (h0 : Ex.FV (· < x1) e0) (hr : Ex.FV (· < x1) r) (hk : Ex.FV (· < x1) k)
    (hE : Ex.eval σ A e0 = N.w) {s k' : ℕ} (hR : Ex.eval σ A r = s) (hK : Ex.eval σ A k = k')
    (ud : Fin N.h → Fin (2 ^ N.b))
    (hu : ∀ i < N.A, Rp (Function.update σ x1 i) A u (((NPar.exA (fun t => (ud t : ℕ)) i : ℕ) : N.Rg))) :
    Rp σ A (faE vq vA x1 e0 r k u) (N.faMsgS ud s k') := by
  have := rp_fa (q := 2 ^ N.M + 1) (A := A) hq (q_gt N hM) hvq hvA hA h0 hr hk hE hR hK
    (fun i' => ((NPar.exA (fun t => (ud t : ℕ)) i' : ℕ) : N.Rg)) hu
  exact this

/-- `ibOut`: root `ωi = 2^(w (2^(k+1) - 1))`, `tInv = 2^eT` -/
theorem rp_ibOut (N : NPar) (hM : 1 ≤ N.M) {vq vA x1 : ℕ} (hq : σ vq = 2 ^ N.M + 1) (hvq : vq < x1) (hvA : vA < x1)
    (hA : σ vA = N.A) {e0 eT k u : Ex} (h0 : Ex.FV (· < x1) e0) (hk : Ex.FV (· < x1) k)
    (hE : Ex.eval σ A e0 = N.w * (2 ^ (N.k + 1) - 1)) (hT : Ex.eval σ A eT = (2 * N.M - 1) * (N.k + 1))
    {j : ℕ} (hK : Ex.eval σ A k = j) (Z : ℕ → N.Rg)
    (hu : ∀ i < N.A, Rp (Function.update σ x1 i) A u (Z i)) :
    Rp σ A (ibE vq vA x1 e0 eT k u) (ibOut N.A N.ωi N.tInv Z j) := by
  have := rp_ib (q := 2 ^ N.M + 1) (A := A) hq (q_gt N hM) hvq hvA hA h0 hk hE hT hK Z hu
  have e1 : N.ωi = (2 : ZMod (2 ^ N.M + 1)) ^ (N.w * (2 ^ (N.k + 1) - 1)) := by
    unfold Par.ωi Par.ω; rw [pow_mul]
  have e2 : N.tInv = (2 : ZMod (2 ^ N.M + 1)) ^ ((2 * N.M - 1) * (N.k + 1)) := rfl
  unfold ibOut
  rw [e1, e2]
  exact this


/-- `midMsg` of a form `F` over slots `ι` (slot codes via `dec`) -/
theorem rp_midMsg {ι : Type} (N : NPar) (hM : 1 ≤ N.M) (F : Form ι) {vq vA x1 x2 x3 vI vS : ℕ}
    (hq : σ vq = 2 ^ N.M + 1) (hvq : vq < x1) (hvA : vA < x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS) (hA : σ vA = N.A)
    {ei ew k1 j1 nE epsE lE rE yE : Ex}
    (hei : Ex.FV (· < x1) ei) (hew : Ex.FV (· < x1) ew) (hk1 : Ex.FV (· < x1) k1) (hj1 : Ex.FV (· < x1) j1)
    (hn : Ex.FV (· < x1) nE) (hε : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hl : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hr : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hy : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) yE)
    {K1 J1 : ℕ} (hEi : Ex.eval σ A ei = N.w * (2 ^ (N.k + 1) - 1)) (hEw : Ex.eval σ A ew = N.w)
    (hK1 : Ex.eval σ A k1 = K1) (hJ1 : Ex.eval σ A j1 = J1) (hnv : Ex.eval σ A nE = F.n)
    (dec : ℕ → ι) (Y : ι → ℕ → N.Rg)
    (hεv : ∀ t (ht : t < F.n), Rp (Function.update σ x2 t) A epsE ((F.ε ⟨t, ht⟩ : ℤ) : N.Rg))
    (hlv : ∀ t (ht : t < F.n), dec (Ex.eval (Function.update σ x2 t) A lE) = F.l ⟨t, ht⟩)
    (hrv : ∀ t (ht : t < F.n), dec (Ex.eval (Function.update σ x2 t) A rE) = F.r ⟨t, ht⟩)
    (hyv : ∀ i s, s < N.A → Rp (Function.update (Function.update σ vI i) vS s) A yE (Y (dec i) s)) :
    Rp σ A (midE vq vA x1 x2 x3 vI vS ei ew k1 j1 nE epsE lE rE yE) (N.midMsg F K1 Y J1) := by
  classical
  have := rp_mid (q := 2 ^ N.M + 1) (A := A) hq (q_gt N hM) hvq hvA h12 h23 h3I hIS hA hei hew hk1 hj1 hn hε hl hr hy
    hEi hEw hK1 hJ1 hnv (fun t => if ht : t < F.n then ((F.ε ⟨t, ht⟩ : ℤ) : N.Rg) else 0)
    (fun t => Ex.eval (Function.update σ x2 t) A lE) (fun t => Ex.eval (Function.update σ x2 t) A rE)
    (fun i s => Y (dec i) s)
    (fun t ht => by simpa [ht] using hεv t ht) (fun t _ => rfl) (fun t _ => rfl) hyv
  have e1 : N.ωi = (2 : ZMod (2 ^ N.M + 1)) ^ (N.w * (2 ^ (N.k + 1) - 1)) := by
    unfold Par.ωi Par.ω; rw [pow_mul]
  unfold Par.midMsg
  rw [e1]
  have hfun : (fun k₂ => ∑ t : Fin F.n, (F.ε t : N.Rg) * (hatOut N.A N.ω (Y (F.l t)) k₂ * hatOut N.A N.ω (Y (F.r t)) k₂)) =
      (fun k₂ => ∑ t ∈ range F.n, (fun t => if ht : t < F.n then ((F.ε ⟨t, ht⟩ : ℤ) : N.Rg) else 0) t *
        (hatOut N.A (2 ^ N.w) (fun s => Y (dec (Ex.eval (Function.update σ x2 t) A lE)) s) k₂ *
         hatOut N.A (2 ^ N.w) (fun s => Y (dec (Ex.eval (Function.update σ x2 t) A rE)) s) k₂)) := by
    funext k₂
    rw [← Fin.sum_univ_eq_sum_range (fun t => (if ht : t < F.n then ((F.ε ⟨t, ht⟩ : ℤ) : N.Rg) else 0) *
      (hatOut N.A (2 ^ N.w) (fun s => Y (dec (Ex.eval (Function.update σ x2 t) A lE)) s) k₂ *
       hatOut N.A (2 ^ N.w) (fun s => Y (dec (Ex.eval (Function.update σ x2 t) A rE)) s) k₂)) F.n]
    refine sum_congr rfl fun t _ => ?_
    simp only [t.2, dif_pos, hlv t t.2, hrv t t.2]
    rfl
  rw [hfun]
  exact this

end
end ECDLP.L68
end
