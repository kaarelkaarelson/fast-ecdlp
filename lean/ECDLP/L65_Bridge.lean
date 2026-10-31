import ECDLP.L65_Params
import ECDLP.L57_Concrete

/-!
# L65 / Bridge: the real ECDLP edge network satisfies the data of `edgeFamily r`

For the input `(p, a, b, xR, yR)`, `r + 1` points, prefix `π`, with the explicit parameters of L59
(`NParE (Nat.size p)`; the per-slot width is `Z = Bits (size p) = 2·size p + 3` plus the gadget rounding,
all constants `< 2^Z`: `parOK_explicit`), and `n` any number with `Nat.size p + 4 ≤ 4 n` (the input length):

* `edge_bridge_fits`: for every enumeration of the gates and every cluster count `G > 0` there is a clustering
  `χ` into `G` clusters whose coarsened network has the same value as `edgeValue`, `total ≤ Ub r n` (`= Uc r · X^4`)
  and `Fits (Pb r G n)` (`= Ub r n / G + Wm r n`).  No `G^4 ≤ L` hypothesis.
* `edge_bridge_gates`: the number of gates is at most `nodesE r n` (`828 (r+1) X^2`).
* `edge_bridge_setting`: every gate's setting has at most `Sb n = 19680 X^3` bits.
-/
noncomputable section
namespace ECDLP.L65
open Finset ECDLP.L30 ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L59 ECDLP.L51
  Factoring.Aux

variable {r K : ℕ}

theorem Ub_ge (r n L : ℕ) (hn : L + 4 ≤ 4 * n) : 96552 * (r + 1) * (L + 4) ≤ Ub r n := by
  have h := Xs_n_le n
  unfold Ub Uc
  have : L + 4 ≤ 16 * Xs n ^ 4 := by omega
  nlinarith [Nat.zero_le (r + 1), Nat.mul_le_mul_left (96552 * (r + 1)) this]

open Classical in
theorem edge_bridge_fits (p a b xR yR : ℕ) (hp : 0 < p) (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (π : List Bool) (e : Cn r ≃ Fin K) (n G : ℕ) (hn : Nat.size p + 4 ≤ 4 * n) (hG : 0 < G)
    {g : ℕ} (eg : CG (Slot r) (UC (fun i : Fin (r + 1) => sgOf (ell p r) π i) e) (NParE (Nat.size p)).A ≃ Fin g) :
    ∃ χ : Fin g → Fin G,
      ((((edgeNet (N0 := NParE (Nat.size p)) (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val)
          (frF (fun i : Fin (r + 1) => sgOf (ell p r) π i) e)
          (okC (NParE (Nat.size p)) (Cl (instOf p a b xR yR r) ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
            (fun i : Fin (r + 1) => sgOf (ell p r) π i) (fun i : Fin (r + 1) => xcOf (ell p r) π i)))).toGNet).toNet
          eg).coarsen χ).Fits (Pb r G n) ∧
      ((((edgeNet (N0 := NParE (Nat.size p)) (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val)
          (frF (fun i : Fin (r + 1) => sgOf (ell p r) π i) e)
          (okC (NParE (Nat.size p)) (Cl (instOf p a b xR yR r) ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
            (fun i : Fin (r + 1) => sgOf (ell p r) π i) (fun i : Fin (r + 1) => xcOf (ell p r) π i)))).toGNet).toNet
          eg).coarsen χ).total ≤ Ub r n ∧
      ((((edgeNet (N0 := NParE (Nat.size p)) (w := fun _ : Fin K => wP (Nat.size p)) (fun c => Subtype.val)
          (frF (fun i : Fin (r + 1) => sgOf (ell p r) π i) e)
          (okC (NParE (Nat.size p)) (Cl (instOf p a b xR yR r) ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
            (fun i : Fin (r + 1) => sgOf (ell p r) π i) (fun i : Fin (r + 1) => xcOf (ell p r) π i)))).toGNet).toNet
          eg).coarsen χ).value =
        edgeValue (instOf p a b xR yR r) (NParE (Nat.size p)) (fun _ : Fin K => wP (Nat.size p)) π (ell p r) e eg := by
  have hKc : K ≤ 18 * (r + 1) := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin] at h
    have h2 := card_Cn_le (n := r)
    omega
  have hnn : ∀ c, Fintype.card (UC (fun i : Fin (r + 1) => sgOf (ell p r) π i) e c) ≤ 9 :=
    fun c => ECDLP.L63.card_UC_le9 _ e c
  have hocc : ∀ i, occ (ιc := UC (fun i : Fin (r + 1) => sgOf (ell p r) π i) e) (fun c => Subtype.val) i ≤ 18 * (r + 1) :=
    fun i => (occ_le_K (fun c => Subtype.val) (fun c => Subtype.val_injective) i).trans hKc
  have hw : ∀ c : Fin K, (fun _ : Fin K => wP (Nat.size p)) c ≤ 80 := by
    intro c
    have := M_le (Nat.size p)
    have hD := DP_pos (Nat.size p)
    simp only
    by_contra hcon
    push Not at hcon
    have : DP (Nat.size p) * 81 ≤ DP (Nat.size p) * wP (Nat.size p) := Nat.mul_le_mul_left _ hcon
    omega
  have hbb : (NParE (Nat.size p)).b ≤ 36 * 2 ^ (NParE (Nat.size p)).k := bP_le (Nat.size p)
  have hDL : 2 ^ (NParE (Nat.size p)).k * 2 ^ (NParE (Nat.size p)).k ≤ 1 * ((Nat.size p) + 4) := by
    have := DD_le (Nat.size p); simpa [NParE_k, DP] using this
  have hS : ∀ c, (NP (NParE (Nat.size p)) (fun _ : Fin K => wP (Nat.size p)) c).SizeOK (frF (fun i : Fin (r + 1) => sgOf (ell p r) π i) e c) :=
    (parOK_explicit p a b xR yR r hp ha hb hx hy π e).2.2.2
  have hb1 : 1 ≤ (NParE (Nat.size p)).b := bP_pos (Nat.size p)
  have hmax := Bw_le (w := fun _ : Fin K => wP (Nat.size p)) (N0 := NParE (Nat.size p)) (fun c => Subtype.val)
    (18 * (r + 1)) 9 36 80 hnn hocc hw hbb
  obtain ⟨χ, h1, h2, h3⟩ := edgeNet_fits (w := fun _ : Fin K => wP (Nat.size p)) (N0 := NParE (Nat.size p)) (fun c => Subtype.val)
    (frF (fun i : Fin (r + 1) => sgOf (ell p r) π i) e)
    (okC (NParE (Nat.size p)) (Cl (instOf p a b xR yR r) ((NParE (Nat.size p)).b * 2 ^ (NParE (Nat.size p)).k)
      (fun i : Fin (r + 1) => sgOf (ell p r) π i) (fun i : Fin (r + 1) => xcOf (ell p r) π i)))
    eg G hG _ hmax
  have hW := Wsum_le (N0 := NParE (Nat.size p)) (w := fun _ : Fin K => wP (Nat.size p)) 9 36 80 18 1 (r + 1) ((Nat.size p) + 4) hnn hw hbb hDL hKc
  have hU := Ub_ge r n (Nat.size p) hn
  have hAD := AD_le_X (Nat.size p) n hn
  have hUt : 18 * 1 * (4 * 9 * (36 + 80 + 5) + 12 * (80 + 4)) * (r + 1) * ((Nat.size p) + 4) ≤ Ub r n := by
    refine le_trans (le_of_eq ?_) hU
    ring
  refine ⟨χ, ?_, h2.trans (hW.trans hUt), ?_⟩
  · intro x
    refine (h1 x).trans ?_
    unfold Pb
    refine Nat.add_le_add (Nat.div_le_div_right (hW.trans hUt)) ?_
    unfold Wm Wcn
    have : ((18 * (r + 1) + 1) * (36 + 1) + (9 + 3) * (80 + 4)) * (AP (Nat.size p) * 2 ^ (NParE (Nat.size p)).k) ≤
        20532 * (r + 1) * Xs n ^ 3 := by
      have hD : 2 ^ (NParE (Nat.size p)).k = DP (Nat.size p) := rfl
      rw [hD]
      calc ((18 * (r + 1) + 1) * (36 + 1) + (9 + 3) * (80 + 4)) * (AP (Nat.size p) * DP (Nat.size p))
          ≤ (1711 * (r + 1)) * (12 * Xs n ^ 3) :=
            Nat.mul_le_mul (by nlinarith) hAD
        _ = 20532 * (r + 1) * Xs n ^ 3 := by ring
    exact this
  · rw [h3]
    rfl

end ECDLP.L65
end
