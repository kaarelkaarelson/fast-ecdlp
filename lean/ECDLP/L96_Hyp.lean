import ECDLP.L96_Bnd
import ECDLP.L81_Bdd
import ECDLP.L90_BddD
import ECDLP.L80_BWle

/-!
# L96 / Hyp: discharging `BddHyps` (L95's five open hypotheses) on frame data

* `hwV`, `hcV`: the widths of the edge network are `<= ewid <= Sb n`, so `2^c <= V` from `hset` (L57 `msg_w_le`, L89 `parB`).
* `hsN`: `sN <= 2^wt <= 2^Wm <= 2^Pb <= V` (frame network `fN_hheld`, `WtBnd`, `hWc`); `sN = 1` outside the node range.
* `hsrc`: L81 `bdd_srcSlot` with the numerics of `parB` / `X5_le_V`.
* `hbn`: `BN V sigma0 B r` -- needs `Ub r n <= V` (`ok_U0`, i.e. `r + 1 <= 2^19000`), the only place where that bound enters.
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

theorem hWm_of {r V m K0 ℓ n : ℕ} (h : EdgeReq r V m K0 ℓ n) : ECDLP.L65.Wm r n ≤ V :=
  le_trans (le_trans (Pb_ge r (Gs K0 ℓ) n) (Nat.lt_two_pow_self).le) h.hWc

theorem ewid_le {r : ℕ} (d : FrData) (n : ℕ) (hn : Nat.size d.p + 4 ≤ 4 * n)
    (g : CG (Slot r) (UC (sgR r (ell d.p r) d.τ) (cnEquiv r)) (NParE (Nat.size d.p)).A) :
    ewid (NParE (Nat.size d.p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) g ≤ Sb n := by
  have hPB := parB (Nat.size d.p) n hn
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ (Xs_pos n)
  have hSb : Sb n = 19680 * Xs n ^ 3 := rfl
  cases g with
  | src i s =>
    show (NParE (Nat.size d.p)).b * (NParE (Nat.size d.p)).h + 1 ≤ Sb n
    have := hPB.hbh
    show bP (Nat.size d.p) * hP (Nat.size d.p) + 1 ≤ Sb n
    omega
  | gt c _ =>
    show (NP (NParE (Nat.size d.p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) c).M + 4 ≤ Sb n
    have hMc : (NP (NParE (Nat.size d.p)) (fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) c).M = DP (Nat.size d.p) * wP (Nat.size d.p) := rfl
    rw [hMc]
    have := hPB.hM
    omega

theorem hwV_real {r V m n : ℕ} (d : FrData) (hn : Nat.size d.p + 4 ≤ 4 * n) (hset : 2 ^ Sb n ≤ V) :
    ∀ i, (dNet r d m).w i + 1 ≤ V := by
  intro i
  have h1 := msg_w_le (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) i
  have wi : (dNet r d m).w i = (edgeNet (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ)).w i := rfl
  rw [wi]
  exact le_V hset (le_trans h1 (ewid_le d n hn i))

theorem hcV_real {r V m : ℕ} (d : FrData) {n : ℕ} (hn : Nat.size d.p + 4 ≤ 4 * n) (hset : 2 ^ Sb n ≤ V) :
    ∀ a b : Fin ((layOf (sgR r (ell d.p r) d.τ)).gTot (NParE (Nat.size d.p)).A),
      2 ^ (toGNetE (dNet r d m) (ECDLP.L68.edgeEM (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
          (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) m)).c
          ((dEnum r d).symm a) ((dEnum r d).symm b) ≤ V := by
  intro a b
  refine pow_le_V hset ?_
  set i := (dEnum r d).symm a
  set j := (dEnum r d).symm b
  have hi := msg_w_le (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) i
  have hj := msg_w_le (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ) j
  have ei := ewid_le d n hn i
  have ej := ewid_le d n hn j
  show (if j ∈ (dNet r d m).pa i then (dNet r d m).w j + 1 else if i ∈ (dNet r d m).pa j then (dNet r d m).w i + 1 else 0) ≤ Sb n
  have wi : (dNet r d m).w i = (edgeNet (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ)).w i := rfl
  have wj : (dNet r d m).w j = (edgeNet (w := fun _ : Fin (18 * r + 12) => wP (Nat.size d.p)) (phiR r (ell d.p r) d.τ)
    (frF (sgR r (ell d.p r) d.τ) (cnEquiv r)) (okR r d.p d.a d.b d.xR d.yR d.τ)).w j := rfl
  split_ifs <;> omega

theorem hsN_real {r V m ℓ n : ℕ} (d : FrData) (hp0 : 0 < d.p) (hn : Nat.size d.p + 4 ≤ 4 * n)
    (hE : EdgeReq r V m Factoring.Aux.K0u ℓ n) :
    ∀ a : ℕ, sN (dNet r d m) (dEnum r d) a ≤ V := by
  intro a
  by_cases ha : a < (layOf (sgR r (ell d.p r) d.τ)).gTot (NParE (Nat.size d.p)).A
  · have h1 := fN_hheld r d m ⟨a, ha⟩
    have h2 := (wtBnd_real r d m n hp0 hn).1 ⟨a, ha⟩
    have h3 : 2 ^ ECDLP.L65.Wm r n ≤ V :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Pb_ge r (Gs Factoring.Aux.K0u ℓ) n)) hE.hWc
    exact le_trans h1 (le_trans (Nat.pow_le_pow_right (by norm_num) h2) h3)
  · have hV : 1 ≤ V := by have := hE.hn; omega
    have e1 : nfN (dNet r d m) (dEnum r d) a = 1 := by unfold nfN; rw [dif_neg ha]
    have e2 : nA (dNet r d m) (dEnum r d) a = fun _ => 1 := by funext k; unfold nA; rw [dif_neg ha]
    unfold sN
    rw [e1, e2, pp_const]
    simpa using hV


/-- `BN` on frame data (needs `Ub r n <= V`, i.e. `hr : r + 1 <= 2^19000` through `ok_U0`) -/
theorem hbn_real {r V m k ℓ n : ℕ} (hr : r + 1 ≤ 2 ^ 19000) (d : FrData) {B : ℕ → ℕ → ℕ} (hD : FrD r n B d)
    (hE : EdgeReq r V m Factoring.Aux.K0u ℓ n) (hA1 : ∀ a j, B a j ≤ 1) :
    ∀ σ₀, CtxM m n k σ₀ → BN V σ₀ B r := by
  intro σ₀ hC
  obtain ⟨hp0, hodd, ha, hb, hx, hy, hnS, hRd, hlen, h2s⟩ := hD
  have h0 : σ₀ 0 = n := hC.2.2.1
  have hn16 := hE.hn
  have hN := nodes_le_V hE (show 2 ≤ Factoring.Aux.K0u by decide)
  have hq := ECDLP.L95.hn_r_of_nodes r n hN
  have hUb := ok_U0 hr hE
  have hUg := Ub_ge r n (Nat.size d.p) hnS
  have hell : ell d.p r ≤ Nat.size d.p := Nat.size_le_size (Bd_le hp0 r)
  have hbW := bWof_le (Nat.size d.p) h2s
  have e9 : numCells (B 9) 1 n = d.τ.length := hRd.hlen
  have e10 : numCells (B 10) 1 n = ell d.p r := hRd.hl
  have e11 : numCells (B 11) 1 n = ECDLP.L72.bWof (Nat.size d.p) := hRd.hbW
  refine ⟨by omega, hA1, by rw [h0]; omega, by rw [h0, e9]; omega, by rw [h0, e10]; omega,
    by rw [h0, e11]; omega, ?_, by omega⟩
  rw [h0, e10]
  have : (r + 2) * (ell d.p r + 2) ≤ 96552 * (r + 1) * (Nat.size d.p + 4) := by
    calc (r + 2) * (ell d.p r + 2) ≤ (2 * (r + 1)) * (Nat.size d.p + 4) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 96552 * (r + 1) * (Nat.size d.p + 4) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem hsrc_real {r V m k ℓ n : ℕ} (d : FrData) {B : ℕ → ℕ → ℕ} (hnS : Nat.size d.p + 4 ≤ 4 * n)
    (hE : EdgeReq r V m Factoring.Aux.K0u ℓ n) (hbn : ∀ σ₀, CtxM m n k σ₀ → BN V σ₀ B r)
    (hm1 : 1 < m) (hR : ReadsR (CtxM m n k) B r d.p d.a d.b d.xR d.yR d.τ) (hodd : d.p % 2 = 1) :
    ∀ σ₀, CtxM m n k σ₀ → ∀ σ : ℕ → ℕ, Ag 13 σ₀ σ →
        ∀ (a : Fin ((layOf (sgR r (ell d.p r) d.τ)).gTot (NParE (Nat.size d.p)).A)) (i : Slot r) (s : Fin (NParE (Nat.size d.p)).A),
          (dEnum r d).symm a = CG.src i s → σ (16 + 4) = a → σ (16 + 7) ≤ V →
          σ (16 + 10) = 2 ^ (NParE (Nat.size d.p)).b → σ (16 + 12) = (NParE (Nat.size d.p)).A →
          σ (16 + 13) = (NParE (Nat.size d.p)).h → σ (16 + 14) = (NParE (Nat.size d.p)).b →
          σ (16 + 16) = (layOf (sgR r (ell d.p r) d.τ)).eι i → σ (16 + 17) = s →
          Bdd V σ B (rSrc2 r d.p d.a d.b d.xR d.yR d.τ m hm1 hR hodd).srcE := by
  intro σ₀ hC σ hσ a i s hsym h4 h7 h10 h12 h13 h14 h16 h17
  have H : BN V σ B r := ECDLP.L90.BN_ag (by norm_num) hσ (hbn σ₀ hC)
  have hset := hE.hset
  have hN := nodes_le_V hE (show 2 ≤ Factoring.Aux.K0u by decide)
  have hq := ECDLP.L95.hn_r_of_nodes r n hN
  have hPB := parB (Nat.size d.p) n hnS
  have hX3 : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ (Xs_pos n)
  have hX1 : 1 ≤ Xs n := Xs_pos n
  have hX5 := X5_le_V hset
  have hSb : Sb n = 19680 * Xs n ^ 3 := rfl
  have hb1 : 1 ≤ bP (Nat.size d.p) := bP_pos _
  have hh1 : 1 ≤ hP (Nat.size d.p) := Nat.one_le_two_pow
  have hbh := hPB.hbh
  have hAp := hPB.hA
  have hq16 : σ (16 + 16) ≤ V := by
    rw [h16]
    have := ((layOf (sgR r (ell d.p r) d.τ)).eι i).2
    have h2 : (layOf (sgR r (ell d.p r) d.τ)).nι = 24 * r + 23 := rfl
    omega
  have hjj : hP (Nat.size d.p) * AP (Nat.size d.p) * bP (Nat.size d.p) + 2 ≤ V := by
    have h4' : Xs n ^ 4 ≤ Xs n ^ 5 := Nat.pow_le_pow_right hX1 (by norm_num)
    have : hP (Nat.size d.p) * AP (Nat.size d.p) * bP (Nat.size d.p) = (bP (Nat.size d.p) * hP (Nat.size d.p)) * AP (Nat.size d.p) := by ring
    rw [this]
    have h5 : (bP (Nat.size d.p) * hP (Nat.size d.p)) * AP (Nat.size d.p) ≤ (444 * Xs n ^ 3) * (3 * Xs n) := Nat.mul_le_mul hbh hAp
    have h6 : (444 * Xs n ^ 3) * (3 * Xs n) = 1332 * Xs n ^ 4 := by ring
    have h7' : 1 ≤ Xs n ^ 4 := Nat.one_le_pow _ _ hX1
    omega
  have hpw : 2 ^ (bP (Nat.size d.p) * hP (Nat.size d.p)) ≤ V := pow_le_V hset (by omega)
  have hhV : hP (Nat.size d.p) ≤ V := by
    have : hP (Nat.size d.p) ≤ bP (Nat.size d.p) * hP (Nat.size d.p) := Nat.le_mul_of_pos_left _ hb1
    exact le_V hset (by omega)
  have hbV : bP (Nat.size d.p) ≤ V := by
    have : bP (Nat.size d.p) ≤ bP (Nat.size d.p) * hP (Nat.size d.p) := Nat.le_mul_of_pos_right _ hh1
    exact le_V hset (by omega)
  show Bdd V σ B (srcE 16 (badE 16 r))
  exact bdd_srcSlot H (u := 16) (h := hP (Nat.size d.p)) (b := bP (Nat.size d.p)) (As := AP (Nat.size d.p)) (s := s)
    (code := σ (16 + 7)) h13 h14 h12 h17 rfl s.2 hq16 h7 hjj hpw hhV hbV

/-- **`BddHyps` on frame data, from `r + 1 <= 2^19000`** -/
theorem bddHyps_real (r : ℕ) (hr : r + 1 ≤ 2 ^ 19000) : BddHyps r := by
  intro d m n k B V ℓ hB3 hD hE hk hA1 hm1 hR hodd
  have hnS : Nat.size d.p + 4 ≤ 4 * n := hD.2.2.2.2.2.2.1
  have hbn := hbn_real (k := k) hr d hD hE hA1
  exact ⟨hbn, hsN_real d hD.1 hnS hE, hcV_real d hnS hE.hset, hwV_real d hnS hE.hset,
    hsrc_real d hnS hE hbn hm1 hR hodd⟩

/-- **Capstone, `r + 1 <= 2^19000`**: only `OffFrame` remains. -/
theorem subexp_real2_final (r : ℕ) (hr1 : 1 ≤ r) (hr : r + 1 ≤ 2 ^ 19000)
    (Hj : OffFrame r (Ereal2 r) (gEreal2 r) (btReal2 r)) : (ECDLP.SubexponentialRateStmt (r + 1)) :=
  subexp_real2' r hr1 (bddHyps_real r hr) Hj

end ECDLP.L96
end
