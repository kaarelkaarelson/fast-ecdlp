import ECDLP.L44_Str

/-!
# L44 / Main: one network whose value is the number of generic decompositions with a given prefix

`main_count`: for the Weierstrass curve `y² = x³ + a x + b` over `ZMod p`, `m = n + 1` points, prefix `π` of
L35's string (`ℓ` bits of each `x_i`, big-endian, then the sign bit `[(p-1)/2 < y_i]`), the value of the network
`gadgetNet N (combine F B) (okC N (Cl ..))` is the number of tuples in `GenSet` (ordered generic factor-base
tuples with `x_i.val < X` and sum `R`) whose string `strOf p ℓ P` has prefix `π`.
-/
noncomputable section
namespace ECDLP.L44
open Finset ECDLP.L30 Slot Cst ECDLP.L34 ECDLP.L35 ECDLP.L38

variable {n K : ℕ}

open Classical in
theorem main_count (I : Inst) [hpp : Fact I.p.Prime] [(shortW I.p I.a I.b).IsElliptic]
    (N : NPar) (π : List Bool) (ℓ : ℕ) (hℓ : ℓ ≤ N.b * 2 ^ N.k)
    (hlen : π.length ≤ (n + 1) * (ℓ + 1)) (e : Cn n ≃ Fin K)
    -- instance conditions (as in L30 `card_int_eq_card_generic`)
    (ha0 : 0 ≤ I.a) (ha : I.a < I.p) (hb0 : 0 ≤ I.b) (hb : I.b < I.p) (hXp : I.X ≤ I.p)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hO : 2 * (I.p : ℤ) ≤ I.O) (hN : I.O + 2 * (I.p : ℤ) < I.N)
    (hR : 0 ≤ I.R.1 ∧ I.R.1 < I.p ∧ 0 ≤ I.R.2 ∧ I.R.2 < I.p)
    (hRns : (shortW I.p I.a I.b).Nonsingular (I.R.1 : ZMod I.p) (I.R.2 : ZMod I.p))
    -- parameters of the network
    (hcvB : ∀ c, I.cv c < 2 ^ (N.b * 2 ^ N.k))
    (B : ℤ) (hB : 0 < B)
    (hBd : ∀ c, ((famF (fun i : Fin (n + 1) => sgOf ℓ π i) e c).mass : ℤ) *
      ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B)
    (hS : N.SizeOK (combine (famF (fun i : Fin (n + 1) => sgOf ℓ π i) e) B)) (hb1 : 1 ≤ N.b)
    {g : ℕ} (eg : Gate (Slot n) N.A ≃ Fin g) :
    (((gadgetNet N (combine (famF (fun i : Fin (n + 1) => sgOf ℓ π i) e) B)
        (okC N (Cl I (N.b * 2 ^ N.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toForced.toGNet).toNet eg).value =
      ((((GenSet (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X)
        ((I.R.1 : ZMod I.p), (I.R.2 : ZMod I.p)) n).filter
          (fun P => π <+: strOf I.p ℓ P)).card : ℕ) : ℤ) := by
  have hcv0 : ∀ c, 0 ≤ I.cv c := by
    intro c
    have hp : (0 : ℤ) ≤ I.p := by positivity
    cases c <;> simp only [Inst.cv_one, Inst.cv_cp, Inst.cv_ca, Inst.cv_cb, Inst.cv_cOp, Inst.cv_cX,
      Inst.cv_cN, Inst.cv_cRx, Inst.cv_cRy, Inst.cv_cc0, Inst.cv_cc1] <;> first | positivity | linarith [hR.1, hR.2.2.1] | exact mul_nonneg (by linarith) hp
  have hxc : ∀ i : Fin (n + 1), ∀ jb ∈ xcOf ℓ π i, jb.1 < N.b * 2 ^ N.k := by
    intro i jb hjb
    simp only [xcOf, List.mem_filterMap, List.mem_range] at hjb
    obtain ⟨q, hq, hπ⟩ := hjb
    cases hq' : π[i * (ℓ + 1) + q]? with
    | none => simp [hq'] at hπ
    | some β =>
      simp only [hq', Option.map_some, Option.some.injEq] at hπ
      subst hπ
      show ℓ - 1 - q < _
      omega
  rw [net_value I N (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) e hcv0 hcvB hXX
    hxc B hB hBd hS hb1 eg,
    ncard_int_filter I (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i)
      ha0 ha hb0 hb hXp hXX hO hN hR hRns]
  congr 2
  apply Finset.filter_congr
  intro P _
  exact (prefix_iff_QP I.p ℓ π hlen P).symm

end ECDLP.L44
end

#print axioms ECDLP.L44.main_count
