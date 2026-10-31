import ECDLP.L54_Value
import ECDLP.L44_Main

/-!
# L54 / Main: the per-identity network for L44's system

For each identity `c` of L30/L44's system (`famF sg e c`), the gadget `c` only reads the slots that occur in
its form (`usedS`), with its own ring exponent `M_c = 2^k w_c`; all gadgets read the shared source slots.
`main_count'`: `Net.value` of this network is the number of generic factor-base decompositions whose string has the
prefix `π` (same right-hand side as L44's `main_count`).
-/
noncomputable section
namespace ECDLP.L54
open Finset ECDLP.L30 ECDLP.L44 Slot Cst ECDLP.L34 ECDLP.L35 ECDLP.L38

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}

open Classical in
/-- L44's `system_value_V` count, from digit assignments to slot values (no network) -/
theorem dcount_eq_V (N : NPar) (F : Fin K → Form ι) (C : ι → List (ℕ × Bool))
    (hC : ∀ i, ∀ jb ∈ C i, jb.1 < N.b * 2 ^ N.k) :
    (univ.filter fun d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b) =>
        (∀ i s, okC N C i s (d i s)) ∧ ∀ c, N.Holds (F c) (N.dgOf d)).card =
      (univ.filter fun V : ι → Fin (2 ^ (N.b * 2 ^ N.k)) =>
        (∀ i, ∀ jb ∈ C i, ((V i : Fin _) : ℕ).testBit jb.1 = jb.2) ∧
          ∀ c, HV (F c) (fun i => ((V i : Fin _) : ℕ)) = 0).card := by
  refine Finset.card_bij (fun d _ => slotEquiv N d) ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    refine ⟨fun i jb hjb => ?_, fun c => ?_⟩
    · rw [slotEquiv_val]
      exact (okC_iff N C hC d i).1 (fun s => hd.1 i s) jb hjb
    · exact hd.2 c
  · intro d d' _ _ h
    exact (slotEquiv N).injective h
  · intro V hV
    refine ⟨(slotEquiv N).symm V, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hV ⊢
    have hv : ∀ i, sv N ((slotEquiv N).symm V) i = ((V i : Fin _) : ℕ) := fun i => by
      rw [← slotEquiv_val]; simp
    refine ⟨fun i s => ?_, fun c => ?_⟩
    · have := (okC_iff N C hC ((slotEquiv N).symm V) i).2 (by
        intro jb hjb; rw [hv]; exact hV.1 i jb hjb)
      exact this s
    · have := hV.2 c
      unfold HV at this
      show ∑ t : Fin (F c).n, (F c).ε t * (((N.toPar.val (N.dgOf ((slotEquiv N).symm V) ((F c).l t)) : ℕ) : ℤ) *
        ((N.toPar.val (N.dgOf ((slotEquiv N).symm V) ((F c).r t)) : ℕ) : ℤ)) = 0
      have h2 : ∀ i, N.toPar.val (N.dgOf ((slotEquiv N).symm V) i) = ((V i : Fin _) : ℕ) := hv
      simp only [h2]
      exact this

end

section
variable {n K : ℕ}

/-- slots occurring in a form -/
def usedS {ι : Type} [DecidableEq ι] (F : Form ι) : Finset ι := univ.image F.l ∪ univ.image F.r

theorem l_mem {ι : Type} [DecidableEq ι] (F : Form ι) (t : Fin F.n) : F.l t ∈ usedS F :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ t))

theorem r_mem {ι : Type} [DecidableEq ι] (F : Form ι) (t : Fin F.n) : F.r t ∈ usedS F :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ t))

/-- the form restricted to the slots it reads -/
def restr {ι : Type} [DecidableEq ι] (F : Form ι) : Form {i // i ∈ usedS F} where
  n := F.n
  l t := ⟨F.l t, l_mem F t⟩
  r t := ⟨F.r t, r_mem F t⟩
  ε := F.ε

theorem mass_restr {ι : Type} [DecidableEq ι] (F : Form ι) : (restr F).mass = F.mass := rfl

/-- the slot type of identity `c` -/
abbrev UC (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) : Type :=
  {i : Slot n // i ∈ usedS (famF sg e c)}

/-- the restricted forms -/
def frF (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) : Form (UC sg e c) := restr (famF sg e c)

theorem mass_frF (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (c : Fin K) : (frF sg e c).mass ≤ 6 := by
  show (famF sg e c).mass ≤ 6
  exact mass_le sg (e.symm c)

/-- numeric size condition of identity `c` (mass `≤ 6`) -/
theorem sizeOK_fr (sg : Fin (n + 1) → Sg) (e : Cn n ≃ Fin K) (N0 : NPar) (w : Fin K → ℕ) (c : Fin K)
    (h1 : 1 ≤ 2 ^ N0.k * w c) (h2 : 2 * 2 ^ N0.k ≤ N0.A * N0.A)
    (h3 : 12 * (2 ^ N0.k * (2 ^ N0.b * 2 ^ N0.b)) ≤ 2 ^ (2 ^ N0.k * w c)) :
    (NP N0 w c).SizeOK (frF sg e c) := by
  refine ⟨h1, h2, ?_⟩
  have hm := mass_frF sg e c
  have : 2 * ((frF sg e c).mass * (2 ^ N0.k * (2 ^ N0.b * 2 ^ N0.b))) ≤ 12 * (2 ^ N0.k * (2 ^ N0.b * 2 ^ N0.b)) := by
    nlinarith [Nat.zero_le (2 ^ N0.k * (2 ^ N0.b * 2 ^ N0.b))]
  exact this.trans h3

variable (I : Inst)

open Classical in
theorem net_value' (N0 : NPar) (w : Fin K → ℕ) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool))
    (e : Cn n ≃ Fin K)
    (hcv0 : ∀ c, 0 ≤ I.cv c) (hcvB : ∀ c, I.cv c < 2 ^ (N0.b * 2 ^ N0.k))
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hxc : ∀ i, ∀ jb ∈ xc i, jb.1 < N0.b * 2 ^ N0.k)
    (hS : ∀ c, (NP N0 w c).SizeOK (frF sg e c)) (hb : 1 ≤ N0.b) {g : ℕ}
    (eg : CG (Slot n) (UC sg e) N0.A ≃ Fin g) :
    ((((compNet (w := w) (fun c => Subtype.val) (frF sg e) (okC N0 (Cl I (N0.b * 2 ^ N0.k) sg xc))).toForced.toGNet).toNet
        eg).value) =
      (({t : IntAssign n | IOK I t ∧ SignOK I sg t ∧ XB xc t}.ncard : ℕ) : ℤ) := by
  have hC : ∀ s, ∀ jb ∈ Cl I (N0.b * 2 ^ N0.k) sg xc s, jb.1 < N0.b * 2 ^ N0.k := by
    intro s jb hjb
    cases s with
    | cst c => simp only [Cl, pinList, List.mem_map, List.mem_range] at hjb
               obtain ⟨j, hj, rfl⟩ := hjb; exact hj
    | tg i =>
      cases hg : sg i
      · simp only [Cl, hg, pinList, List.mem_map, List.mem_range] at hjb
        obtain ⟨j, hj, rfl⟩ := hjb; exact hj
      · simp [Cl, hg] at hjb
      · simp [Cl, hg] at hjb
    | v a => cases a with
      | x i => exact hxc i jb hjb
      | _ => simp [Cl] at hjb
    | sl a => simp [Cl] at hjb
    | u i => simp [Cl] at hjb
  rw [comp_value (w := w) (fun c => Subtype.val) (frF sg e) (okC N0 (Cl I (N0.b * 2 ^ N0.k) sg xc)) hS hb eg]
  congr 1
  rw [← count_corr I sg xc (N0.b * 2 ^ N0.k) hcv0 hcvB hXX e]
  exact (card_congr_pred _ _ _ _ (fun d => Iff.rfl)).trans
    (dcount_eq_V N0 (famF sg e) (Cl I (N0.b * 2 ^ N0.k) sg xc) hC)

open Classical in
/-- **Main theorem (per-identity network).**  `Net.value` of the glued per-identity network equals the number of
ordered generic factor-base decompositions `R = P_1+...+P_m` (`GenSet`) whose string has the prefix `π`. -/
theorem main_count' (I : Inst) [hpp : Fact I.p.Prime] [(shortW I.p I.a I.b).IsElliptic]
    (N0 : NPar) (w : Fin K → ℕ) (π : List Bool) (ℓ : ℕ) (hℓ : ℓ ≤ N0.b * 2 ^ N0.k)
    (hlen : π.length ≤ (n + 1) * (ℓ + 1)) (e : Cn n ≃ Fin K)
    (ha0 : 0 ≤ I.a) (ha : I.a < I.p) (hb0 : 0 ≤ I.b) (hb : I.b < I.p) (hXp : I.X ≤ I.p)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hO : 2 * (I.p : ℤ) ≤ I.O) (hN : I.O + 2 * (I.p : ℤ) < I.N)
    (hR : 0 ≤ I.R.1 ∧ I.R.1 < I.p ∧ 0 ≤ I.R.2 ∧ I.R.2 < I.p)
    (hRns : (shortW I.p I.a I.b).Nonsingular (I.R.1 : ZMod I.p) (I.R.2 : ZMod I.p))
    (hcvB : ∀ c, I.cv c < 2 ^ (N0.b * 2 ^ N0.k))
    (hS : ∀ c, (NP N0 w c).SizeOK (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e c)) (hb1 : 1 ≤ N0.b)
    {g : ℕ} (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g) :
    ((((compNet (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
        (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
          (fun i : Fin (n + 1) => xcOf ℓ π i)))).toForced.toGNet).toNet eg).value) =
      ((((GenSet (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X)
        ((I.R.1 : ZMod I.p), (I.R.2 : ZMod I.p)) n).filter
          (fun P => π <+: strOf I.p ℓ P)).card : ℕ) : ℤ) := by
  have hcv0 : ∀ c, 0 ≤ I.cv c := by
    intro c
    have hp : (0 : ℤ) ≤ I.p := by positivity
    cases c <;> simp only [Inst.cv_one, Inst.cv_cp, Inst.cv_ca, Inst.cv_cb, Inst.cv_cOp, Inst.cv_cX,
      Inst.cv_cN, Inst.cv_cRx, Inst.cv_cRy, Inst.cv_cc0, Inst.cv_cc1] <;> first | positivity | linarith [hR.1, hR.2.2.1] | exact mul_nonneg (by linarith) hp
  have hxc : ∀ i : Fin (n + 1), ∀ jb ∈ xcOf ℓ π i, jb.1 < N0.b * 2 ^ N0.k := by
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
  rw [net_value' I N0 w (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i) e hcv0 hcvB hXX
    hxc hS hb1 eg,
    ncard_int_filter I (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i)
      ha0 ha hb0 hb hXp hXX hO hN hR hRns]
  congr 2
  apply Finset.filter_congr
  intro P _
  exact (prefix_iff_QP I.p ℓ π hlen P).symm

end
end ECDLP.L54
end
