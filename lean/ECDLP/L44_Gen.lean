import ECDLP.L44_Net

/-!
# L44 / Gen: from `IntOK` solutions with sign/bit constraints to generic decompositions with a prefix predicate

* `card_sol_eq_card_gen_filter`: L30's field-level bijection `t ↦ t.1` (`SolSet → GenSet`), restricted to a predicate
  `Q` on the point tuple (the proof of L30's `card_sol_eq_card_gen` with a filter).
* `ncard_int_filter`: the integer-level count with `SignOK`/`XB` equals the filtered generic count.
-/
namespace ECDLP.L44
open ECDLP.L30 WeierstrassCurve WeierstrassCurve.Affine

section field
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

theorem card_sol_eq_card_gen_filter [Fintype F] (FB : F → Prop) {R : F × F}
    (hR : W.Nonsingular R.1 R.2) (n : ℕ) (Q : (Fin (n + 1) → F × F) → Prop) [DecidablePred Q] :
    ((SolSet W FB R n).filter (fun t => Q t.1)).card = ((GenSet W FB R n).filter Q).card := by
  classical
  apply Finset.card_bij (fun t _ => t.1)
  · intro t ht0
    obtain ⟨ht, hq⟩ := Finset.mem_filter.1 ht0
    rw [Finset.mem_filter]
    refine ⟨?_, hq⟩
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨hns, hc⟩ := ht
    simp only [GenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hns, ?_⟩
    have hns' := nat_ns W (fun i => (hns i).1)
    obtain ⟨hch, hn⟩ := (constraints_iff W _ _ _ _ _).1 hc
    refine ⟨(genericF_iff W _).2 (chain_generic hns' hch), ?_⟩
    have := (chain_iff (n := n) (R := R) hns' hR).1 ⟨_, _, _, hch, hn⟩
    rw [psumF_eq]
    simpa using this.2
  · intro t ht0 t' ht0' h
    have ht := (Finset.mem_filter.1 ht0).1
    have ht' := (Finset.mem_filter.1 ht0').1
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    obtain ⟨hns, hc⟩ := ht
    obtain ⟨hns2, hc'⟩ := ht'
    obtain ⟨P, S, w, l⟩ := t
    obtain ⟨P', S', w', l'⟩ := t'
    change P = P' at h
    subst h
    have hns' := nat_ns W (fun i => (hns i).1)
    obtain ⟨hch, -⟩ := (constraints_iff W _ _ _ _ _).1 hc
    obtain ⟨hch', -⟩ := (constraints_iff W _ _ _ _ _).1 hc'
    obtain ⟨u1, u2⟩ := chain_unique hns' hch hch'
    have hS : S = S' := by
      funext i
      have := u1 i (by have := i.isLt; omega)
      simpa [ext_apply] using this
    have hw : w = w' := by
      funext k
      have := (u2 k k.isLt).1
      simpa [ext_apply] using this
    have hl : l = l' := by
      funext k
      have := (u2 k k.isLt).2
      simpa [ext_apply] using this
    subst hS hw hl
    rfl
  · intro P hP0
    obtain ⟨hP, hq⟩ := Finset.mem_filter.1 hP0
    simp only [GenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨hns, hg, hsum⟩ := hP
    have hns' := nat_ns W (fun i => (hns i).1)
    have hG := (genericF_iff W P).1 hg
    have hch := chain_complete hns' hG
    refine ⟨(P, fun i => canS W (ext P) i, fun k => canW W (ext P) k,
      fun k => canL W (ext P) k), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hq⟩
    simp only [SolSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hns, ?_⟩
    rw [constraints_iff]
    refine ⟨?_, ?_⟩
    · refine ((chain_congr_iff W (n := n) ?_ ?_ ?_).2 hch)
      · intro k hk
        simp [ext, show k < n + 1 by omega]
      · intro k hk
        simp [ext, hk]
      · intro k hk
        simp [ext, hk]
    · have : ext (fun i : Fin (n + 1) => canS W (ext P) i) n = canS W (ext P) n := by
        simp [ext]
      rw [this]
      simp only [canS]
      have h3 := psumF_eq W P (Fin.last n)
      rw [hsum, Fin.val_last] at h3
      rw [← h3]
      exact coord_ptOf hR

end field

/-- sign requirement on the value of `y` -/
def SgN (p : ℕ) : Sg → ℕ → Prop
  | .none, _ => True
  | .pos, y => (p - 1) / 2 < y
  | .neg, y => y ≤ (p - 1) / 2

/-- prefix predicate on a tuple of points over `ZMod p` -/
def QP {n : ℕ} (p : ℕ) (xc : Fin (n + 1) → List (ℕ × Bool)) (sg : Fin (n + 1) → Sg)
    (P : Fin (n + 1) → ZMod p × ZMod p) : Prop :=
  ∀ i, (∀ jb ∈ xc i, ((P i).1.val).testBit jb.1 = jb.2) ∧ SgN p (sg i) (P i).2.val

section main
variable {n : ℕ} (I : Inst) [hpp : Fact I.p.Prime]

theorem val_cast {z : ℤ} (h0 : 0 ≤ z) (h : z < I.p) : ((z : ZMod I.p)).val = z.toNat := by
  have := lift_of_range (p := I.p) h0 h
  simp only [lift] at this
  omega

theorem q_iff (hXp : I.X ≤ I.p) (sg : Fin (n + 1) → Sg) (xc : Fin (n + 1) → List (ℕ × Bool))
    (t : IntAssign n) (h : IOK I t) :
    (SignOK I sg t ∧ XB xc t) ↔ QP I.p xc sg (toSol (p := I.p) t).1 := by
  have hr := h.1
  have hx : ∀ i, ((((t.P i).1 : ℤ) : ZMod I.p)).val = (t.P i).1.toNat := fun i =>
    val_cast I (hr i).1 (lt_of_lt_of_le (hr i).2.1 (by exact_mod_cast hXp))
  have hy : ∀ i, ((((t.P i).2 : ℤ) : ZMod I.p)).val = (t.P i).2.toNat := fun i =>
    val_cast I (hr i).2.2.1 (hr i).2.2.2
  have hsg : ∀ i, SgP I (sg i) (t.P i).2 ↔ SgN I.p (sg i) (t.P i).2.toNat := by
    intro i
    have h0 := (hr i).2.2.1
    cases hg : sg i
    · simp [SgP, SgN]
    · simp only [SgP, SgN, Inst.cv_cc1]; omega
    · simp only [SgP, SgN, Inst.cv_cc0]; omega
  constructor
  · rintro ⟨hs, hxb⟩ i
    refine ⟨fun jb hjb => ?_, ?_⟩
    · show ((((t.P i).1 : ℤ) : ZMod I.p)).val.testBit jb.1 = jb.2
      rw [hx i]; exact hxb i jb hjb
    · show SgN I.p (sg i) ((((t.P i).2 : ℤ) : ZMod I.p)).val
      rw [hy i]; exact (hsg i).1 (hs i)
  · intro hq
    refine ⟨fun i => (hsg i).2 ?_, fun i jb hjb => ?_⟩
    · have := (hq i).2
      change SgN I.p (sg i) ((((t.P i).2 : ℤ) : ZMod I.p)).val at this
      rwa [hy i] at this
    · have := (hq i).1 jb hjb
      change ((((t.P i).1 : ℤ) : ZMod I.p)).val.testBit jb.1 = jb.2 at this
      rwa [hx i] at this

open Classical in
theorem ncard_int_filter [(shortW I.p I.a I.b).IsElliptic] (sg : Fin (n + 1) → Sg)
    (xc : Fin (n + 1) → List (ℕ × Bool))
    (ha0 : 0 ≤ I.a) (ha : I.a < I.p) (hb0 : 0 ≤ I.b) (hb : I.b < I.p) (hXp : I.X ≤ I.p)
    (hXX : ∀ x : ℤ, 0 ≤ x → x < I.X → x * x ≤ I.p)
    (hO : 2 * (I.p : ℤ) ≤ I.O) (hN : I.O + 2 * (I.p : ℤ) < I.N)
    (hR : 0 ≤ I.R.1 ∧ I.R.1 < I.p ∧ 0 ≤ I.R.2 ∧ I.R.2 < I.p)
    (hRns : (shortW I.p I.a I.b).Nonsingular (I.R.1 : ZMod I.p) (I.R.2 : ZMod I.p)) :
    {t : IntAssign n | IOK I t ∧ SignOK I sg t ∧ XB xc t}.ncard =
      ((GenSet (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X)
        ((I.R.1 : ZMod I.p), (I.R.2 : ZMod I.p)) n).filter (QP I.p xc sg)).card := by
  rw [← card_sol_eq_card_gen_filter (shortW I.p I.a I.b) (fun x : ZMod I.p => x.val < I.X) hRns n
    (QP I.p xc sg), ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun t _ => toSol (p := I.p) t)
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨toSol_mem hXp t ht.1, (q_iff I hXp sg xc t ht.1).1 ht.2⟩
  · intro t t' ht ht' h
    exact toSol_inj hpp.out.pos hXp ht.1 ht'.1 h
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs
    obtain ⟨t, ht, e⟩ := toSol_surj ha0 ha hb0 hb hXX hO hN hR s hs.1
    refine ⟨t, ⟨ht, (q_iff I hXp sg xc t ht).2 (by rw [e]; exact hs.2)⟩, e⟩

end main
end ECDLP.L44
