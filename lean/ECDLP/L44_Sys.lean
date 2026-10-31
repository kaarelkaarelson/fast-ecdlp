import ECDLP.L44_Value

/-!
# L44 / Sys: `system_value` stated on slot values

`system_value_V`: the value of L38's combined network (with bit-constraint checks `okC`) is the number of
valuations `V : ι → Fin (2^(b 2^k))` satisfying the bit constraints and all identities `HV (F c) V = 0`.
-/
noncomputable section
namespace ECDLP.L44
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38

section
variable {ι : Type} (N : NPar)

theorem idx_lt (s : Fin N.A) (i' : Fin N.h) : (s : ℕ) + N.A * i' < 2 ^ N.k := by
  rw [← N.hAh]
  calc (s : ℕ) + N.A * i' < N.A + N.A * i' := by have := s.2; omega
    _ = N.A * (i' + 1) := by ring
    _ ≤ N.A * N.h := Nat.mul_le_mul_left _ i'.2

theorem mod_lt' (m : Fin (2 ^ N.k)) : (m : ℕ) % N.A < N.A := Nat.mod_lt _ N.toPar.A_pos

theorem div_lt' (m : Fin (2 ^ N.k)) : (m : ℕ) / N.A < N.h :=
  Nat.div_lt_of_lt_mul (by rw [N.hAh]; exact m.2)

/-- one slot: slices ↔ digit vector -/
def sliceEquiv : (Fin N.A → Fin N.h → Fin (2 ^ N.b)) ≃ (Fin (2 ^ N.k) → Fin (2 ^ N.b)) where
  toFun d m := d ⟨m % N.A, mod_lt' N m⟩ ⟨m / N.A, div_lt' N m⟩
  invFun u s i' := u ⟨s + N.A * i', idx_lt N s i'⟩
  left_inv d := by
    funext s i'
    have hA0 := N.toPar.A_pos
    have e1 : ((s : ℕ) + N.A * i') % N.A = s := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.2]
    have e2 : ((s : ℕ) + N.A * i') / N.A = i' := by
      rw [Nat.add_mul_div_left _ _ hA0, Nat.div_eq_of_lt s.2]; simp
    simp only
    congr 2 <;> apply Fin.ext <;> simp [e1, e2]
  right_inv u := by
    funext m
    have hA0 := N.toPar.A_pos
    simp only
    congr 1
    apply Fin.ext
    simp only
    have := Nat.mod_add_div (m : ℕ) N.A
    omega

theorem sliceEquiv_apply (d : Fin N.A → Fin N.h → Fin (2 ^ N.b)) (m : Fin (2 ^ N.k)) :
    sliceEquiv N d m = d ⟨m % N.A, mod_lt' N m⟩ ⟨m / N.A, div_lt' N m⟩ := rfl

/-- digit vector ↔ value -/
def valEquiv : (Fin (2 ^ N.k) → Fin (2 ^ N.b)) ≃ Fin (2 ^ (N.b * 2 ^ N.k)) :=
  Equiv.ofBijective (fun u => ⟨vl N u, vl_lt N u⟩)
    ⟨fun u u' h => vl_inj N (by simpa using congrArg Fin.val h),
     fun v => by
       obtain ⟨u, hu⟩ := vl_surj N v.1 v.2
       exact ⟨u, Fin.ext hu⟩⟩

variable [Fintype ι] [DecidableEq ι]

/-- value of slot `i` of a digit assignment -/
def sv (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) : ℕ := vl N (N.dgOf d i)

/-- all slots at once -/
def slotEquiv : (ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) ≃ (ι → Fin (2 ^ (N.b * 2 ^ N.k))) :=
  Equiv.piCongrRight fun _ => (sliceEquiv N).trans (valEquiv N)

theorem slotEquiv_val (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) :
    ((slotEquiv N d i : Fin _) : ℕ) = sv N d i := rfl

/-- bit-constraint checks on FA gates -/
def okC (C : ι → List (ℕ × Bool)) (i : ι) (s : Fin N.A) (u : Fin N.h → Fin (2 ^ N.b)) : Prop :=
  ∀ jb ∈ C i, jb.1 / N.b % N.A = s.val → ∀ h : jb.1 / N.b / N.A < N.h,
    ((u ⟨_, h⟩ : Fin (2 ^ N.b)) : ℕ).testBit (jb.1 % N.b) = jb.2

theorem okC_iff (C : ι → List (ℕ × Bool)) (hC : ∀ i, ∀ jb ∈ C i, jb.1 < N.b * 2 ^ N.k)
    (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) :
    (∀ s, okC N C i s (d i s)) ↔ ∀ jb ∈ C i, (sv N d i).testBit jb.1 = jb.2 := by
  constructor
  · intro h jb hjb
    have hj := hC i jb hjb
    have hb : 0 < N.b := b_pos N hj
    have hm : jb.1 / N.b < 2 ^ N.k := (Nat.div_lt_iff_lt_mul hb).2 (by linarith)
    unfold sv
    rw [testBit_vl N _ jb.1 hj]
    have := h ⟨(jb.1 / N.b) % N.A, mod_lt' N ⟨_, hm⟩⟩ jb hjb rfl (div_lt' N ⟨_, hm⟩)
    exact this
  · intro h s jb hjb hs hh
    have hj := hC i jb hjb
    have hb : 0 < N.b := b_pos N hj
    have hm : jb.1 / N.b < 2 ^ N.k := (Nat.div_lt_iff_lt_mul hb).2 (by linarith)
    have h1 := h jb hjb
    unfold sv at h1
    rw [testBit_vl N _ jb.1 hj] at h1
    rw [← h1]
    have : s = ⟨(jb.1 / N.b) % N.A, mod_lt' N ⟨_, hm⟩⟩ := Fin.ext hs.symm
    subst this
    rfl

/-- value of a form on a valuation -/
def HV (F : Form ι) (V : ι → ℕ) : ℤ := ∑ t : Fin F.n, F.ε t * ((V (F.l t) : ℤ) * (V (F.r t) : ℤ))

variable {K : ℕ}

open Classical in
/-- **L38's `system_value` on slot values.** -/
theorem system_value_V (F : Fin K → Form ι) (C : ι → List (ℕ × Bool))
    (hC : ∀ i, ∀ jb ∈ C i, jb.1 < N.b * 2 ^ N.k) (B : ℤ) (hB : 0 < B)
    (hBd : ∀ c, ((F c).mass : ℤ) * ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B)
    (hS : N.SizeOK (combine F B)) (hb : 1 ≤ N.b) {g : ℕ} (e : Gate ι N.A ≃ Fin g) :
    (((gadgetNet N (combine F B) (okC N C)).toForced.toGNet).toNet e).value =
      ((univ.filter fun V : ι → Fin (2 ^ (N.b * 2 ^ N.k)) =>
        (∀ i, ∀ jb ∈ C i, ((V i : Fin _) : ℕ).testBit jb.1 = jb.2) ∧
          ∀ c, HV (F c) (fun i => ((V i : Fin _) : ℕ)) = 0).card : ℤ) := by
  rw [system_value N F (okC N C) B hB hBd hS hb e]
  congr 1
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
end ECDLP.L44
end

#print axioms ECDLP.L44.system_value_V
