import ECDLP.L73_Asm
import ECDLP.L76_Lay2
import ECDLP.L44_Sys

/-!
# L81 / Src: the source/check gate weight expression `SrcWt` (generic in the bit-constraint oracle)

`srcE badE` is the product over the `h*b` bits `(t, bt)` of the slice of a source node of `1 - bad(jj, v)`, where
`jj = (t*A + s)*b + bt` is the global bit position in the slot, `v` the bit `bt` of digit `t` of the free value (read from the
setting code in slot `u+7` as `code / 2^(b*t+bt) % 2`), and `badE` (the oracle) is `1` iff `(jj, !v) ∈ C i`, i.e. iff the
bit constraint list of the slot `i` is violated at `jj`.  `srcWt_of_oracle` : the resulting `SrcWt` for `ok = okC N0 C`.
Slots used: `u+30, u+31` (loop variables), `u+32 = jj`, `u+33 = v`, `u+34, u+35` (power binders).
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace ECDLP.L81
open Finset Factoring.Aux Ex ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68 ECDLP.L73

/-- `2^n` by an `iter` -/
def pw2 (x y : ℕ) (n : Ex) : Ex := .iter x y n (.lit 1) (.mul (.var y) (.lit 2))

theorem eval_pw2 {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {x y : ℕ} (_hxy : x ≠ y) (n : Ex) :
    Ex.eval σ A (pw2 x y n) = 2 ^ Ex.eval σ A n := by
  simp only [pw2, Ex.eval]
  generalize Ex.eval σ A n = k
  have : ∀ j, iterF (fun j s => Ex.eval (Function.update (Function.update σ x j) y s) A
      (.mul (.var y) (.lit 2))) 1 j = 2 ^ j := by
    intro j
    induction j with
    | zero => simp [iterF]
    | succ j ih =>
      rw [iterF, ih]
      simp [Ex.eval, Function.update_self, pow_succ]
  exact this k

/-- the cell of the slice: `1 - bad(jj, v)` -/
def srcCell (u : ℕ) (badE : Ex) : Ex :=
  .lett (u + 32) (.add (.mul (.add (.mul (.var (u + 30)) (.var (u + 12))) (.var (u + 17))) (.var (u + 14))) (.var (u + 31)))
    (.lett (u + 33)
      (.mod (.div (.var (u + 7)) (pw2 (u + 34) (u + 35) (.add (.mul (.var (u + 14)) (.var (u + 30))) (.var (u + 31))))) (.lit 2))
      (.sub (.lit 1) badE))

/-- the weight expression of a source node -/
def srcE (u : ℕ) (badE : Ex) : Ex :=
  .prod (u + 30) (.var (u + 13)) (.lit 2) (.prod (u + 31) (.var (u + 14)) (.lit 2) (srcCell u badE))

theorem digit_bit (h b : ℕ) (c : ℕ) (t : ℕ) (bt : ℕ) (hbt : bt < b) :
    (c / (2 ^ b) ^ t % 2 ^ b).testBit bt = decide (c / 2 ^ (b * t + bt) % 2 = 1) := by
  rw [← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  simp [hbt, Nat.mul_comm t b, Nat.add_comm bt]


theorem foldProd_bits_lt (f : ℕ → ℕ) (j : ℕ) (hf : ∀ i < j, f i = 0 ∨ f i = 1) :
    foldProd f 2 j = if ∀ i < j, f i = 1 then 1 else 0 := by
  induction j with
  | zero => simp [foldProd]
  | succ j ih =>
    have ih := ih (fun i hi => hf i (by omega))
    rw [foldProd, ih]
    by_cases h : ∀ i < j, f i = 1
    · rcases hf j (by omega) with h0 | h1
      · have : ¬ ∀ i < j + 1, f i = 1 := fun H => by have := H j (by omega); omega
        rw [if_pos h, if_neg this, h0]
      · have : ∀ i < j + 1, f i = 1 := fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
          · exact h i h'
          · subst h'; exact h1
        rw [if_pos h, if_pos this, h1]
    · have : ¬ ∀ i < j + 1, f i = 1 := fun H => h fun i hi => H i (by omega)
      rw [if_neg h, if_neg this]; simp

/-- the environment in which the oracle is evaluated -/
def env4 (σ : ℕ → ℕ) (u t bt jj v : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update σ (u + 30) t) (u + 31) bt) (u + 32) jj) (u + 33) v

theorem eval_srcCell {A : ℕ → ℕ → ℕ} {u : ℕ} {σ : ℕ → ℕ} {badE : Ex} {b As s code : ℕ}
    (hb : σ (u + 14) = b) (hA : σ (u + 12) = As) (hs : σ (u + 17) = s)
    (hc : σ (u + 7) = code) (t bt : ℕ) :
    Ex.eval (Function.update (Function.update σ (u + 30) t) (u + 31) bt) A (srcCell u badE) =
      1 - Ex.eval (env4 σ u t bt ((t * As + s) * b + bt) (code / 2 ^ (b * t + bt) % 2)) A badE := by
  simp only [srcCell, Ex.eval, eval_pw2 (show u + 34 ≠ u + 35 by omega)]
  simp [env4, Function.update_apply, hb, hA, hs, hc]

theorem ite_one_iff (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) = 1 ↔ P := by
  split_ifs with h <;> simp [h]

open Classical in
theorem eval_srcE {A : ℕ → ℕ → ℕ} {u : ℕ} {σ : ℕ → ℕ} {badE : Ex} {h b As s code : ℕ}
    (hh : σ (u + 13) = h) (hb : σ (u + 14) = b) (hA : σ (u + 12) = As) (hs : σ (u + 17) = s)
    (hc : σ (u + 7) = code) (bd : ℕ → ℕ → Prop)
    (hbad : ∀ t < h, ∀ bt < b, Ex.eval (env4 σ u t bt ((t * As + s) * b + bt) (code / 2 ^ (b * t + bt) % 2)) A badE =
      if bd t bt then 1 else 0) :
    Ex.eval σ A (srcE u badE) = if ∀ t < h, ∀ bt < b, ¬ bd t bt then 1 else 0 := by
  have inner : ∀ t < h, Ex.eval (Function.update σ (u + 30) t) A
      (.prod (u + 31) (.var (u + 14)) (.lit 2) (srcCell u badE)) = if ∀ bt < b, ¬ bd t bt then 1 else 0 := by
    intro t ht
    set σ1 := Function.update σ (u + 30) t with h1
    have hb1 : σ1 (u + 14) = b := by rw [h1, Function.update_of_ne (by omega)]; exact hb
    change foldProd (fun bt => Ex.eval (Function.update σ1 (u + 31) bt) A (srcCell u badE)) 2 (σ1 (u + 14)) = _
    rw [hb1]
    have hcell : ∀ bt < b, Ex.eval (Function.update σ1 (u + 31) bt) A (srcCell u badE) =
        if bd t bt then 0 else 1 := by
      intro bt hbt
      rw [h1, eval_srcCell hb hA hs hc, hbad t ht bt hbt]
      split_ifs <;> simp
    rw [foldProd_bits_lt]
    · congr 1
      apply propext
      refine forall₂_congr fun bt hbt => ?_
      rw [hcell bt hbt]
      by_cases hp : bd t bt <;> simp [hp]
    · intro bt hbt
      rw [hcell bt hbt]
      split_ifs <;> simp
  unfold srcE
  change foldProd (fun t => Ex.eval (Function.update σ (u + 30) t) A
      (.prod (u + 31) (.var (u + 14)) (.lit 2) (srcCell u badE))) 2 (σ (u + 13)) = _
  rw [hh]
  rw [foldProd_bits_lt]
  · congr 1
    apply propext
    refine forall₂_congr fun t ht => ?_
    rw [inner t ht]
    exact ite_one_iff (∀ bt < b, ¬ bd t bt)
  · intro t ht
    rw [inner t ht]
    split_ifs <;> simp


/-! ### value bounds -/

theorem iter_pow2 (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (x y : ℕ) (j : ℕ) :
    iterF (fun j s => Ex.eval (Function.update (Function.update σ x j) y s) A (.mul (.var y) (.lit 2))) 1 j = 2 ^ j := by
  induction j with
  | zero => simp [iterF]
  | succ j ih =>
    rw [iterF, ih]
    simp [Ex.eval, Function.update_self, pow_succ]

theorem bdd_pw2 {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {x y : ℕ} (n : Ex) (hn : Bdd V σ A n)
    (hV : 2 ^ Ex.eval σ A n ≤ V) (h2 : 2 ≤ V) : Bdd V σ A (pw2 x y n) := by
  simp only [pw2, Bdd]
  refine ⟨hn, (show 1 ≤ V by omega), fun j hj => ?_⟩
  have e1 : Ex.eval σ A (.lit 1) = 1 := rfl
  rw [e1, iter_pow2]
  have h3 : 2 ^ (j + 1) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) hj) hV
  have h4 : 2 ^ j ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h3
  rw [pow_succ] at h3
  simp only [Bdd, Ex.eval, Function.update_self]
  exact ⟨h4, h2, h3⟩

theorem bdd_srcCell {V : ℕ} {A : ℕ → ℕ → ℕ} {u : ℕ} {σ : ℕ → ℕ} {badE : Ex} {h b As s code : ℕ}
    (hb : σ (u + 14) = b) (hA : σ (u + 12) = As) (hs : σ (u + 17) = s) (hc : σ (u + 7) = code)
    (h2 : 2 ≤ V) (hcV : code ≤ V) (hjj : h * As * b ≤ V) (hpw : 2 ^ (b * h) ≤ V)
    (t bt : ℕ) (ht : t < h) (hbt : bt < b) (hsA : s < As)
    (hbad : Bdd V (env4 σ u t bt ((t * As + s) * b + bt) (code / 2 ^ (b * t + bt) % 2)) A badE) :
    Bdd V (Function.update (Function.update σ (u + 30) t) (u + 31) bt) A (srcCell u badE) := by
  have hbpos : 1 ≤ b := by omega
  have hj : (t * As + s) * b + bt < h * As * b := by
    have : (t * As + s + 1) * b ≤ h * As * b := Nat.mul_le_mul_right _ (by nlinarith)
    nlinarith
  have hjV : (t * As + s) * b + bt ≤ V := by omega
  have h1 : (t * As + s) * b ≤ V := by omega
  have h3 : t * As + s ≤ V := le_trans (Nat.le_mul_of_pos_right _ hbpos) h1
  have h4 : t * As ≤ V := by omega
  have hbt' : b * t + bt ≤ b * h := by nlinarith
  have hpw' : 2 ^ (b * t + bt) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) hbt') hpw
  have hApos : 0 < As := by omega
  have hhpos : 0 < h := by omega
  have e1 : h ≤ h * As * b := by
    calc h = h * 1 * 1 := by ring
      _ ≤ h * As * b := Nat.mul_le_mul (Nat.mul_le_mul_left h hApos) hbpos
  have e2 : As ≤ h * As * b := by
    calc As = 1 * As * 1 := by ring
      _ ≤ h * As * b := Nat.mul_le_mul (Nat.mul_le_mul_right As hhpos) hbpos
  have e3 : b ≤ h * As * b := Nat.le_mul_of_pos_left b (Nat.mul_pos hhpos hApos)
  have hbV : b ≤ V := by omega
  have htV : t ≤ V := by omega
  have hbtV : bt ≤ V := by omega
  have hbtv : b * t + bt ≤ V := le_trans hbt' (le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) hpw)
  have hbt0 : b * t ≤ V := by omega
  have hAV : As ≤ V := by omega
  have hsV : s ≤ V := by omega
  simp only [srcCell, Bdd, Ex.eval]
  have e30 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 30) = t := by
    simp [Function.update_apply]
  have e31 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 31) = bt := by
    simp [Function.update_apply]
  have e12 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 12) = As := by
    simp [Function.update_apply, hA]
  have e17 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 17) = s := by
    simp [Function.update_apply, hs]
  have e14 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 14) = b := by
    simp [Function.update_apply, hb]
  have e7 : Function.update (Function.update σ (u + 30) t) (u + 31) bt (u + 7) = code := by
    simp [Function.update_apply, hc]
  simp only [e30, e31, e12, e17, e14]
  refine ⟨⟨⟨⟨⟨htV, hAV, h4⟩, hsV, h3⟩, hbV, h1⟩, hbtV, hjV⟩, ?_⟩
  set σ3 := Function.update (Function.update (Function.update σ (u + 30) t) (u + 31) bt) (u + 32)
    ((t * As + s) * b + bt) with hσ3
  have g7 : σ3 (u + 7) = code := by simp [hσ3, Function.update_apply, hc]
  have g14 : σ3 (u + 14) = b := by simp [hσ3, Function.update_apply, hb]
  have g30 : σ3 (u + 30) = t := by simp [hσ3, Function.update_apply]
  have g31 : σ3 (u + 31) = bt := by simp [hσ3, Function.update_apply]
  have hn : Ex.eval σ3 A (.add (.mul (.var (u + 14)) (.var (u + 30))) (.var (u + 31))) = b * t + bt := by
    simp [Ex.eval, g14, g30, g31]
  have hnB : Bdd V σ3 A (.add (.mul (.var (u + 14)) (.var (u + 30))) (.var (u + 31))) := by
    simp only [Bdd, Ex.eval, g14, g30, g31]
    exact ⟨⟨hbV, htV, hbt0⟩, hbtV, hbtv⟩
  have hpB := bdd_pw2 (x := u + 34) (y := u + 35) _ hnB (by rw [hn]; exact hpw') h2
  have hev := eval_pw2 (σ := σ3) (A := A) (x := u + 34) (y := u + 35) (by omega)
    (.add (.mul (.var (u + 14)) (.var (u + 30))) (.var (u + 31)))
  rw [hn] at hev
  rw [g7, hev]
  refine ⟨⟨⟨hcV, hpB⟩, h2⟩, by omega, ?_⟩
  exact hbad

/-- **Value bound of the source weight expression** (all intermediate values `<= V`) from the bound of the oracle. -/
theorem bdd_srcE {V : ℕ} {A : ℕ → ℕ → ℕ} {u : ℕ} {σ : ℕ → ℕ} {badE : Ex} {h b As s code : ℕ}
    (hh : σ (u + 13) = h) (hb : σ (u + 14) = b) (hA : σ (u + 12) = As) (hs : σ (u + 17) = s)
    (hc : σ (u + 7) = code) (hsA : s < As)
    (h2 : 2 ≤ V) (hcV : code ≤ V) (hjj : h * As * b ≤ V) (hpw : 2 ^ (b * h) ≤ V) (hhV : h ≤ V) (hbV : b ≤ V)
    (hbad : ∀ t < h, ∀ bt < b,
      Bdd V (env4 σ u t bt ((t * As + s) * b + bt) (code / 2 ^ (b * t + bt) % 2)) A badE) :
    Bdd V σ A (srcE u badE) := by
  have hf : ∀ (f : ℕ → ℕ) (j : ℕ), foldProd f 2 j ≤ V := fun f j =>
    le_trans (by cases j with
      | zero => simp [foldProd]
      | succ j => rw [foldProd]; omega) (show 1 ≤ V by omega)
  simp only [srcE, Bdd, Ex.eval, hh]
  refine ⟨hhV, h2, fun t ht => ?_, fun j _ => hf _ j⟩
  have hb1 : Function.update σ (u + 30) t (u + 14) = b := by simp [Function.update_apply, hb]
  simp only [Bdd, Ex.eval, hb1]
  refine ⟨hbV, h2, fun bt hbt => ?_, fun j _ => hf _ j⟩
  exact bdd_srcCell hb hA hs hc h2 hcV hjj hpw t bt ht hbt hsA (hbad t ht bt hbt)

/-! ### the semantic lemma: `okC` as a product of oracle cells -/

theorem pos_div_mod (t s As b bt : ℕ) (hs : s < As) (hbt : bt < b) :
    ((t * As + s) * b + bt) / b % As = s ∧ ((t * As + s) * b + bt) / b / As = t ∧ ((t * As + s) * b + bt) % b = bt := by
  have hb : 0 < b := by omega
  have hA : 0 < As := by omega
  have e1 : ((t * As + s) * b + bt) / b = t * As + s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hbt, zero_add]
  have e2 : ((t * As + s) * b + bt) % b = bt := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbt]
  refine ⟨?_, ?_, e2⟩
  · rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · rw [e1, Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hs, zero_add]

theorem pos_inv (jj b As : ℕ) (hb : 0 < b) (hA : 0 < As) :
    ((jj / b / As) * As + jj / b % As) * b + jj % b = jj := by
  rw [Nat.mul_comm (jj / b / As) As, Nat.div_add_mod (jj / b) As, Nat.mul_comm (jj / b) b, Nat.div_add_mod jj b]


open Classical in
/-- `okC` as the absence of violated oracle cells -/
theorem okC_iff_cells {N0 : NPar} {ι : Type} (C : ι → List (ℕ × Bool)) (i : ι) (s : Fin N0.A) (d : Dg N0) (code : ℕ)
    (hb0 : 0 < N0.b)
    (hd : ∀ t : Fin N0.h, (d t : ℕ) = code / (2 ^ N0.b) ^ (t : ℕ) % 2 ^ N0.b) :
    okC N0 C i s d ↔ ∀ t < N0.h, ∀ bt < N0.b,
      ¬ ((((t * N0.A + s) * N0.b + bt), decide (code / 2 ^ (N0.b * t + bt) % 2 = 0)) ∈ C i) := by
  have hA0 : 0 < N0.A := s.pos
  have hv : ∀ k, code / 2 ^ k % 2 = 0 ∨ code / 2 ^ k % 2 = 1 := fun k => by omega
  constructor
  · intro hok t ht bt hbt hmem
    obtain ⟨e1, e2, e3⟩ := pos_div_mod t s N0.A N0.b bt s.2 hbt
    have := hok _ hmem e1 (by simp only [e2]; exact ht)
    simp only [hd, e2, e3] at this
    rw [digit_bit N0.h N0.b code t bt hbt] at this
    rcases hv (N0.b * t + bt) with h0 | h1
    · simp [h0] at this
    · simp [h1] at this
  · intro hcell ⟨j0, b0⟩ hjb h1 h2
    simp only at h1 h2
    set t := j0 / N0.b / N0.A with ht
    set bt := j0 % N0.b with hbt
    have hbt' : bt < N0.b := Nat.mod_lt _ hb0
    by_contra hne
    apply hcell t h2 bt hbt'
    have hjj : (t * N0.A + s) * N0.b + bt = j0 := by
      have := pos_inv j0 N0.b N0.A hb0 hA0
      rw [h1] at this
      exact this
    have hx : ((d ⟨t, h2⟩ : Fin _) : ℕ).testBit bt = decide (code / 2 ^ (N0.b * t + bt) % 2 = 1) := by
      rw [hd ⟨t, h2⟩]
      exact digit_bit N0.h N0.b code t bt hbt'
    rw [hx] at hne
    have : decide (code / 2 ^ (N0.b * t + bt) % 2 = 0) = b0 := by
      rcases hv (N0.b * t + bt) with h0 | h1'
      · rw [h0] at hne ⊢
        cases b0 <;> simp at hne ⊢
      · rw [h1'] at hne ⊢
        cases b0 <;> simp at hne ⊢
    rw [hjj, this]
    exact hjb


/-! ### the `SrcWt` instance -/

section inst
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  {L : Lay ι ιc} {u : ℕ} {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {m : ℕ}

open Classical in
theorem W_src_q (ok : ι → Fin N0.A → Dg N0 → Prop) (hm1 : 1 < m) (i : ι) (s : Fin N0.A) (q : CG ι ιc N0.A)
    (hq : q = CG.src i s) (z : (edgeNetM (w := w) φ F ok m).S q) :
    ∃ d : Dg N0, ((edgeEFM φ F ok m q z.1 : Fin _) : ℕ) = ((dCode N0.h N0.b d : Fin _) : ℕ) ∧
      ((edgeNetM (w := w) φ F ok m).W q z = 1 ↔ ok i s d) := by
  subst hq
  haveI : Fact (1 < m) := ⟨hm1⟩
  refine ⟨z.1, rfl, ?_⟩
  show (Int.castRingHom (ZMod m)) (if ok i s z.1 then 1 else 0) = 1 ↔ _
  by_cases h : ok i s z.1
  · simp [h]
  · simp [h]

/-- **`SrcWt` for `ok = okC N0 C`** from a bit-constraint oracle `badE` (`1` iff the constraint list is violated at the
position, given the bit value in slot `u+33`). -/
def srcWt (C : ι → List (ℕ × Bool)) (badE : Ex) (hm1 : 1 < m) (hu : B ≤ u) (hb0 : 0 < N0.b)
    (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F (okC N0 C) m) (L.enum N0.A) u)
    (hbad : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ (i : ι) (jj v : ℕ), σ (u + 16) = L.eι i → σ (u + 32) = jj →
      σ (u + 33) = v → v ≤ 1 → Ex.eval σ A badE = if (jj, decide (v = 0)) ∈ C i then 1 else 0) :
    SrcWt (w := w) X where
  srcE := srcE u badE
  hsrc := by
    classical
    intro σ₀ hC σ hσ a i s z hq h4 h7 h10 h12 h13 h14 h16 h17
    obtain ⟨d, hd1, hd2⟩ := W_src_q (w := w) (φ := φ) (F := F) (okC N0 C) hm1 i s _ hq z
    have hzc := zcode_noparent (w := w) φ F (okC N0 C) m (L.enum N0.A) a
      (by show paC φ _ = ∅; rw [hq]; simp [paC]) z
    have hcode : σ (u + 7) = ((dCode N0.h N0.b d : Fin _) : ℕ) := by rw [h7, hzc, hd1]
    have hdig : ∀ t : Fin N0.h, (d t : ℕ) = σ (u + 7) / (2 ^ N0.b) ^ (t : ℕ) % 2 ^ N0.b := by
      intro t
      rw [hcode, ← dCode_digit]
      simp
    have key := okC_iff_cells C i s d (σ (u + 7)) hb0 hdig
    rw [if_congr hd2 rfl rfl]
    rw [eval_srcE (As := N0.A) (s := (s : ℕ)) (h := N0.h) (b := N0.b) (code := σ (u + 7)) h13 h14 h12 h17 rfl
      (fun t bt => ((t * N0.A + (s : ℕ)) * N0.b + bt, decide (σ (u + 7) / 2 ^ (N0.b * t + bt) % 2 = 0)) ∈ C i)]
    · simp only [← key]
    · intro t ht bt hbt
      have g := hσ
      have g4 : Ag B σ₀ (env4 σ u t bt ((t * N0.A + s) * N0.b + bt) (σ (u + 7) / 2 ^ (N0.b * t + bt) % 2)) := by
        unfold env4
        exact (((g.upd (by omega) _).upd (by omega) _).upd (by omega) _).upd (by omega) _
      have := hbad σ₀ hC _ g4 i ((t * N0.A + s) * N0.b + bt) (σ (u + 7) / 2 ^ (N0.b * t + bt) % 2)
        (by simp [env4, Function.update_apply, h16]) (by simp [env4])
        (by simp [env4, Function.update_apply]) (by omega)
      rw [this]
      split_ifs <;> simp_all

end inst
end ECDLP.L81
