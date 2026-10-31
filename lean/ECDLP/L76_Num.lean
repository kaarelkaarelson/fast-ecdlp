import ECDLP.L71_Shift
import FactoringAux.DriverMath

/-!
# L76 / Num: the bit-array number representation and the ripple-carry adder `addC`

A *big number* of width `n` in array `f` is `numCells f 1 n = ∑_{j<n} [f (1+j) ≠ 0] 2^j` (cells `1..n`, little endian,
nonzero = 1; this is the representation of L63's `Reads`).  The global width is read from scalar `710`.
Scratch scalars of `addC`: `720 .. 729`.
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- value of cells `1..n` -/
abbrev V (f : ℕ → ℕ) (n : ℕ) : ℕ := numCells f 1 n

/-- the bit of a cell -/
def bt (f : ℕ → ℕ) (i : ℕ) : ℕ := if f i = 0 then 0 else 1

theorem bt_le (f : ℕ → ℕ) (i : ℕ) : bt f i ≤ 1 := by unfold bt; split_ifs <;> omega

theorem V_snoc (f : ℕ → ℕ) (n : ℕ) : V f (n + 1) = V f n + bt f (n + 1) * 2 ^ n := by
  unfold V numCells
  rw [Finset.sum_range_succ]
  simp only [bt, Nat.add_comm 1 n]

theorem V_lt (f : ℕ → ℕ) (n : ℕ) : V f n < 2 ^ n := numCells_lt f 1 n

theorem V_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ j, 1 ≤ j → j ≤ n → f j = g j) : V f n = V g n :=
  numCells_congr fun j h1 h2 => h j h1 (by omega)

theorem V_congr_bt {f g : ℕ → ℕ} {n : ℕ} (h : ∀ j, 1 ≤ j → j ≤ n → bt f j = bt g j) : V f n = V g n := by
  induction n with
  | zero => simp [V, numCells]
  | succ n ih => rw [V_snoc, V_snoc, ih (fun j a b => h j a (by omega)), h (n + 1) (by omega) le_rfl]

theorem bt_bt (f : ℕ → ℕ) (i : ℕ) : bt (fun _ => bt f i) 0 = bt f i := by
  unfold bt; split_ifs <;> simp_all

/-- the cells `1..n` are bits; cells outside are those of `g` -/
def Cells (n : ℕ) (f g : ℕ → ℕ) : Prop :=
  ∀ i, (1 ≤ i ∧ i ≤ n → f i ≤ 1) ∧ (¬ (1 ≤ i ∧ i ≤ n) → f i = g i)

/-- scalars outside `Z` are unchanged -/
def ScKeep (Z : ℕ → Prop) (s t : St) : Prop := ∀ y, ¬ Z y → t.sc y = s.sc y

/-- arrays other than `d` are unchanged -/
def ArKeep (d : ℕ) (s t : St) : Prop := ∀ a, a ≠ d → t.ar a = s.ar a


/-! ### the ripple-carry adder / subtracter -/

/-- the (possibly complemented) bit -/
def bs (neg : Bool) (f : ℕ → ℕ) (i : ℕ) : ℕ := if neg then 1 - bt f i else bt f i

theorem bs_le (neg : Bool) (f : ℕ → ℕ) (i : ℕ) : bs neg f i ≤ 1 := by
  unfold bs; have := bt_le f i; split_ifs <;> omega

/-- value of the (complemented) bits `1..n` -/
def Wn (neg : Bool) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Wn neg f n + bs neg f (n + 1) * 2 ^ n

theorem Wn_false (f : ℕ → ℕ) (n : ℕ) : Wn false f n = V f n := by
  induction n with
  | zero => simp [Wn, V, numCells]
  | succ n ih => rw [Wn, ih, V_snoc]; simp [bs]

theorem Wn_true (f : ℕ → ℕ) (n : ℕ) : Wn true f n + V f n + 1 = 2 ^ n := by
  induction n with
  | zero => simp [Wn, V, numCells]
  | succ n ih =>
    rw [Wn, V_snoc, pow_succ]
    have : bs true f (n + 1) + bt f (n + 1) = 1 := by have := bt_le f (n + 1); simp [bs]; omega
    nlinarith [ih, this]

theorem Wn_congr {neg : Bool} {f g : ℕ → ℕ} {n : ℕ} (h : ∀ j, 1 ≤ j → j ≤ n → f j = g j) : Wn neg f n = Wn neg g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Wn, Wn, ih (fun j a b => h j a (by omega))]
    simp only [bs, bt, h (n + 1) (by omega) le_rfl]

def addBody (neg : Bool) (dst src : ℕ) : Cmd :=
  .seq (.rd 723 dst 721 1) (.seq (.rd 724 src 721 1)
   (.seq (if neg then .ifZero 724 (.setK 724 1) (.setK 724 0) else .skip) (.seq (.copy 725 722)
    (.seq (.ifZero 723 .skip (.incr 725)) (.seq (.ifZero 724 .skip (.incr 725))
      (.seq (.ifLt 725 726 (.setK 722 0) (.seq (.setK 722 1) (.seq (.decr 725) (.decr 725))))
        (.wr dst 721 1 725)))))))

/-- `dst := dst + src` (`neg = false`) or `dst + (2^W-1-src) + 1` (`neg = true`, i.e. `dst - src` with carry out `[src ≤ dst]`)
on cells `1..W` (`W` = scalar 710); the carry out is left in scalar 722 -/
def addC (neg : Bool) (dst src : ℕ) : Cmd :=
  .seq (.setK 722 (if neg then 1 else 0)) (.seq (.setK 726 2) (.loop 710 721 (addBody neg dst src)))

theorem addBody_step (neg : Bool) (dst src : ℕ) (s : St) (j c : ℕ) (hc : c ≤ 1) (h722 : s.sc 722 = c) (h726 : s.sc 726 = 2) :
    let r := Cmd.run (addBody neg dst src) (s.setSc 721 j)
    r.1.sc 722 = (bt (s.ar dst) (j + 1) + bs neg (s.ar src) (j + 1) + c) / 2 ∧
    r.1.ar = Function.update s.ar dst (Function.update (s.ar dst) (j + 1)
      ((bt (s.ar dst) (j + 1) + bs neg (s.ar src) (j + 1) + c) % 2)) ∧
    r.1.sc 726 = 2 ∧ (∀ y, y < 721 ∨ 725 < y → r.1.sc y = s.sc y) ∧ r.2 ≤ 24 := by
  intro r
  have h1 : (s.setSc 721 j).sc 722 = c := by simp [St.setSc, Function.update_apply, h722]
  cases neg <;>
  (by_cases a : s.ar dst (j + 1) = 0 <;> by_cases b : s.ar src (j + 1) = 0 <;> rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
  simp [r, addBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_copy, Cmd.run_ifZero, Cmd.run_incr, Cmd.run_ifLt, Cmd.run_setK,
    Cmd.run_decr, Cmd.run_wr, Cmd.run_skip, bt, bs, Function.update_apply, a, b, h722, h726] <;>
  (intro y hy; split_ifs <;> first | rfl | (exfalso; omega)))

theorem Cells_succ {j : ℕ} {f g : ℕ → ℕ} (h : Cells j f g) (v : ℕ) (hv : v ≤ 1) :
    Cells (j + 1) (Function.update f (j + 1) v) g := by
  intro i
  obtain ⟨h1, h2⟩ := h i
  by_cases hi : i = j + 1
  · subst hi; simp [hv]
  · simp only [Function.update_apply, if_neg hi]
    refine ⟨fun ⟨a, b⟩ => h1 ⟨a, by omega⟩, fun hn => h2 fun ⟨a, b⟩ => hn ⟨a, by omega⟩⟩

theorem V_update_succ {j : ℕ} {f : ℕ → ℕ} (v : ℕ) (hv : v ≤ 1) :
    V (Function.update f (j + 1) v) (j + 1) = V f j + v * 2 ^ j := by
  rw [V_snoc]
  have e : V (Function.update f (j + 1) v) j = V f j :=
    V_congr fun i _ hi => by simp [Function.update_apply, show i ≠ j + 1 by omega]
  have e2 : bt (Function.update f (j + 1) v) (j + 1) = v := by
    simp only [bt, Function.update_self]; split_ifs <;> omega
  rw [e, e2]


/-- the registers `721 .. 726` -/
def ZA (y : ℕ) : Prop := 721 ≤ y ∧ y ≤ 726

theorem addC_run (neg : Bool) (dst src : ℕ) (hds : dst ≠ src) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    Cells n ((Cmd.run (addC neg dst src) st).1.ar dst) (st.ar dst) ∧
    V ((Cmd.run (addC neg dst src) st).1.ar dst) n + (Cmd.run (addC neg dst src) st).1.sc 722 * 2 ^ n =
      V (st.ar dst) n + Wn neg (st.ar src) n + (if neg then 1 else 0) ∧
    (Cmd.run (addC neg dst src) st).1.sc 722 ≤ 1 ∧ ArKeep dst st (Cmd.run (addC neg dst src) st).1 ∧
    ScKeep ZA st (Cmd.run (addC neg dst src) st).1 ∧ (Cmd.run (addC neg dst src) st).2 ≤ 25 * n + 10 := by
  set st1 : St := ((st.setSc 722 (if neg then 1 else 0)).setSc 726 2) with hst1
  have e710 : st1.sc 710 = n := by simp [hst1, St.setSc, Function.update_apply, hW]
  let P : ℕ → St → Prop := fun j t =>
    Cells j (t.ar dst) (st.ar dst) ∧
    V (t.ar dst) j + t.sc 722 * 2 ^ j = V (st.ar dst) j + Wn neg (st.ar src) j + (if neg then 1 else 0) ∧
    t.sc 722 ≤ 1 ∧ t.sc 726 = 2 ∧ ArKeep dst st t ∧ ScKeep ZA st t
  have h0 : P 0 st1 := by
    refine ⟨fun i => ⟨fun h => by omega, fun _ => rfl⟩, ?_, ?_, ?_, fun a _ => rfl, fun y hy => ?_⟩
    · cases neg <;> simp [hst1, V, numCells, St.setSc, Wn]
    · cases neg <;> simp [hst1, St.setSc]
    · simp [hst1, St.setSc]
    · have : ¬ (721 ≤ y ∧ y ≤ 726) := hy
      simp [hst1, St.setSc, Function.update_apply]
      split_ifs <;> first | rfl | omega
  have hstep : ∀ j t, j < st1.sc 710 → P j t → P (j + 1) (Cmd.run (addBody neg dst src) (t.setSc 721 j)).1 := by
    intro j t hj ⟨c1, c2, c3, c4, c5, c6⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := addBody_step neg dst src t j (t.sc 722) c3 rfl c4
    have hd : t.ar dst (j + 1) = st.ar dst (j + 1) := (c1 (j + 1)).2 (fun ⟨_, h⟩ => by omega)
    have hs : t.ar src = st.ar src := c5 src (Ne.symm hds)
    have hbd' : bt (t.ar dst) (j + 1) = bt (st.ar dst) (j + 1) := by simp only [bt, hd]
    rw [hbd', hs] at b1 b2
    set tot := bt (st.ar dst) (j + 1) + bs neg (st.ar src) (j + 1) + t.sc 722 with htot
    have hbd := bt_le (st.ar dst) (j + 1)
    have hbs := bs_le neg (st.ar src) (j + 1)
    have htot3 : tot ≤ 3 := by omega
    have hnb : tot % 2 ≤ 1 := by omega
    have hupd : (Cmd.run (addBody neg dst src) (t.setSc 721 j)).1.ar dst =
        Function.update (t.ar dst) (j + 1) (tot % 2) := by
      rw [b2]; simp [hd]
    refine ⟨?_, ?_, ?_, b3, ?_, ?_⟩
    · rw [hupd]; exact Cells_succ c1 _ hnb
    · rw [hupd, V_update_succ _ hnb, b1, V_snoc (st.ar dst), Wn, pow_succ]
      have hk : tot % 2 + 2 * (tot / 2) = tot := by omega
      have := congrArg (· * 2 ^ j) hk
      simp only [add_mul] at this
      have h3 : tot * 2 ^ j = bt (st.ar dst) (j + 1) * 2 ^ j + bs neg (st.ar src) (j + 1) * 2 ^ j + t.sc 722 * 2 ^ j := by
        rw [htot]; ring
      linarith [c2]
    · rw [b1]; omega
    · intro a ha
      rw [b2]
      simp [Function.update_apply, ha]
      exact c5 a ha
    · intro y hy
      have := b4 y
      by_cases h : y < 721 ∨ 725 < y
      · rw [this h]; exact c6 y hy
      · exfalso; apply hy; unfold ZA; omega
  have hI := Cmd.loop_inv (b := 710) (c := 721) (body := addBody neg dst src) P h0 hstep
  have hC := Cmd.loop_cost_le (b := 710) (c := 721) (body := addBody neg dst src) P 24 h0 hstep
    (fun j t hj hp => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hp
      exact (addBody_step neg dst src t j (t.sc 722) c3 rfl c4).2.2.2.2)
  rw [e710] at hI hC
  have hr : Cmd.run (addC neg dst src) st =
      ((Cmd.run (.loop 710 721 (addBody neg dst src)) st1).1,
        1 + (1 + (Cmd.run (.loop 710 721 (addBody neg dst src)) st1).2 + 1) + 1) := by
    simp [addC, Cmd.run_seq, Cmd.run_setK, hst1]
  rw [hr]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hI
  refine ⟨c1, c2, c3, c5, c6, ?_⟩
  simp only
  nlinarith [hC]

/-- addition -/
theorem add_run (dst src : ℕ) (hds : dst ≠ src) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    Cells n ((Cmd.run (addC false dst src) st).1.ar dst) (st.ar dst) ∧
    V ((Cmd.run (addC false dst src) st).1.ar dst) n + (Cmd.run (addC false dst src) st).1.sc 722 * 2 ^ n =
      V (st.ar dst) n + V (st.ar src) n ∧
    (Cmd.run (addC false dst src) st).1.sc 722 ≤ 1 ∧ ArKeep dst st (Cmd.run (addC false dst src) st).1 ∧
    ScKeep ZA st (Cmd.run (addC false dst src) st).1 ∧ (Cmd.run (addC false dst src) st).2 ≤ 25 * n + 10 := by
  have := addC_run false dst src hds st n hW
  rw [Wn_false] at this
  simpa using this

/-- subtraction: `dst := dst - src mod 2^n`, scalar 722 = `[src ≤ dst]` (no borrow) -/
theorem sub_run (dst src : ℕ) (hds : dst ≠ src) (st : St) (n : ℕ) (hW : st.sc 710 = n) :
    Cells n ((Cmd.run (addC true dst src) st).1.ar dst) (st.ar dst) ∧
    V ((Cmd.run (addC true dst src) st).1.ar dst) n + V (st.ar src) n + (Cmd.run (addC true dst src) st).1.sc 722 * 2 ^ n =
      V (st.ar dst) n + 2 ^ n ∧
    (Cmd.run (addC true dst src) st).1.sc 722 ≤ 1 ∧ ArKeep dst st (Cmd.run (addC true dst src) st).1 ∧
    ScKeep ZA st (Cmd.run (addC true dst src) st).1 ∧ (Cmd.run (addC true dst src) st).2 ≤ 25 * n + 10 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := addC_run true dst src hds st n hW
  have hw := Wn_true (st.ar src) n
  refine ⟨a1, ?_, a3, a4, a5, a6⟩
  simp only [if_true] at a2
  omega

end ECDLP.L76
