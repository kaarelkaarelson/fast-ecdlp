import ECDLP.L34_Main

/-!
# L34 / Net: the gadget as a gate network (settings, edge consistency, weights)

Nodes: `FA(i, s)` (slot `i`, `s < A`) holds the digits `s + A i'` (`i' < h`) of slot `i`;
`MID(k₁)` holds what it receives (`Y i s`); `IB(j₁)` holds what it receives (`Z r'`);
`CAR(j)` holds the coefficient it receives and its incoming (signed) carry.
`Good a` = all edge messages agree (a sender's message equals what the receiver stores) and the CAR weights
accept (`2^b ∣ cin + c`, first carry `0`, last outgoing carry `0`).
* `good_pinned`: a good assignment is the forced `run` of its FA settings.
* `good_run_iff`: `run d` is good iff the integer identity holds for the digits `d`.
* `good_ncard`: number of good assignments = number of FA settings whose digits satisfy the identity.
-/
namespace ECDLP.L34

open Finset Factoring.Aux

variable {ι : Type}

/-- Gadget parameters with `h` digits per input gate, `A * h = 2^k`. -/
structure NPar extends Par where
  h : ℕ
  hAh : A * h = 2 ^ k

namespace NPar
variable (N : NPar) (F : Form ι)

/-- zero-padded read of a finite family -/
def exA {X : Type*} [Zero X] {n : ℕ} (f : Fin n → X) : ℕ → X := fun s => if h : s < n then f ⟨s, h⟩ else 0

theorem exA_of_lt {X : Type*} [Zero X] {n : ℕ} (f : Fin n → X) (s : Fin n) : exA f s = f s := by
  simp [exA]

/-- Slices of an FA gate to digit vector. -/
def dgOf (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) : Fin (2 ^ N.k) → Fin (2 ^ N.b) :=
  fun m => d i ⟨m % N.A, Nat.mod_lt _ (N.toPar.A_pos)⟩
    ⟨m / N.A, Nat.div_lt_of_lt_mul (by rw [N.hAh]; exact m.2)⟩

/-- FA gate `s`: message to `MID k₁` from its stored slice (digits `s + A i'`, zero past `h`). -/
def faMsgS (u : Fin N.h → Fin (2 ^ N.b)) (s k₁ : ℕ) : N.Rg :=
  faOut N.A N.ω s (fun i' => ((exA (fun t => (u t : ℕ)) i' : ℕ) : N.Rg)) k₁

theorem sq_dgOf (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) (s : Fin N.A) (i' : ℕ) :
    N.sq (N.dgOf d i) (s + N.A * i') = exA (fun t => (d i s t : ℕ)) i' := by
  have hA0 := N.toPar.A_pos
  unfold Par.sq exA
  by_cases hi : i' < N.h
  · have hlt : (s : ℕ) + N.A * i' < 2 ^ N.k := by
      rw [← N.hAh]
      calc (s : ℕ) + N.A * i' < N.A + N.A * i' := by omega
        _ = N.A * (i' + 1) := by ring
        _ ≤ N.A * N.h := Nat.mul_le_mul_left _ hi
    rw [dif_pos hlt, dif_pos hi]
    simp only [dgOf]
    have e1 : ((s : ℕ) + N.A * i') % N.A = s := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.2]
    have e2 : ((s : ℕ) + N.A * i') / N.A = i' := by
      rw [Nat.add_mul_div_left _ _ hA0, Nat.div_eq_of_lt s.2]; simp
    have e1' : (⟨((s : ℕ) + N.A * i') % N.A, Nat.mod_lt _ hA0⟩ : Fin N.A) = s := Fin.ext e1
    have e2' : (⟨((s : ℕ) + N.A * i') / N.A, Nat.div_lt_of_lt_mul (by rw [N.hAh]; exact hlt)⟩ : Fin N.h) = ⟨i', hi⟩ := Fin.ext e2
    rw [e1', e2']
  · have : ¬ ((s : ℕ) + N.A * i' < 2 ^ N.k) := by
      rw [← N.hAh]
      have : N.A * N.h ≤ N.A * i' := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [dif_neg this, dif_neg hi]

theorem faMsgS_eq (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (i : ι) (s : Fin N.A) (k₁ : ℕ) :
    N.faMsgS (d i s) s k₁ = N.faMsg (N.dgOf d i) s k₁ := by
  unfold faMsgS Par.faMsg
  congr 1
  funext i'
  rw [N.sq_dgOf d i s i']

theorem hatOut_congr' (A : ℕ) {R : Type*} [CommRing R] (ζ : R) {a a' : ℕ → R} (h : ∀ r < A, a r = a' r) (k : ℕ) :
    hatOut A ζ a k = hatOut A ζ a' k := by
  unfold hatOut
  exact sum_congr rfl fun r hr => by rw [h r (mem_range.1 hr)]

theorem midMsg_congr (k₁ : ℕ) {Y Y' : ι → ℕ → N.Rg} (h : ∀ i, ∀ s < N.A, Y i s = Y' i s) (j₁ : ℕ) :
    N.midMsg F k₁ Y j₁ = N.midMsg F k₁ Y' j₁ := by
  unfold Par.midMsg
  congr 1
  funext k₂
  refine sum_congr rfl fun t _ => ?_
  rw [hatOut_congr' N.A N.ω (h (F.l t)) k₂, hatOut_congr' N.A N.ω (h (F.r t)) k₂]

theorem ibOut_congr {z z' : ℕ → N.Rg} (h : ∀ r < N.A, z r = z' r) (j : ℕ) :
    ibOut N.A N.ωi N.tInv z j = ibOut N.A N.ωi N.tInv z' j := by
  unfold ibOut
  rw [hatOut_congr' N.A N.ωi h]

/-- Carries along the chain (`c` the signed coefficients). -/
def carS (b : ℕ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => (carS b c j + c j) / 2 ^ b

/-- A global setting of the gates. -/
structure Asg (ι : Type) (N : NPar) where
  fa : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)
  mid : Fin N.A → ι → Fin N.A → N.Rg
  ib : Fin N.A → Fin N.A → N.Rg
  car : Fin (N.A * N.A) → N.Rg × ℤ

variable {N}

/-- incoming carry / received coefficient of CAR gate `j` (zero past the end) -/
def Asg.cin (a : Asg ι N) (j : ℕ) : ℤ := if h : j < N.A * N.A then (a.car ⟨j, h⟩).2 else 0
def Asg.cf (a : Asg ι N) (j : ℕ) : N.Rg := if h : j < N.A * N.A then (a.car ⟨j, h⟩).1 else 0

/-- **Good** setting: all edges agree and all weights are `1`. -/
structure Good (F : Form ι) (a : Asg ι N) : Prop where
  g1 : ∀ i s k₁, a.mid k₁ i s = N.faMsgS (a.fa i s) s k₁
  g2 : ∀ j₁ k₁, a.ib j₁ k₁ = N.midMsg F k₁ (fun i => exA (a.mid k₁ i)) j₁
  g3 : ∀ j : Fin (N.A * N.A), (a.car j).1 =
        ibOut N.A N.ωi N.tInv (exA (a.ib ⟨j % N.A, Nat.mod_lt _ N.toPar.A_pos⟩)) (j / N.A)
  g4a : a.cin 0 = 0
  g4b : ∀ j, j + 1 < N.A * N.A → a.cin (j + 1) = (a.cin j + (a.cf j).valMinAbs) / 2 ^ N.b
  g4c : ∀ j, j < N.A * N.A → (2 ^ N.b : ℤ) ∣ a.cin j + (a.cf j).valMinAbs
  g4d : (a.cin (N.A * N.A - 1) + (a.cf (N.A * N.A - 1)).valMinAbs) / 2 ^ N.b = 0

/-- IB gate message (as a function of the FA settings). -/
def ibS (F : Form ι) (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (j₁ : ℕ) (k₁ : Fin N.A) : N.Rg :=
  N.midMsg F k₁ (fun i => exA (fun s : Fin N.A => N.faMsgS (d i s) s k₁)) j₁

/-- coefficient received by CAR gate `j`. -/
def coefS (F : Form ι) (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) (j : ℕ) : N.Rg :=
  ibOut N.A N.ωi N.tInv (exA (fun k₁ : Fin N.A => ibS F d (j % N.A) k₁)) (j / N.A)

/-- The honest run from the FA settings. -/
def run (F : Form ι) (d : ι → Fin N.A → Fin N.h → Fin (2 ^ N.b)) : Asg ι N where
  fa := d
  mid := fun k₁ i s => N.faMsgS (d i s) s k₁
  ib := fun j₁ k₁ => ibS F d j₁ k₁
  car := fun j => (coefS F d j, NPar.carS N.b (fun j' => (coefS F d j').valMinAbs) j)

end NPar
end ECDLP.L34
