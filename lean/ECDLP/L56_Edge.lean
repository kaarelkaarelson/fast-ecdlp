import ECDLP.L56_PForced
import ECDLP.L54_Value

/-!
# L56 / Edge: the gadget network with child-specific messages (PForced)

Same gate set as L54 (`src`, and per identity `fa`, `mid`, `ib`, `car`; `CG`), same parents, but now
* `fa (c,j,s)` sends to `mid (c,k)` ONLY the ring element `faMsgS slice s k` (one `Rg` element);
* `mid (c,k)` sends to `ib (c,j₁)` only the element `midMsg .. k .. j₁`;
* `ib (c,j₁)` sends to `car (c,j)` (`j % A = j₁`) only the element `ibOut .. (j / A)`;
* `car` sends its carry; `src` sends the slice.
Every message type is a single ring element (`M+1` bits), a carry (`M+3` bits) or a slice (`h b` bits).
-/
noncomputable section
namespace ECDLP.L56
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem mem_paC_gt (c : Fin K) {g q : Gate (ιc c) N0.A} (h : q ∈ paG (NP N0 w c) g) :
    CG.gt c q ∈ paC (w := w) φ (CG.gt c g) :=
  Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, h, rfl⟩)

/-- message type sent by a gate: a single ring element / carry / slice -/
def CM2 (ι : Type) (ιc : Fin K → Type) (N0 : NPar) (w : Fin K → ℕ) : CG ι ιc N0.A → Type
  | .src _ _ => Dg N0
  | .gt c (Gate.fa _ _) => (NP N0 w c).Rg
  | .gt c (Gate.mid _) => (NP N0 w c).Rg
  | .gt c (Gate.ib _) => (NP N0 w c).Rg
  | .gt c (Gate.car _) => Fin (2 ^ ((NP N0 w c).M + 3))

instance instCM2f : ∀ g : CG ι ιc N0.A, Fintype (CM2 ι ιc N0 w g)
  | .src _ _ => inferInstanceAs (Fintype (Dg N0))
  | .gt c (Gate.fa _ _) => inferInstanceAs (Fintype (NP N0 w c).Rg)
  | .gt c (Gate.mid _) => inferInstanceAs (Fintype (NP N0 w c).Rg)
  | .gt c (Gate.ib _) => inferInstanceAs (Fintype (NP N0 w c).Rg)
  | .gt c (Gate.car _) => inferInstanceAs (Fintype (Fin (2 ^ ((NP N0 w c).M + 3))))

instance instCM2i : ∀ g : CG ι ιc N0.A, Inhabited (CM2 ι ιc N0 w g)
  | .src _ _ => inferInstanceAs (Inhabited (Dg N0))
  | .gt c (Gate.fa _ _) => inferInstanceAs (Inhabited (NP N0 w c).Rg)
  | .gt c (Gate.mid _) => inferInstanceAs (Inhabited (NP N0 w c).Rg)
  | .gt c (Gate.ib _) => inferInstanceAs (Inhabited (NP N0 w c).Rg)
  | .gt c (Gate.car _) => ⟨⟨0, by positivity⟩⟩

abbrev EZ (g : CG ι ιc N0.A) : Type :=
  CF ι ιc N0 g × (∀ q : {q // q ∈ paC (w := w) φ g}, CM2 ι ιc N0 w q.1)

def cinE (c : Fin K) (j : Fin (N0.A * N0.A)) (z : EZ (w := w) φ (CG.gt c (Gate.car j))) : ℤ :=
  if h : 0 < j.val then
    decC (NP N0 w c) (z.2 ⟨CG.gt c (Gate.car ⟨j.val - 1, by have := j.2; omega⟩), mem_paC_gt φ c (Finset.mem_insert_of_mem (by rw [dif_pos h]; exact Finset.mem_singleton_self _))⟩)
  else 0

def cfE (c : Fin K) (j : Fin (N0.A * N0.A)) (z : EZ (w := w) φ (CG.gt c (Gate.car j))) : ℤ :=
  (show (NP N0 w c).Rg from z.2 ⟨CG.gt c (Gate.ib ⟨j.val % N0.A, Nat.mod_lt _ N0.toPar.A_pos⟩),
    mem_paC_gt φ c (Finset.mem_insert_self _ _)⟩).valMinAbs

def outE : ∀ g : CG ι ιc N0.A, EZ (w := w) φ g → CG ι ιc N0.A → CM2 ι ιc N0 w g
  | .src _ _ => fun z _ => z.1
  | .gt c (Gate.fa j s) => fun z ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.mid k) => (NP N0 w c).faMsgS
            (show Dg N0 from z.2 ⟨CG.src (φ c j) s, by simp [paC, extraPa]⟩) s k
        | _ => 0
  | .gt c (Gate.mid k) => fun z ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.ib j₁) => (NP N0 w c).midMsg (F c) k
            (fun i => NPar.exA (fun s : Fin N0.A => (show (NP N0 w c).Rg from
              z.2 ⟨CG.gt c (Gate.fa i s), mem_paC_gt φ c (Finset.mem_image.2 ⟨(i, s), mem_univ _, rfl⟩)⟩))) j₁
        | _ => 0
  | .gt c (Gate.ib j₁) => fun z ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.car j) => ibOut N0.A (NP N0 w c).ωi (NP N0 w c).tInv
            (NPar.exA (fun k : Fin N0.A => (show (NP N0 w c).Rg from
              z.2 ⟨CG.gt c (Gate.mid k), mem_paC_gt φ c (Finset.mem_image.2 ⟨k, mem_univ _, rfl⟩)⟩))) (j.val / N0.A)
        | _ => 0
  | .gt c (Gate.car j) => fun z _ =>
      encC (NP N0 w c) ((cinE (w := w) φ c j z + cfE (w := w) φ c j z) / 2 ^ N0.b)

open Classical in
def WE : ∀ g : CG ι ιc N0.A, EZ (w := w) φ g → ℤ
  | .src i s => fun z => if ok i s z.1 then 1 else 0
  | .gt _ (Gate.fa _ _) => fun _ => 1
  | .gt _ (Gate.mid _) => fun _ => 1
  | .gt _ (Gate.ib _) => fun _ => 1
  | .gt c (Gate.car j) => fun z => if ((2 ^ N0.b : ℤ) ∣ cinE (w := w) φ c j z + cfE (w := w) φ c j z) ∧
        (j.val + 1 = N0.A * N0.A → (cinE (w := w) φ c j z + cfE (w := w) φ c j z) / 2 ^ N0.b = 0) then 1 else 0

/-- **The sliced network with genuinely child-specific messages.** -/
def edgeNet : PForced ℤ (CG ι ιc N0.A) where
  Free := CF ι ιc N0
  fFree := instCFf
  Msg := CM2 ι ιc N0 w
  fMsg := instCM2f
  iMsg := instCM2i
  pa := paC (w := w) φ
  rk := rkC (w := w)
  hrk := hrkC φ
  W := WE (w := w) φ ok
  out := outE (w := w) φ F

theorem WE_01 : ∀ (g : CG ι ιc N0.A) z, (edgeNet (w := w) φ F ok).W g z = 0 ∨ (edgeNet (w := w) φ F ok).W g z = 1 := by
  classical
  intro g z
  cases g with
  | src i s => simp only [edgeNet, WE]; split_ifs <;> simp
  | gt c g =>
    cases g with
    | fa j s => exact Or.inr rfl
    | mid k => exact Or.inr rfl
    | ib j₁ => exact Or.inr rfl
    | car j => simp only [edgeNet, WE]; split_ifs <;> simp

/-- the claimed forced messages: projections of L38's honest vectors, per child -/
def uE (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) : ∀ g : CG ι ιc N0.A, CG ι ιc N0.A → CM2 ι ιc N0 w g
  | .src i s => fun _ => x (.src i s)
  | .gt c (Gate.fa j s) => fun ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.mid k) => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) (Gate.fa j s) k
        | _ => 0
  | .gt c (Gate.mid k) => fun ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.ib j₁) => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) (Gate.mid k) j₁
        | _ => 0
  | .gt c (Gate.ib j₁) => fun ch =>
      show (NP N0 w c).Rg from
        match ch with
        | .gt _ (Gate.car j) => honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) (Gate.ib j₁)
            ⟨j.val / N0.A, Nat.div_lt_of_lt_mul j.2⟩
        | _ => 0
  | .gt c (Gate.car j) => fun _ =>
      honest (N := NP N0 w c) (F c) (dcOf (w := w) φ c (dC x)) (Gate.car j)

theorem uE_rec (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) :
    ∀ g ch, uE (w := w) φ F x g ch = (edgeNet (w := w) φ F ok).out g (x g, fun j => uE (w := w) φ F x j.1 g) ch := by
  intro g ch
  cases g with
  | src i s => rfl
  | gt c g =>
    cases g with
    | fa j s => cases ch with
      | src _ _ => rfl
      | gt c' g' => cases g' <;> rfl
    | mid k => cases ch with
      | src _ _ => rfl
      | gt c' g' =>
        cases g' with
        | ib j₁ =>
          exact congrFun (honest_rec (N := NP N0 w c) (F c) (hS c).1 hb (xOf (dcOf (w := w) φ c (dC x))) (Gate.mid k)) j₁
        | _ => rfl
    | ib j₁ => cases ch with
      | src _ _ => rfl
      | gt c' g' =>
        cases g' with
        | car j =>
          exact congrFun (honest_rec (N := NP N0 w c) (F c) (hS c).1 hb (xOf (dcOf (w := w) φ c (dC x))) (Gate.ib j₁))
            ⟨j.val / N0.A, Nat.div_lt_of_lt_mul j.2⟩
        | _ => rfl
    | car j =>
      exact honest_rec (N := NP N0 w c) (F c) (hS c).1 hb (xOf (dcOf (w := w) φ c (dC x))) (Gate.car j)

theorem tvc_eq_uE (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (x : ∀ g : CG ι ιc N0.A, CF ι ιc N0 g) : (edgeNet (w := w) φ F ok).tvc x = uE (w := w) φ F x :=
  ((edgeNet (w := w) φ F ok).tvc_unique x _ (fun i c => uE_rec φ F ok hS hb x i c)).symm

end
end ECDLP.L56
end
