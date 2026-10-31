import ECDLP.L38_Compose

/-!
# L54 / Comp: per-identity gadget networks glued on shared source slots

Data: shared slots `ι`; for each identity `c : Fin K` its own slot type `ιc c` with a map `φ c : ιc c → ι`
(the slots the identity reads), a form `F c` over `ιc c`, and its own ring exponent `w c`
(`M_c = 2^k * w c`); the digit shape `(k, A, b, h)` is shared (`N0`).

Gates: `src i s` (free variable: the digit slice of slot `i`, local check `ok i s`; sends the slice) and, for each
identity `c`, a copy of L38's gadget gates `gt c g` in which the `fa j s` gate has NO free variable but receives the
slice from `src (φ c j) s` (an equality message), the other gates being L38's `mid`, `ib`, `car`.
`comp_value`: `Net.value` = number of digit assignments passing all `ok` and every identity.
-/
noncomputable section
namespace ECDLP.L54
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38

section
variable {ι : Type} {K : ℕ} (ιc : Fin K → Type) (N0 : NPar) (w : Fin K → ℕ)

/-- the parameters of identity `c`: shared digit shape, own ring exponent -/
def NP (c : Fin K) : NPar := { N0 with w := w c }

inductive CG (ι : Type) {K : ℕ} (ιc : Fin K → Type) (A : ℕ) : Type
  | src (i : ι) (s : Fin A)
  | gt (c : Fin K) (g : Gate (ιc c) A)

variable {ιc N0 w}

/-- gates ≃ sum -/
def cgEquiv (ι : Type) {K : ℕ} (ιc : Fin K → Type) (A : ℕ) :
    CG ι ιc A ≃ (ι × Fin A) ⊕ (Σ c : Fin K, Gate (ιc c) A) where
  toFun
    | .src i s => .inl (i, s)
    | .gt c g => .inr ⟨c, g⟩
  invFun
    | .inl p => .src p.1 p.2
    | .inr p => .gt p.1 p.2
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with p | p <;> rfl

instance instDecEq (ι : Type) [DecidableEq ι] {K : ℕ} (ιc : Fin K → Type) [∀ c, DecidableEq (ιc c)]
    (A : ℕ) : DecidableEq (CG ι ιc A) :=
  fun a b => decidable_of_iff _ (cgEquiv ι ιc A).injective.eq_iff

instance instFin (ι : Type) [Fintype ι] {K : ℕ} (ιc : Fin K → Type) [∀ c, Fintype (ιc c)]
    [∀ c, DecidableEq (ιc c)] (A : ℕ) : Fintype (CG ι ιc A) :=
  Fintype.ofEquiv _ (cgEquiv ι ιc A).symm

variable [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)]

abbrev Dg (N0 : NPar) : Type := Fin N0.h → Fin (2 ^ N0.b)

def CF (ι : Type) (ιc : Fin K → Type) (N0 : NPar) : CG ι ιc N0.A → Type
  | .src _ _ => Dg N0
  | .gt _ _ => Unit

def CM (ι : Type) (ιc : Fin K → Type) [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)]
    (N0 : NPar) (w : Fin K → ℕ) : CG ι ιc N0.A → Type
  | .src _ _ => Dg N0
  | .gt c g => MsgT (NP N0 w c) g

instance instCFf : ∀ g : CG ι ιc N0.A, Fintype (CF ι ιc N0 g)
  | .src _ _ => inferInstanceAs (Fintype (Dg N0))
  | .gt _ _ => inferInstanceAs (Fintype Unit)

instance instCFd : ∀ g : CG ι ιc N0.A, DecidableEq (CF ι ιc N0 g)
  | .src _ _ => inferInstanceAs (DecidableEq (Dg N0))
  | .gt _ _ => inferInstanceAs (DecidableEq Unit)

instance instCMf : ∀ g : CG ι ιc N0.A, Fintype (CM ι ιc N0 w g)
  | .src _ _ => inferInstanceAs (Fintype (Dg N0))
  | .gt c g => instMsgF (NP N0 w c) g

instance instCMi : ∀ g : CG ι ιc N0.A, Inhabited (CM ι ιc N0 w g)
  | .src _ _ => inferInstanceAs (Inhabited (Dg N0))
  | .gt c g => instMsgI (NP N0 w c) g

variable [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)

/-- extra parent of an `fa` gate: its source -/
def extraPa (c : Fin K) : Gate (ιc c) N0.A → Finset (CG ι ιc N0.A)
  | .fa j s => {.src (φ c j) s}
  | _ => ∅

def paC : CG ι ιc N0.A → Finset (CG ι ιc N0.A)
  | .src _ _ => ∅
  | .gt c g => (paG (NP N0 w c) g).image (CG.gt c) ∪ extraPa φ c g

def rkC : CG ι ιc N0.A → ℕ
  | .src _ _ => 0
  | .gt c g => rkG (NP N0 w c) g + 1

theorem hrkC : ∀ (g j : CG ι ιc N0.A), j ∈ paC (w := w) φ g → rkC (w := w) j < rkC (w := w) g := by
  intro g j h
  cases g with
  | src i s => simp [paC] at h
  | gt c g =>
    simp only [paC] at h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
      have := hrkG (NP N0 w c) g q hq
      simp only [rkC]; omega
    · cases g with
      | fa j' s => simp [extraPa] at h; subst h; simp [rkC, rkG]
      | mid _ => simp [extraPa] at h
      | ib _ => simp [extraPa] at h
      | car _ => simp [extraPa] at h

/-- free variable of the gadget gate `g` of identity `c`, read off the received messages -/
def frs (c : Fin K) : ∀ g : Gate (ιc c) N0.A,
    CF ι ιc N0 (.gt c g) × (∀ j : {j // j ∈ paC (w := w) φ (.gt c g)}, CM ι ιc N0 w j.1) →
      FreeT (NP N0 w c) g
  | .fa j s, z => z.2 ⟨.src (φ c j) s, by simp [paC, extraPa]⟩
  | .mid _, _ => ()
  | .ib _, _ => ()
  | .car _, _ => ()

def msr (c : Fin K) (g : Gate (ιc c) N0.A)
    (z : CF ι ιc N0 (.gt c g) × (∀ j : {j // j ∈ paC (w := w) φ (.gt c g)}, CM ι ιc N0 w j.1)) :
    ∀ q : {q // q ∈ paG (NP N0 w c) g}, MsgT (NP N0 w c) q.1 :=
  fun q => z.2 ⟨.gt c q.1, by
    simp only [paC]; exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨q.1, q.2, rfl⟩)⟩

def toGS (c : Fin K) (g : Gate (ιc c) N0.A)
    (z : CF ι ιc N0 (.gt c g) × (∀ j : {j // j ∈ paC (w := w) φ (.gt c g)}, CM ι ιc N0 w j.1)) :
    FreeT (NP N0 w c) g × (∀ q : {q // q ∈ paG (NP N0 w c) g}, MsgT (NP N0 w c) q.1) :=
  (frs φ c g z, msr φ c g z)

variable (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

open Classical in
def compNet : TForced ℤ (CG ι ιc N0.A) where
  Free := CF ι ιc N0
  fFree := instCFf
  dFree := instCFd
  Msg := CM ι ιc N0 w
  fMsg := instCMf
  iMsg := instCMi
  pa := paC (w := w) φ
  rk := rkC (w := w)
  hrk := hrkC φ
  W
    | .src i s => fun z => if ok i s z.1 then 1 else 0
    | .gt c g => fun z => WG (NP N0 w c) (fun _ _ _ => True) g (toGS φ c g z)
  out
    | .src _ _ => fun z => z.1
    | .gt c g => fun z => outG (NP N0 w c) (F c) g (toGS φ c g z)

end
end ECDLP.L54
end
