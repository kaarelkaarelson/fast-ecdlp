import ECDLP.L73_Lay
import ECDLP.L68_CarPEx

/-!
# L73 / Iface: the per-kind interface `GateKindPEx` and the decode state

Slots (relative to the base `u` of `PEx`; `u..u+3` = `a b z q`, `u+4..u+9` = engine scratch):
* `u+4` node (nf, nm, w, wt), `u+5` the (parent/current) node, `u+6` the child, `u+7` the setting code `z` of `u+5`;
* `u+10 pb = 2^b`, `u+11 pM = 2^M`, `u+12 pA = A`, `u+13 ph = h`  (parameters of the identity of the current node);
* `u+15 dc = c`, `u+16 dj`, `u+17 ds`, `u+18 dbase = nι*A + off c` (global index of the first gate of the block),
  `u+19 dn = nc c`, `u+20 dq` (coordinate of the child within its gate kind);
* `u+14 = b`, `u+27 = M` (the log-size M of the identity), `u+30 ..` free scratch for gate-kind expressions.
-/
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

inductive GKind | src | fa | mid | ib | car
  deriving DecidableEq

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar}

def kindOf : CG ι ιc N0.A → GKind
  | .src _ _ => .src
  | .gt _ (.fa _ _) => .fa
  | .gt _ (.mid _) => .mid
  | .gt _ (.ib _) => .ib
  | .gt _ (.car _) => .car

/-- the identity of a gate (`none` for `src`) -/
def idOf : CG ι ιc N0.A → Option (Fin K)
  | .src _ _ => none
  | .gt c _ => some c

/-- the coordinates `(dj, ds)` of a gate: `src (i,s)`: `(eι i, s)`; `fa (j,s)`: `(ecc j, s)`; `mid k`, `ib j`, `car j`: `(·, 0)` -/
def coordOf (L : Lay ι ιc) : CG ι ιc N0.A → ℕ × ℕ
  | .src i s => (L.eι i, s)
  | .gt c (.fa j s) => (L.ecc c j, s)
  | .gt _ (.mid k) => (k, 0)
  | .gt _ (.ib j) => (j, 0)
  | .gt _ (.car j) => (j.val, 0)

/-- coordinate of a child within its kind -/
def childCoord : CG ι ιc N0.A → ℕ
  | .src _ _ => 0
  | .gt _ (.fa _ _) => 0
  | .gt _ (.mid k) => k
  | .gt _ (.ib j) => j
  | .gt _ (.car j) => j.val

variable {m B g : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {w : Fin K → ℕ}
  {φ : ∀ c, ιc c → ι} {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop}

/-- the decode state: the facts about the slots that the dispatch establishes before it runs a gate-kind expression
on the node `a` with child `b` -/
structure KSt (L : Lay ι ιc) (σ : ℕ → ℕ) (u : ℕ) (a b : ℕ) (qa qb : CG ι ιc N0.A) : Prop where
  ha : σ (u + 5) = a
  hb : σ (u + 6) = b
  hpar : ∀ c, idOf qa = some c →
    σ (u + 10) = 2 ^ (NP N0 w c).b ∧ σ (u + 11) = 2 ^ (NP N0 w c).M ∧ σ (u + 12) = N0.A ∧ σ (u + 13) = N0.h ∧
    σ (u + 15) = c.val ∧ σ (u + 18) = L.nι * N0.A + L.off N0.A c ∧ σ (u + 19) = L.nc c
  hM : ∀ c, idOf qa = some c → σ (u + 27) = (NP N0 w c).M
  hbits : σ (u + 14) = N0.b
  hj : σ (u + 16) = (coordOf L qa).1
  hs : σ (u + 17) = (coordOf L qa).2
  hq : σ (u + 20) = childCoord qb

variable (L : Lay ι ιc) (m)

/-- the setting code of a node, as `PEx.hout` states it -/
def zcode (e : CG ι ιc N0.A ≃ Fin g) (a : Fin g) (z : (edgeNetM (w := w) φ F ok m).S (e.symm a)) : ℕ :=
  (pfCoding (edgeNetM (w := w) φ F ok m) (edgeEM (w := w) φ F ok m) (edgeEFM φ F ok m) e
    (hF := edge_free_nonempty φ F ok m)).e a z

/-- **The per-kind interface** (instantiated by L74 for `fa`, `mid` and by L75 for `ib`).
`outE` computes the CODE `ec` of the message the node `a` (of kind `kd`, slot `u+5`) sends to its child `b`
(slot `u+6`) from its setting code (slot `u+7`) in the decode state `KSt`.  It may read the slots `u..u+3`,
`u+5..u+7`, `u+10..u+20` (read only) and bind only slots `>= u+30` (and `u`, `u+1`, `u+2` through `readParent`).
Parents' messages are read with `digE X` after setting `u := node`, `u+1 := parent index`, `u+2 := code`. -/
structure GateKindPEx (kd : GKind) (e : CG ι ιc N0.A ≃ Fin g) (u : ℕ)
    (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u) where
  outE : Ex
  hout : ∀ σ₀, Ctx σ₀ → ∀ σ : ℕ → ℕ, Ag B σ₀ σ → ∀ a b : Fin g, ∀ z : (edgeNetM (w := w) φ F ok m).S (e.symm a),
    kindOf (e.symm a) = kd → e.symm a ∈ (edgeNetM (w := w) φ F ok m).pa (e.symm b) →
    KSt (w := w) L σ u a b (e.symm a) (e.symm b) → σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m e a z →
    Ex.eval σ A outE = ec (ι := ι) (ιc := ιc) (w := w) (e.symm a)
      ((edgeNetM (w := w) φ F ok m).out (e.symm a) z (e.symm b))


section read
variable {u : ℕ} {e : CG ι ιc N0.A ≃ Fin g}
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) e u)

/-- the code of the message of the parent with global index `idx` (an expression in slots `>= u+10`), read from the
setting code in slot `u+7` of the node in slot `u+5` -/
def readParent (idx : Ex) : Ex :=
  .lett u (.var (u + 5)) (.lett (u + 2) (.var (u + 7)) (.lett (u + 1) idx (digE X u (u + 1))))

theorem eval_readParent {σ₀ : ℕ → ℕ} {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ) {idx : Ex}
    {a k : Fin g} {p : CG ι ιc N0.A} (z : (edgeNetM (w := w) φ F ok m).S (e.symm a))
    (ha : σ (u + 5) = a) (hz : σ (u + 7) = zcode (w := w) (φ := φ) (F := F) (ok := ok) m e a z)
    (hidx : Ex.eval (Function.update (Function.update σ u (σ (u + 5))) (u + 2) (σ (u + 7))) A idx = k)
    (hkp : e.symm k = p) (hp : p ∈ paC (w := w) φ (e.symm a)) :
    Ex.eval σ A (readParent (w := w) (φ := φ) (F := F) (ok := ok) m X idx) = pm (w := w) φ F ok m z p := by
  simp only [readParent, Ex.eval]
  set σ1 := Function.update σ u (σ (u + 5)) with h1
  set σ2 := Function.update σ1 (u + 2) (σ1 (u + 7)) with h2
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  have e1 : σ1 (u + 7) = σ (u + 7) := by rw [h1, Function.update_of_ne (by omega)]
  have e2 : σ2 = Function.update σ1 (u + 2) (σ (u + 7)) := by rw [h2, e1]
  have hk' : Ex.eval σ2 A idx = k := by rw [e2, h1]; exact hidx
  set σ3 := Function.update σ2 (u + 1) (Ex.eval σ2 A idx) with h3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  refine eval_digE_pm (w := w) X hu hC g3 (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := k)
    ?_ ?_ hkp hp z ?_
  · rw [h3, Function.update_of_ne (by omega), h2, Function.update_of_ne (by omega), h1, Function.update_self]; exact ha
  · rw [h3, Function.update_self, hk']
  · rw [h3, Function.update_of_ne (by omega), h2, Function.update_self, e1]; exact hz

end read
end
end ECDLP.L73
end
