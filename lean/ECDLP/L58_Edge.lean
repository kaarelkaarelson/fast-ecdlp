import ECDLP.L58_Glue
import ECDLP.L56_EdgeCount

/-!
# L58 / Edge: the edge network over `ZMod m`, and the engine interface for it

`edgeNet` (L56) is a `PForced ℤ`; Rudich's engine runs over `ZMod m` for every modulus `m`.
The ring occurs only in the 0/1 weights, so `PForced.mapRing` changes it and the shared bits
(`Net.cc`, hence `Fits`/`total`) are literally unchanged.  `edge_value_zmod`: the value over
`ZMod m` is the cast of the same count as `edge_value`.

`EdgeEngineData` is the part of the engine interface (`TopNet`) that is NOT about the value:
what remains to be built for the edge family (expression-level representation, fit bounds).
-/
noncomputable section
namespace ECDLP.L58
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

/-- Change of the ring of a forced network (weights are mapped; messages, gates unchanged). -/
def mapRing {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type} (P : PForced R ι) : PForced S ι where
  Free := P.Free
  fFree := P.fFree
  Msg := P.Msg
  fMsg := P.fMsg
  iMsg := P.iMsg
  pa := P.pa
  rk := P.rk
  hrk := P.hrk
  W i s := f (P.W i s)
  out := P.out

section
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type} (P : PForced R ι)

theorem mapRing_tvc (x : ∀ i, P.Free i) : (mapRing f P).tvc x = P.tvc x :=
  P.tvc_unique x _ (fun i c => (mapRing f P).tvc_eq x i c)

theorem mapRing_run (x : ∀ i, P.Free i) (i : ι) : (mapRing f P).run x i = P.run x i := by
  unfold PForced.run
  refine Prod.ext rfl (funext fun j => ?_)
  show (mapRing f P).tvc x j.1 i = P.tvc x j.1 i
  rw [mapRing_tvc]

/-- The shared bits do not see the ring. -/
theorem mapRing_cc [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g) (a b : Fin g) :
    ((mapRing f P).toGNet.toNet e).cc a b = (P.toGNet.toNet e).cc a b := rfl

theorem mapRing_c [DecidableEq ι] {g : ℕ} (e : ι ≃ Fin g) (a b : Fin g) :
    ((mapRing f P).toGNet.toNet e).c a b = (P.toGNet.toNet e).c a b := rfl

end

variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

/-- The edge network over `ZMod m`. -/
def edgeNetM (m : ℕ) : PForced (ZMod m) (CG ι ιc N0.A) :=
  mapRing (Int.castRingHom (ZMod m)) (edgeNet (w := w) φ F ok)

open Classical in
/-- **The edge network over `ZMod m` has the same count as over `ℤ`.** -/
theorem edge_value_zmod (m : ℕ) (hm : 1 < m) (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) :
    (((edgeNetM (w := w) φ F ok m).toGNet.toNet e).value) =
      ((univ.filter fun d : ι → Fin N0.A → Dg N0 =>
        (∀ i s, ok i s (d i s)) ∧
          ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card : ZMod m) := by
  have : Fact (1 < m) := ⟨hm⟩
  have hW : ∀ i s, (edgeNetM (w := w) φ F ok m).W i s = 0 ∨ (edgeNetM (w := w) φ F ok m).W i s = 1 := by
    intro i s
    rcases WE_01 (w := w) φ F ok i s with h | h
    · left; show Int.castRingHom (ZMod m) ((edgeNet (w := w) φ F ok).W i s) = 0; rw [h]; simp
    · right; show Int.castRingHom (ZMod m) ((edgeNet (w := w) φ F ok).W i s) = 1; rw [h]; simp
  rw [PForced.pforced_value _ e hW]
  have hcA : ∀ x : (∀ i, (edgeNet (w := w) φ F ok).Free i),
      (∀ i, (edgeNetM (w := w) φ F ok m).W i ((edgeNetM (w := w) φ F ok m).run x i) = 1) ↔
      (∀ i, (edgeNet (w := w) φ F ok).W i ((edgeNet (w := w) φ F ok).run x i) = 1) := by
    intro x
    refine forall_congr' fun i => ?_
    show Int.castRingHom (ZMod m) ((edgeNet (w := w) φ F ok).W i
      ((mapRing (Int.castRingHom (ZMod m)) (edgeNet (w := w) φ F ok)).run x i)) = 1 ↔ _
    rw [mapRing_run]
    rcases WE_01 (w := w) φ F ok i ((edgeNet (w := w) φ F ok).run x i) with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hZ := edge_value (w := w) φ F ok hS hb e
  rw [PForced.pforced_value _ e (fun g z => WE_01 (w := w) φ F ok g z)] at hZ
  have hc : (univ.filter fun x : (∀ i, (edgeNet (w := w) φ F ok).Free i) =>
        ∀ i, (edgeNet (w := w) φ F ok).W i ((edgeNet (w := w) φ F ok).run x i) = 1).card =
      (univ.filter fun d : ι → Fin N0.A → Dg N0 =>
        (∀ i s, ok i s (d i s)) ∧ ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card := by
    exact_mod_cast hZ
  refine congrArg Nat.cast ?_
  rw [← hc]
  convert congrArg Finset.card (Finset.filter_congr (s := (univ : Finset (∀ i, (edgeNet (w := w) φ F ok).Free i)))
    (fun x _ => hcA x)) using 2
  all_goals first | rfl | (apply heq_of_eq; congr 1)


/-! ### The interface for the edge family -/

/-- The part of the engine interface (`TopNet`) for the edge family that is not the value: the
expression-level representation of the network over `ZMod m` (`CoarsenHyp`, i.e. `NRep` of the
edge network and the cluster map), and the fit/total bounds of its clusterings.  These are the
three things still to be built (L31 plan rows 5 and 6). -/
structure EdgeTopData (T : TopShape) (m n k : ℕ) (A : ℕ → ℕ → ℕ) {g : ℕ} (e : CG ι ιc N0.A ≃ Fin g) where
  κ : Coding ((edgeNetM (w := w) φ F ok m).toGNet.toNet e)
  cl : ∀ g' : ℕ, 0 < g' → Fin g → Fin g'
  hyp : ∀ (g' : ℕ) (hg : 0 < g') (σ₀ : ℕ → ℕ), σ₀ 10 = m → σ₀ 11 = T.sF n → σ₀ 0 = n → σ₀ 2 = k →
    CoarsenHyp m 13 σ₀ A (T.cp g') ((edgeNetM (w := w) φ F ok m).toGNet.toNet e) κ (cl g' hg)
  fits : ∀ (g' : ℕ) (hg : 0 < g'),
    (((edgeNetM (w := w) φ F ok m).toGNet.toNet e).coarsen (cl g' hg)).Fits (T.P0 (T.sF n) g')
  total : ∀ (g' : ℕ) (hg : 0 < g'),
    (((edgeNetM (w := w) φ F ok m).toGNet.toNet e).coarsen (cl g' hg)).total ≤ T.U0 (T.sF n)

open Classical in
/-- The edge count (the number of decompositions the network counts, as in `edge_value`). -/
def edgeCount : ℕ :=
  (univ.filter fun d : ι → Fin N0.A → Dg N0 =>
    (∀ i s, ok i s (d i s)) ∧ ∀ c, N0.Holds (F c) (N0.dgOf (fun j => d (φ c j)))).card

/-- Edge data plus the (already proved) value give the engine interface. -/
def EdgeTopData.toTopNet {T : TopShape} {m n k : ℕ} {A : ℕ → ℕ → ℕ} {g : ℕ} {e : CG ι ιc N0.A ≃ Fin g}
    (D : EdgeTopData (w := w) φ F ok T m n k A e) (hm : 1 < m) (hS : ∀ c, (NP N0 w c).SizeOK (F c))
    (hb : 1 ≤ N0.b) : TopNet T m n k A (edgeCount φ F ok) where
  gI := g
  inner := (edgeNetM (w := w) φ F ok m).toGNet.toNet e
  κ := D.κ
  cl := D.cl
  hyp := D.hyp
  fits := D.fits
  total := D.total
  value g' hg := by
    rw [Net.value_coarsen]
    exact edge_value_zmod (w := w) φ F ok m hm hS hb e

/-- **First glue theorem for the edge family.**  Given the edge data, the engine's top expression
represents `deepMult * (number of decompositions)` modulo `m`. -/
theorem top_rep_edge {T : TopShape} (K0 ℓ : ℕ) (hK : 2 ≤ K0) {m n k : ℕ} {A : ℕ → ℕ → ℕ} {σ : ℕ → ℕ}
    {g : ℕ} {e : CG ι ιc N0.A ≃ Fin g} (D : EdgeTopData (w := w) φ F ok T m n k A e) (hm : 1 < m)
    (hS : ∀ c, (NP N0 w c).SizeOK (F c)) (hb : 1 ≤ N0.b)
    (h10 : σ 10 = m) (hn : σ 0 = n) (hk : σ 2 = k) :
    ZR m (Ex.eval σ A (T.topE K0 ℓ))
      ((deepMult K0 ℓ ((Kb K0 ℓ * T.U0 (T.sF n) + Gs K0 ℓ * T.P0 (T.sF n) (Gs K0 ℓ)) / Kb K0 ℓ ^ 3) : ZMod m) *
        (edgeCount φ F ok : ZMod m)) :=
  top_rep_gen T K0 ℓ hK hm h10 hn hk (D.toTopNet φ F ok hm hS hb)

end ECDLP.L58
end
