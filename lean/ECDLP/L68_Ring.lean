import ECDLP.L64_Edge

/-!
# L68 / Ring: an `Ex` combinator library for `ZMod q` (values are `ZMod.val`)

`Rp σ A e x` : the expression `e` evaluates to `x.val`.  Closure: `mulE`, `addE`, `sumE` (`foldSum` mod `q`),
`pwE` (`2^e mod q`).  Used for the DFT-style messages `faOut`, `hatOut`, `ibOut` of the gadget.
-/
noncomputable section
namespace ECDLP.L68
open Finset Factoring.Aux Ex

section
set_option linter.unusedSectionVars false
variable {q : ℕ} [NeZero q] {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vq : ℕ}

/-- `e` represents the ring element `x` -/
def Rp (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (e : Ex) (x : ZMod q) : Prop := Ex.eval σ A e = x.val

def mulE (vq : ℕ) (a b : Ex) : Ex := .mod (.mul a b) (.var vq)
def addE (vq : ℕ) (a b : Ex) : Ex := .mod (.add a b) (.var vq)
def sumE (vq x : ℕ) (n body : Ex) : Ex := .sum x n (.var vq) body
def pwE (vq x : ℕ) (e : Ex) : Ex := .prod x e (.var vq) (.lit 2)
def natE (vq : ℕ) (a : Ex) : Ex := .mod a (.var vq)

theorem rp_mul (hq : σ vq = q) {a b : Ex} {x y : ZMod q} (ha : Rp σ A a x) (hb : Rp σ A b y) :
    Rp σ A (mulE vq a b) (x * y) := by
  unfold Rp at *
  simp only [mulE, Ex.eval, ha, hb, hq, ZMod.val_mul]

theorem rp_add (hq : σ vq = q) {a b : Ex} {x y : ZMod q} (ha : Rp σ A a x) (hb : Rp σ A b y) :
    Rp σ A (addE vq a b) (x + y) := by
  unfold Rp at *
  simp only [addE, Ex.eval, ha, hb, hq, ZMod.val_add]

theorem rp_nat (hq : σ vq = q) {a : Ex} {n : ℕ} (ha : Ex.eval σ A a = n) :
    Rp σ A (natE vq a) (n : ZMod q) := by
  unfold Rp
  simp only [natE, Ex.eval, ha, hq, ZMod.val_natCast]

theorem foldSum_val (f : ℕ → ZMod q) (n : ℕ) :
    foldSum (fun i => (f i).val) q n = (∑ i ∈ range n, f i).val := by
  induction n with
  | zero => simp [foldSum]
  | succ n ih => rw [foldSum, ih, sum_range_succ, ZMod.val_add]

theorem foldSum_congr (f g : ℕ → ℕ) (m n : ℕ) (h : ∀ i < n, f i = g i) : foldSum f m n = foldSum g m n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldSum, foldSum, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem rp_sum (hq : σ vq = q) {x : ℕ} {nE body : Ex} {n : ℕ} (hn : Ex.eval σ A nE = n) (g : ℕ → ZMod q)
    (hb : ∀ i < n, Rp (Function.update σ x i) A body (g i)) :
    Rp σ A (sumE vq x nE body) (∑ i ∈ range n, g i) := by
  unfold Rp at *
  simp only [sumE, Ex.eval, hq, hn]
  rw [← foldSum_val]
  exact foldSum_congr _ _ _ _ hb

theorem foldProd_val (f : ℕ → ZMod q) (hq : 1 < q) (n : ℕ) :
    foldProd (fun i => (f i).val) q n = (∏ i ∈ range n, f i).val := by
  have : Fact (1 < q) := ⟨hq⟩
  induction n with
  | zero => simp [foldProd, ZMod.val_one]
  | succ n ih => rw [foldProd, ih, prod_range_succ, ZMod.val_mul]

theorem rp_pw (hq : σ vq = q) (hq2 : 2 < q) {x : ℕ} {eE : Ex} {e : ℕ} (he : Ex.eval σ A eE = e) :
    Rp σ A (pwE vq x eE) ((2 : ZMod q) ^ e) := by
  have hq1 : 1 < q := by omega
  have : Fact (1 < q) := ⟨hq1⟩
  unfold Rp
  simp only [pwE, Ex.eval, hq, he]
  have h2 : ((2 : ZMod q)).val = 2 := by
    have := ZMod.val_natCast (n := q) 2
    simpa [Nat.mod_eq_of_lt hq2] using this
  have := foldProd_val (q := q) (fun _ => 2) hq1 e
  simp only [prod_const, card_range, h2] at this
  exact this


theorem eval_stab {e : Ex} {t x : ℕ} (he : Ex.FV (· < t) e) (hx : t ≤ x) (v : ℕ) :
    Ex.eval (Function.update σ x v) A e = Ex.eval σ A e := by
  refine (Ex.FV_congr A e (· < t) _ _ (fun y hy => ?_) he).1
  rw [Function.update_of_ne (by omega)]

/-- the DFT stage `faOut` with root `2^e0`: `ζ^(r k) * Σ_{i<A} u_i ζ^(A i k)` -/
def faE (vq vA x1 : ℕ) (e0 r k u : Ex) : Ex :=
  mulE vq (pwE vq x1 (.mul e0 (.mul r k)))
    (sumE vq x1 (.var vA) (mulE vq u (pwE vq x1 (.mul e0 (.mul (.mul (.var vA) (.var x1)) k)))))

theorem rp_fa (hq : σ vq = q) (hq2 : 2 < q) {vA x1 : ℕ} (hvq : vq < x1) (hvA : vA < x1) {A' : ℕ} (hA : σ vA = A')
    {e0 r k u : Ex} (h0 : Ex.FV (· < x1) e0) (hr : Ex.FV (· < x1) r) (hk : Ex.FV (· < x1) k)
    {E R K : ℕ} (hE : Ex.eval σ A e0 = E) (hR : Ex.eval σ A r = R) (hK : Ex.eval σ A k = K)
    (U : ℕ → ZMod q) (hu : ∀ i < A', Rp (Function.update σ x1 i) A u (U i)) :
    Rp σ A (faE vq vA x1 e0 r k u) (faOut A' ((2 : ZMod q) ^ E) R U K) := by
  unfold faOut
  simp only [← pow_mul]
  refine rp_mul hq (rp_pw hq hq2 (by simp only [Ex.eval, hE, hR, hK])) ?_
  refine rp_sum hq (by simp only [Ex.eval, hA]) _ fun i hi => ?_
  have hq' : (Function.update σ x1 i) vq = q := by rw [Function.update_of_ne (by omega)]; exact hq
  have hA' : (Function.update σ x1 i) vA = A' := by rw [Function.update_of_ne (by omega)]; exact hA
  refine rp_mul hq' (hu i hi) (rp_pw hq' hq2 ?_)
  simp only [Ex.eval, eval_stab h0 (le_refl _), eval_stab hk (le_refl _), hE, hK, hA']
  simp

/-- `hatOut`: `Σ_{r<A} a_r ζ^(A r k)` with `ζ = 2^e0`; the body `u` reads the loop variable `x1` -/
def hatE (vq vA x1 : ℕ) (e0 k u : Ex) : Ex :=
  sumE vq x1 (.var vA) (mulE vq u (pwE vq x1 (.mul e0 (.mul (.mul (.var vA) (.var x1)) k))))

theorem rp_hat (hq : σ vq = q) (hq2 : 2 < q) {vA x1 : ℕ} (hvq : vq < x1) (hvA : vA < x1) {A' : ℕ} (hA : σ vA = A')
    {e0 k u : Ex} (h0 : Ex.FV (· < x1) e0) (hk : Ex.FV (· < x1) k)
    {E K : ℕ} (hE : Ex.eval σ A e0 = E) (hK : Ex.eval σ A k = K)
    (U : ℕ → ZMod q) (hu : ∀ i < A', Rp (Function.update σ x1 i) A u (U i)) :
    Rp σ A (hatE vq vA x1 e0 k u) (hatOut A' ((2 : ZMod q) ^ E) U K) := by
  unfold hatOut hatE
  simp only [← pow_mul]
  refine rp_sum hq (by simp only [Ex.eval, hA]) _ fun i hi => ?_
  have hq' : (Function.update σ x1 i) vq = q := by rw [Function.update_of_ne (by omega)]; exact hq
  have hA' : (Function.update σ x1 i) vA = A' := by rw [Function.update_of_ne (by omega)]; exact hA
  refine rp_mul hq' (hu i hi) (rp_pw hq' hq2 ?_)
  simp only [Ex.eval, eval_stab h0 (le_refl _), eval_stab hk (le_refl _), hE, hK, hA']
  simp

/-- `ibOut`: `tInv * hatOut`, with `tInv = 2^eT` -/
def ibE (vq vA x1 : ℕ) (e0 eT k u : Ex) : Ex := mulE vq (pwE vq x1 eT) (hatE vq vA x1 e0 k u)

theorem rp_ib (hq : σ vq = q) (hq2 : 2 < q) {vA x1 : ℕ} (hvq : vq < x1) (hvA : vA < x1) {A' : ℕ} (hA : σ vA = A')
    {e0 eT k u : Ex} (h0 : Ex.FV (· < x1) e0) (hk : Ex.FV (· < x1) k)
    {E T K : ℕ} (hE : Ex.eval σ A e0 = E) (hT : Ex.eval σ A eT = T) (hK : Ex.eval σ A k = K)
    (U : ℕ → ZMod q) (hu : ∀ i < A', Rp (Function.update σ x1 i) A u (U i)) :
    Rp σ A (ibE vq vA x1 e0 eT k u) ((2 : ZMod q) ^ T * hatOut A' ((2 : ZMod q) ^ E) U K) :=
  rp_mul hq (rp_pw hq hq2 hT) (rp_hat hq hq2 hvq hvA hA h0 hk hE hK U hu)


theorem eval_fv {e : Ex} {s : ℕ → Prop} (he : Ex.FV s e) {σ σ' : ℕ → ℕ} (h : ∀ y, s y → σ y = σ' y) :
    Ex.eval σ A e = Ex.eval σ' A e := (Ex.FV_congr A e s σ σ' h he).1

/-- the hat transform of the slot-`i` vector `Y i ·`, `i` given by an expression (bound to slot `vI`), index in `vS` -/
def hatYE (vq vA x3 vI vS : ℕ) (e0 k idx y : Ex) : Ex :=
  hatE vq vA x3 e0 k (.lett vI idx (.lett vS (.var x3) y))

/-- `midMsg`: `faOut` (root `2^ei`) of `k₂ ↦ Σ_{t<n} ε_t ĥ(Y (l t)) k₂ · ĥ(Y (r t)) k₂` -/
def midE (vq vA x1 x2 x3 vI vS : ℕ) (ei ew k1 j1 nE epsE lE rE yE : Ex) : Ex :=
  faE vq vA x1 ei k1 j1
    (sumE vq x2 nE (mulE vq epsE (mulE vq (hatYE vq vA x3 vI vS ew (.var x1) lE yE)
      (hatYE vq vA x3 vI vS ew (.var x1) rE yE))))

theorem rp_hatY (hq : σ vq = q) (hq2 : 2 < q) {vA x1 x2 x3 vI vS : ℕ} (hvq : vq < x1) (hvA : vA < x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS) {A' : ℕ} (hA : σ vA = A')
    {ew idx y : Ex} {Ew k₂ iv : ℕ}
    (hew : Ex.FV (· < x1) ew) (hidx : Ex.FV (fun y => y < x1 ∨ y = x2) idx)
    (hy : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) y)
    (hEw : Ex.eval σ A ew = Ew) (hx1 : σ x1 = k₂) (hiv : Ex.eval σ A idx = iv) (Yf : ℕ → ℕ → ZMod q)
    (hyv : ∀ i s, s < A' → Rp (Function.update (Function.update σ vI i) vS s) A y (Yf i s))
    :
    Rp σ A (hatYE vq vA x3 vI vS ew (.var x1) idx y) (hatOut A' ((2 : ZMod q) ^ Ew) (Yf iv) k₂) := by
  refine rp_hat hq hq2 (by omega) (by omega) hA (Ex.FV_mono (fun y hy => by omega) _ hew)
    (by simp only [Ex.FV]; omega) hEw (by simp only [Ex.eval, hx1]) _ fun r' hr' => ?_
  have hid : Ex.eval (Function.update σ x3 r') A idx = iv := by
    rw [eval_fv hidx (σ' := σ) (fun z hz => by
      rw [Function.update_of_ne (by omega)]), hiv]
  unfold Rp
  simp only [Ex.eval, hid, Function.update_self]
  rw [Function.update_of_ne (by omega : x3 ≠ vI), Function.update_self]
  have := hyv iv r' hr'
  unfold Rp at this
  rw [← this]
  refine eval_fv hy fun z hz => ?_
  rcases hz with hz | rfl | rfl
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  · simp [Function.update_apply]
  · simp [Function.update_apply]

theorem rp_mid (hq : σ vq = q) (hq2 : 2 < q) {vA x1 x2 x3 vI vS : ℕ} (hvq : vq < x1) (hvA : vA < x1)
    (h12 : x1 < x2) (h23 : x2 < x3) (h3I : x3 < vI) (hIS : vI < vS) {A' : ℕ} (hA : σ vA = A')
    {ei ew k1 j1 nE epsE lE rE yE : Ex}
    (hei : Ex.FV (· < x1) ei) (hew : Ex.FV (· < x1) ew) (hk1 : Ex.FV (· < x1) k1) (hj1 : Ex.FV (· < x1) j1)
    (hn : Ex.FV (· < x1) nE) (hε : Ex.FV (fun y => y < x1 ∨ y = x2) epsE)
    (hl : Ex.FV (fun y => y < x1 ∨ y = x2) lE) (hr : Ex.FV (fun y => y < x1 ∨ y = x2) rE)
    (hy : Ex.FV (fun y => y < x1 ∨ y = vI ∨ y = vS) yE)
    {Ei Ew K1 J1 n : ℕ} (hEi : Ex.eval σ A ei = Ei) (hEw : Ex.eval σ A ew = Ew) (hK1 : Ex.eval σ A k1 = K1)
    (hJ1 : Ex.eval σ A j1 = J1) (hnv : Ex.eval σ A nE = n)
    (εv : ℕ → ZMod q) (lv rv : ℕ → ℕ) (Yf : ℕ → ℕ → ZMod q)
    (hεv : ∀ t < n, Rp (Function.update σ x2 t) A epsE (εv t))
    (hlv : ∀ t < n, Ex.eval (Function.update σ x2 t) A lE = lv t)
    (hrv : ∀ t < n, Ex.eval (Function.update σ x2 t) A rE = rv t)
    (hyv : ∀ i s, s < A' → Rp (Function.update (Function.update σ vI i) vS s) A yE (Yf i s)) :
    Rp σ A (midE vq vA x1 x2 x3 vI vS ei ew k1 j1 nE epsE lE rE yE)
      (faOut A' ((2 : ZMod q) ^ Ei) K1
        (fun k₂ => ∑ t ∈ range n, εv t * (hatOut A' ((2 : ZMod q) ^ Ew) (Yf (lv t)) k₂ *
          hatOut A' ((2 : ZMod q) ^ Ew) (Yf (rv t)) k₂)) J1) := by
  refine rp_fa hq hq2 hvq hvA hA hei hk1 hj1 hEi hK1 hJ1 _ fun k₂ hk₂ => ?_
  have hq1 : (Function.update σ x1 k₂) vq = q := by rw [Function.update_of_ne (by omega)]; exact hq
  have hA1 : (Function.update σ x1 k₂) vA = A' := by rw [Function.update_of_ne (by omega)]; exact hA
  have hn1 : Ex.eval (Function.update σ x1 k₂) A nE = n := by rw [eval_stab hn (le_refl _)]; exact hnv
  refine rp_sum hq1 hn1 _ fun t ht => ?_
  -- context σ2 = update (update σ x1 k₂) x2 t
  set σ2 := Function.update (Function.update σ x1 k₂) x2 t with hσ2
  have hq2' : σ2 vq = q := by rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hq
  have hA2 : σ2 vA = A' := by rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hA
  have hag : ∀ y, y < x1 → σ2 y = σ y := fun y hy => by
    rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hag2 : ∀ y, (y < x1 ∨ y = x2) → σ2 y = (Function.update σ x2 t) y := fun y hy => by
    rcases hy with hy | rfl
    · rw [hσ2, Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simp [hσ2]
  have hx1 : σ2 x1 = k₂ := by rw [hσ2, Function.update_of_ne (by omega)]; simp
  have hyv2 : ∀ i s, s < A' → Rp (Function.update (Function.update σ2 vI i) vS s) A yE (Yf i s) := by
    intro i s hs
    have := hyv i s hs
    unfold Rp at this ⊢
    rw [← this]
    refine eval_fv hy fun z hz => ?_
    rcases hz with hz | rfl | rfl
    · simp only [Function.update_apply]
      split_ifs <;> first | omega | exact hag z hz
    · simp [Function.update_apply]
    · simp [Function.update_apply]
  have hew2 : Ex.eval σ2 A ew = Ew := by rw [eval_fv hew hag]; exact hEw
  have hid : ∀ idx : Ex, Ex.FV (fun y => y < x1 ∨ y = x2) idx → ∀ iv, Ex.eval (Function.update σ x2 t) A idx = iv →
      Ex.eval σ2 A idx = iv := fun idx hi iv h => by rw [eval_fv hi hag2]; exact h
  refine rp_mul hq2' (by unfold Rp; rw [eval_fv hε hag2]; exact hεv t ht) (rp_mul hq2' ?_ ?_)
  · exact rp_hatY hq2' hq2 hvq hvA h12 h23 h3I hIS hA2 hew hl hy hew2 hx1 (hid lE hl _ (hlv t ht)) Yf hyv2
  · exact rp_hatY hq2' hq2 hvq hvA h12 h23 h3I hIS hA2 hew hr hy hew2 hx1 (hid rE hr _ (hrv t ht)) Yf hyv2

end
end ECDLP.L68
end
