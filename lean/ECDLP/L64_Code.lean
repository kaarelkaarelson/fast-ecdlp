import ECDLP.L64_Rep
import ECDLP.L56_PForced

/-!
# L64 / Code: the setting code of a `PForced` gate network

A setting of gate `i` is `(x, msgs)`, `x : Free i`, `msgs : (parents j) -> Msg j`.  For an enumeration
`e : ι ≃ Fin g` the CODE of the setting of the node `a = e i` is the mixed-radix number
`code = enc x + nf * (sum_k enc (msg of parent e.symm k) * pp (nA a) k)`, where
`nA a k = (card Msg of node k)` if node `k` is a parent of `a`, else `1`.  Digit lemmas:
* `code % nf` is the free code, `dgx (nA a) (code / nf) k` is the message code of the parent `k`.
-/
noncomputable section
namespace ECDLP.L64
open Factoring.Aux Finset ECDLP.L56

variable {R : Type*} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (P : PForced R ι) {g : ℕ}
  (E : ∀ i, P.Msg i ≃ Fin (Fintype.card (P.Msg i))) (EF : ∀ i, P.Free i ≃ Fin (Fintype.card (P.Free i)))
  (e : ι ≃ Fin g)

omit [Fintype ι] in
open Classical in
/-- `PForced.toGNet` with an EXPLICIT message coding `E` (Mathlib's `Fintype.equivFin`, used by `PForced.enc`, is a
non-canonical choice, so no expression can compute it). -/
def toGNetE [DecidableEq ι] : GNet R ι where
  S := P.S
  fS _ := inferInstance
  dS _ := Classical.decEq _
  W := P.W
  c i j := if j ∈ P.pa i then P.w j + 1 else if i ∈ P.pa j then P.w i + 1 else 0
  v i j z := if h : j ∈ P.pa i then (E j (z.2 ⟨j, h⟩) : ℕ) + 1
    else if i ∈ P.pa j then (E i (P.out i z j) : ℕ) + 1 else 0

/-- number of free values of node `a` -/
def nfN (a : ℕ) : ℕ := if h : a < g then Fintype.card (P.Free (e.symm ⟨a, h⟩)) else 1
/-- number of messages of node `a` -/
def nmN (a : ℕ) : ℕ := if h : a < g then Fintype.card (P.Msg (e.symm ⟨a, h⟩)) else 1
/-- radix of position `k` in the message part of node `a` -/
def nA (a k : ℕ) : ℕ :=
  if ha : a < g then (if hk : k < g then (if e.symm ⟨k, hk⟩ ∈ P.pa (e.symm ⟨a, ha⟩) then nmN P e k else 1) else 1) else 1

theorem nmN_pos (a : ℕ) : 0 < nmN P e a := by
  unfold nmN; split_ifs
  · exact Fintype.card_pos
  · exact Nat.one_pos

theorem nA_pos (a k : ℕ) : 0 < nA P e a k := by
  unfold nA; split_ifs
  · exact nmN_pos P e k
  all_goals exact Nat.one_pos

theorem nA_par {a k : Fin g} (h : e.symm k ∈ P.pa (e.symm a)) : nA P e a k = Fintype.card (P.Msg (e.symm k)) := by
  simp [nA, nmN, a.2, k.2, h]

theorem nA_npar {a k : Fin g} (h : e.symm k ∉ P.pa (e.symm a)) : nA P e a k = 1 := by
  simp [nA, a.2, k.2, h]

/-- Families over a subtype of positions, as families over all positions (radix `1` elsewhere). -/
def subPi {g : ℕ} (q : Fin g → Prop) [DecidablePred q] (c n : Fin g → ℕ) (hq : ∀ k, q k → n k = c k)
    (hn : ∀ k, ¬ q k → n k = 1) : (∀ k : {k // q k}, Fin (c k.1)) ≃ (∀ k : Fin g, Fin (n k)) where
  toFun z k := if h : q k then Fin.cast (hq k h).symm (z ⟨k, h⟩) else ⟨0, by rw [hn k h]; exact Nat.one_pos⟩
  invFun w k := Fin.cast (hq k.1 k.2) (w k.1)
  left_inv z := by
    funext k
    simp only [dif_pos k.2]
    rfl
  right_inv w := by
    funext k
    by_cases h : q k
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h]
      apply Fin.ext
      have h1 := (w k).2
      have h2 := hn k h
      show 0 = (w k).val
      omega

theorem subPi_apply {g : ℕ} (q : Fin g → Prop) [DecidablePred q] (c n : Fin g → ℕ) (hq : ∀ k, q k → n k = c k)
    (hn : ∀ k, ¬ q k → n k = 1) (z : ∀ k : {k // q k}, Fin (c k.1)) (k : Fin g) (h : q k) :
    ((subPi q c n hq hn z k : Fin (n k)) : ℕ) = (z ⟨k, h⟩ : ℕ) := by
  simp [subPi, h]

/-- the message part of a setting, as a family over all nodes -/
def msgsEquiv (a : Fin g) :
    (∀ j : {j // j ∈ P.pa (e.symm a)}, P.Msg j.1) ≃ (∀ k : Fin g, Fin (nA P e a k)) :=
  (Equiv.piCongrRight fun j : {j // j ∈ P.pa (e.symm a)} => E j.1).trans <|
  (Equiv.piCongrLeft' (fun j : {j // j ∈ P.pa (e.symm a)} => Fin (Fintype.card (P.Msg j.1)))
    (Equiv.subtypeEquiv e (fun j => by rw [Equiv.symm_apply_apply]))).trans <|
  subPi (fun k : Fin g => e.symm k ∈ P.pa (e.symm a)) (fun k => Fintype.card (P.Msg (e.symm k)))
    (fun k => nA P e a k) (fun k h => nA_par P e h) (fun k h => nA_npar P e h)

theorem msgsEquiv_apply (a : Fin g) (z : ∀ j : {j // j ∈ P.pa (e.symm a)}, P.Msg j.1) (k : Fin g)
    (h : e.symm k ∈ P.pa (e.symm a)) :
    ((msgsEquiv P E e a z k : Fin (nA P e a k)) : ℕ) = (E (e.symm k) (z ⟨e.symm k, h⟩) : ℕ) := by
  unfold msgsEquiv
  exact (subPi_apply (fun k : Fin g => e.symm k ∈ P.pa (e.symm a)) (fun k => Fintype.card (P.Msg (e.symm k)))
    (fun k => nA P e a k) (fun k h => nA_par P e h) (fun k h => nA_npar P e h) _ k h).trans rfl

variable [hF : ∀ i, Nonempty (P.Free i)]

/-- size of the setting code of node `a` -/
def sN (a : ℕ) : ℕ := pp (nA P e a) g * nfN P e a

theorem sN_pos (a : ℕ) : 0 < sN P e a := by
  refine Nat.mul_pos (pp_pos fun i _ => nA_pos P e a i) ?_
  unfold nfN; split_ifs
  · exact Fintype.card_pos
  · exact Nat.one_pos

include hF in
/-- the coding of the settings of the nodes -/
def pfCoding : Coding ((toGNetE P E).toNet e) where
  s := sN P e
  pos a := sN_pos P e a
  e a :=
    (show (P.S (e.symm a)) ≃ (P.S (e.symm a)) from Equiv.refl _).trans <|
    (Equiv.prodComm _ _).trans <|
    (Equiv.prodCongr (msgsEquiv P E e a) (EF (e.symm a))).trans <|
    (Equiv.prodCongr (codeEquiv (nA P e a) g fun i _ => nA_pos P e a i) (Equiv.refl _)).trans <|
    finProdFinEquiv.trans (finCongr (by simp [sN, nfN, a.2]))


section digits
variable (a : Fin g) (x : P.Free (e.symm a)) (ms : ∀ j : {j // j ∈ P.pa (e.symm a)}, P.Msg j.1)

include hF in
theorem code_eq :
    ((pfCoding P E EF e).e a (show P.S (e.symm a) from (x, ms)) : ℕ) =
      (EF (e.symm a) x : ℕ) + Fintype.card (P.Free (e.symm a)) *
        ((codeEquiv (nA P e a) g fun i _ => nA_pos P e a i) (msgsEquiv P E e a ms) : ℕ) := by
  unfold pfCoding
  rfl


include hF in
theorem code_free : ((pfCoding P E EF e).e a (show P.S (e.symm a) from (x, ms)) : ℕ) % Fintype.card (P.Free (e.symm a)) =
    (EF (e.symm a) x : ℕ) := by
  rw [code_eq]
  have h := (EF (e.symm a) x).2
  rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h

include hF in
theorem code_div : ((pfCoding P E EF e).e a (show P.S (e.symm a) from (x, ms)) : ℕ) / Fintype.card (P.Free (e.symm a)) =
    ((codeEquiv (nA P e a) g fun i _ => nA_pos P e a i) (msgsEquiv P E e a ms) : ℕ) := by
  rw [code_eq]
  have h := (EF (e.symm a) x).2
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, zero_add]

include hF in
/-- **The message code of a parent is a digit of the setting code.** -/
theorem code_digit (k : Fin g) (hk : e.symm k ∈ P.pa (e.symm a)) :
    dgx (nA P e a) (((pfCoding P E EF e).e a (show P.S (e.symm a) from (x, ms)) : ℕ) /
        Fintype.card (P.Free (e.symm a))) k =
      (E (e.symm k) (ms ⟨e.symm k, hk⟩) : ℕ) := by
  rw [code_div, ← codeEquiv_symm_apply (nA P e a) g (fun i _ => nA_pos P e a i)]
  rw [Equiv.symm_apply_apply]
  exact msgsEquiv_apply P E e a ms k hk

end digits

end ECDLP.L64
