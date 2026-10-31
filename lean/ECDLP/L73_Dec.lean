import ECDLP.L73_Iface

/-!
# L73 / Dec: arithmetic decode of the gate index (as `Ex`), with the instance data as hypotheses (`InstEx`)
-/
noncomputable section
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ECDLP.L73
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

namespace Lay
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} (L : Lay ι ιc) (A : ℕ)

theorem off_succ (t : ℕ) : L.off A (t + 1) = L.off A t + L.blkN A t := sum_range_succ _ _

theorem off_mono {s t : ℕ} (h : s ≤ t) : L.off A s ≤ L.off A t :=
  sum_le_sum_of_subset (range_mono h)

/-- the identity of a global index: number of blocks that end at or before `y` -/
def cnt (y : ℕ) : ℕ := ∑ t ∈ range K, if y < L.off A (t + 1) then 0 else 1

theorem cnt_eq {c y : ℕ} (hc : c < K) (h1 : L.off A c ≤ y) (h2 : y < L.off A (c + 1)) : L.cnt A y = c := by
  unfold cnt
  have : ∀ t ∈ range K, (if y < L.off A (t + 1) then 0 else 1) = if t < c then 1 else 0 := by
    intro t _
    by_cases ht : t < c
    · have := L.off_mono A (show t + 1 ≤ c by omega)
      rw [if_neg (by omega), if_pos ht]
    · have := L.off_mono A (show c + 1 ≤ t + 1 by omega)
      rw [if_pos (by omega), if_neg ht]
  rw [sum_congr rfl this, sum_boole]
  have : (range K).filter (· < c) = range c := by ext t; simp; omega
  rw [this]; simp

theorem cnt_le (y : ℕ) : L.cnt A y ≤ K := by
  unfold cnt
  calc _ ≤ ∑ _t ∈ range K, 1 := sum_le_sum fun t _ => by split_ifs <;> omega
    _ = K := by simp

theorem off_lt_succ (c : Fin K) : L.off A (c.val + 1) = L.off A c + L.blk A c := by
  rw [off_succ, blkN_fin]

theorem blk_pos (hA : 0 < A) (c : Fin K) : 0 < L.blk A c := by
  unfold blk; have := Nat.mul_pos hA hA; omega

end Lay

section pure
/-- pure versions of the decode formulas -/
def decK (x S nA A r : ℕ) : ℕ :=
  if x < S then 0 else if r < nA then 1 else if r < nA + A then 2 else if r < nA + (A + A) then 3 else 4
def decJ (x S nA A r : ℕ) : ℕ :=
  if x < S then x / A else if r < nA then r / A else if r < nA + A then r - nA
    else if r < nA + (A + A) then r - (nA + A) else r - (nA + (A + A))
def decS (x S nA A r : ℕ) : ℕ := if x < S then x % A else if r < nA then r % A else 0

theorem dec_src {A S nA e s r : ℕ} (hs : s < A) (he : e * A + s < S) :
    decK (e * A + s) S nA A r = 0 ∧ decJ (e * A + s) S nA A r = e ∧ decS (e * A + s) S nA A r = s := by
  have hA : 0 < A := by omega
  simp only [decK, decJ, decS, if_pos he]
  refine ⟨trivial, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hs, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem dec_fa {A S nc e s : ℕ} (hs : s < A) (he : e < nc) :
    decK (S + (o + (e * A + s))) S (nc * A) A (e * A + s) = 1 ∧
    decJ (S + (o + (e * A + s))) S (nc * A) A (e * A + s) = e ∧
    decS (S + (o + (e * A + s))) S (nc * A) A (e * A + s) = s := by
  have hA : 0 < A := by omega
  have h1 : e * A + s < nc * A := by nlinarith
  simp only [decK, decJ, decS, if_neg (show ¬ S + (o + (e * A + s)) < S by omega), if_pos h1]
  refine ⟨trivial, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hs, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem dec_mid {A S nc k o : ℕ} (hk : k < A) :
    decK (S + (o + (nc * A + k))) S (nc * A) A (nc * A + k) = 2 ∧
    decJ (S + (o + (nc * A + k))) S (nc * A) A (nc * A + k) = k ∧
    decS (S + (o + (nc * A + k))) S (nc * A) A (nc * A + k) = 0 := by
  simp only [decK, decJ, decS, if_neg (show ¬ S + (o + (nc * A + k)) < S by omega),
    if_neg (show ¬ nc * A + k < nc * A by omega), if_pos (show nc * A + k < nc * A + A by omega)]
  exact ⟨trivial, by omega, trivial⟩

theorem dec_ib {A S nc k o : ℕ} (hk : k < A) :
    decK (S + (o + (nc * A + (A + k)))) S (nc * A) A (nc * A + (A + k)) = 3 ∧
    decJ (S + (o + (nc * A + (A + k)))) S (nc * A) A (nc * A + (A + k)) = k ∧
    decS (S + (o + (nc * A + (A + k)))) S (nc * A) A (nc * A + (A + k)) = 0 := by
  simp only [decK, decJ, decS, if_neg (show ¬ S + (o + (nc * A + (A + k))) < S by omega),
    if_neg (show ¬ nc * A + (A + k) < nc * A by omega), if_neg (show ¬ nc * A + (A + k) < nc * A + A by omega),
    if_pos (show nc * A + (A + k) < nc * A + (A + A) by omega)]
  exact ⟨trivial, by omega, trivial⟩

theorem dec_car {A S nc k o : ℕ} :
    decK (S + (o + (nc * A + (A + (A + k))))) S (nc * A) A (nc * A + (A + (A + k))) = 4 ∧
    decJ (S + (o + (nc * A + (A + (A + k))))) S (nc * A) A (nc * A + (A + (A + k))) = k ∧
    decS (S + (o + (nc * A + (A + (A + k))))) S (nc * A) A (nc * A + (A + (A + k))) = 0 := by
  simp only [decK, decJ, decS, if_neg (show ¬ S + (o + (nc * A + (A + (A + k)))) < S by omega),
    if_neg (show ¬ nc * A + (A + (A + k)) < nc * A by omega),
    if_neg (show ¬ nc * A + (A + (A + k)) < nc * A + A by omega),
    if_neg (show ¬ nc * A + (A + (A + k)) < nc * A + (A + A) by omega)]
  exact ⟨trivial, by omega, trivial⟩

end pure

section inst
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ}

/-- The instance data as expressions (hypotheses on the context): numbers of slots / identities, shape parameters
(closed expressions), `nc c` and `M_c` (read the identity from slot `u+22`). -/
structure InstEx (L : Lay ι ιc) (N0 : NPar) (w : Fin K → ℕ) (B : ℕ) (Ctx : (ℕ → ℕ) → Prop) (A : ℕ → ℕ → ℕ) (u : ℕ) where
  nIE : Ex
  KE : Ex
  AE : Ex
  hE : Ex
  pbE : Ex
  bE : Ex
  ncE : Ex
  MeE : Ex
  hnI : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A nIE = L.nι
  hK : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A KE = K
  hA : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A AE = N0.A
  hh : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A hE = N0.h
  hpb : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A pbE = 2 ^ N0.b
  hbv : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → Ex.eval σ A bE = N0.b
  hnc : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ c : Fin K, σ (u + 22) = c → Ex.eval σ A ncE = L.nc c
  hMe : ∀ σ₀, Ctx σ₀ → ∀ σ, Ag B σ₀ σ → ∀ c : Fin K, σ (u + 22) = c → Ex.eval σ A MeE = (NP N0 w c).M

variable {L : Lay ι ιc} {u : ℕ} (I : InstEx L N0 w B Ctx A u)

/-- `blkN t` with `A` read from slot `u+12`, loop variable `u+91` -/
def blkLoop : Ex :=
  .add (.mul (.lett (u + 22) (.var (u + 91)) I.ncE) (.var (u + 12)))
    (.add (.var (u + 12)) (.add (.var (u + 12)) (.mul (.var (u + 12)) (.var (u + 12)))))

def offE (t : Ex) : Ex := nsum (u + 91) t (blkLoop I)

variable {σ₀ : ℕ → ℕ} {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

theorem eval_blkLoop {t : ℕ} (ht : t < K) (hA : σ (u + 12) = N0.A) :
    Ex.eval (Function.update σ (u + 91) t) A (blkLoop I) = L.blkN N0.A t := by
  have g1 : Ag B σ₀ (Function.update σ (u + 91) t) := hσ.upd (by omega) _
  have g2 : Ag B σ₀ (Function.update (Function.update σ (u + 91) t) (u + 22) t) := g1.upd (by omega) _
  have := I.hnc σ₀ hC _ g2 ⟨t, ht⟩ (by simp)
  simp only [blkLoop, Ex.eval]
  have h91 : (Function.update σ (u + 91) t) (u + 91) = t := Function.update_self ..
  rw [h91, this]
  simp [Function.update_apply, hA, Lay.blkN, Lay.ncN, ht]

theorem eval_offE {t : Ex} {n : ℕ} (hn : Ex.eval σ A t = n) (hnK : n ≤ K) (hA : σ (u + 12) = N0.A) :
    Ex.eval σ A (offE I t) = L.off N0.A n := by
  simp only [offE, eval_nsum, hn, Lay.off]
  refine sum_congr rfl fun s hs => ?_
  exact eval_blkLoop I hu hC hσ (by have := mem_range.1 hs; omega) hA


/-- numeric code of a gate kind -/
def kc : GKind → ℕ
  | .src => 0 | .fa => 1 | .mid => 2 | .ib => 3 | .car => 4

section dec
omit hu hC hσ

def kcodeE (xs : ℕ) : Ex :=
    (.ifLt (.var xs) (.mul I.nIE (.var (u + 12))) (.lit 0)
      (.ifLt (.var (u + 25)) (.mul (.var (u + 19)) (.var (u + 12))) (.lit 1)
        (.ifLt (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.var (u + 12))) (.lit 2)
          (.ifLt (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.add (.var (u + 12)) (.var (u + 12))))
            (.lit 3) (.lit 4)))))

def djE (xs : ℕ) : Ex :=
    (.ifLt (.var xs) (.mul I.nIE (.var (u + 12))) (.div (.var xs) (.var (u + 12)))
      (.ifLt (.var (u + 25)) (.mul (.var (u + 19)) (.var (u + 12))) (.div (.var (u + 25)) (.var (u + 12)))
        (.ifLt (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.var (u + 12)))
          (.sub (.var (u + 25)) (.mul (.var (u + 19)) (.var (u + 12))))
          (.ifLt (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.add (.var (u + 12)) (.var (u + 12))))
            (.sub (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.var (u + 12))))
            (.sub (.var (u + 25)) (.add (.mul (.var (u + 19)) (.var (u + 12))) (.add (.var (u + 12)) (.var (u + 12)))))))))

def dsE (xs : ℕ) : Ex :=
    (.ifLt (.var xs) (.mul I.nIE (.var (u + 12))) (.mod (.var xs) (.var (u + 12)))
      (.ifLt (.var (u + 25)) (.mul (.var (u + 19)) (.var (u + 12))) (.mod (.var (u + 25)) (.var (u + 12))) (.lit 0)))

/-- decode the node whose index is in slot `xs`: sets the slots `u+10 ..`; then runs `body`.  See `L73_Iface` for the map. -/
def decodeE (xs : ℕ) (body : Ex) : Ex :=
  .lett (u + 12) I.AE <| .lett (u + 13) I.hE <| .lett (u + 10) I.pbE <|
  .lett (u + 24) (.sub (.var xs) (.mul I.nIE (.var (u + 12)))) <|
  .lett (u + 15) (nsum (u + 91) I.KE (.ifLt (.var (u + 24)) (offE I (.add (.var (u + 91)) (.lit 1))) (.lit 0) (.lit 1))) <|
  .lett (u + 22) (.var (u + 15)) <|
  .lett (u + 19) I.ncE <|
  .lett (u + 27) I.MeE <|
  .lett (u + 11) (nprod (u + 91) (.var (u + 27)) (.lit 2)) <|
  .lett (u + 18) (.add (.mul I.nIE (.var (u + 12))) (offE I (.var (u + 15)))) <|
  .lett (u + 25) (.sub (.var xs) (.var (u + 18))) <|
  .lett (u + 21) (kcodeE I xs) <| .lett (u + 16) (djE I xs) <| .lett (u + 17) (dsE I xs) <| .lett (u + 14) I.bE <|
  body

theorem eval_lett' (σ : ℕ → ℕ) (x : ℕ) (e b : Ex) :
    Ex.eval σ A (.lett x e b) = Ex.eval (Function.update σ x (Ex.eval σ A e)) A b := rfl

set_option maxHeartbeats 8000000 in
include hu hC hσ in
theorem eval_decodeE {xs : ℕ} (hxs : xs < u + 10) (body : Ex) (q : CG ι ιc N0.A)
    (hq : σ xs = L.enum N0.A q) :
    ∃ σ' : ℕ → ℕ, Ex.eval σ A (decodeE I xs body) = Ex.eval σ' A body ∧ Ag B σ₀ σ' ∧
      (∀ y, (y < u + 10 ∨ u + 28 ≤ y) → σ' y = σ y) ∧
      σ' (u + 21) = kc (kindOf q) ∧ σ' (u + 16) = (coordOf L q).1 ∧ σ' (u + 17) = (coordOf L q).2 ∧
      (∀ c, idOf q = some c → σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 11) = 2 ^ (NP N0 w c).M ∧ σ' (u + 12) = N0.A ∧
        σ' (u + 13) = N0.h ∧ σ' (u + 15) = c.val ∧ σ' (u + 18) = L.nι * N0.A + L.off N0.A c ∧
        σ' (u + 19) = L.nc c ∧ σ' (u + 27) = (NP N0 w c).M ∧ σ' (u + 14) = N0.b) ∧
      (σ' (u + 10) = 2 ^ N0.b ∧ σ' (u + 12) = N0.A ∧ σ' (u + 13) = N0.h ∧ σ' (u + 14) = N0.b) := by
  unfold decodeE
  rw [eval_lett', I.hA σ₀ hC σ hσ]
  set σ1 := Function.update σ (u + 12) N0.A with h1
  have g1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  rw [eval_lett', I.hh σ₀ hC σ1 g1]
  set σ2 := Function.update σ1 (u + 13) N0.h with h2
  have g2 : Ag B σ₀ σ2 := g1.upd (by omega) _
  rw [eval_lett', I.hpb σ₀ hC σ2 g2]
  set σ3 := Function.update σ2 (u + 10) (2 ^ N0.b) with h3
  have g3 : Ag B σ₀ σ3 := g2.upd (by omega) _
  have a3 : σ3 (u + 12) = N0.A := by simp [h3, h2, h1, Function.update_apply]
  have x3 : σ3 xs = σ xs := by simp [h3, h2, h1, Function.update_apply, show xs ≠ u + 10 by omega,
    show xs ≠ u + 12 by omega, show xs ≠ u + 13 by omega]
  have e4 : Ex.eval σ3 A (.sub (.var xs) (.mul I.nIE (.var (u + 12)))) = σ xs - L.nι * N0.A := by
    simp only [Ex.eval, I.hnI σ₀ hC σ3 g3, a3, x3]
  rw [eval_lett', e4]
  set σ4 := Function.update σ3 (u + 24) (σ xs - L.nι * N0.A) with h4
  have g4 : Ag B σ₀ σ4 := g3.upd (by omega) _
  have a4 : σ4 (u + 12) = N0.A := by simp [h4, a3, Function.update_apply]
  have y4 : σ4 (u + 24) = σ xs - L.nι * N0.A := by simp [h4]
  have e5 : Ex.eval σ4 A (nsum (u + 91) I.KE (.ifLt (.var (u + 24)) (offE I (.add (.var (u + 91)) (.lit 1))) (.lit 0) (.lit 1)))
      = L.cnt N0.A (σ xs - L.nι * N0.A) := by
    rw [eval_nsum, I.hK σ₀ hC σ4 g4, Lay.cnt]
    refine sum_congr rfl fun t ht => ?_
    have ht' := mem_range.1 ht
    have gt4 : Ag B σ₀ (Function.update σ4 (u + 91) t) := g4.upd (by omega) _
    simp only [Ex.eval]
    rw [eval_offE I hu hC gt4 (n := t + 1) (by simp [Ex.eval]) (by omega) (by simp [Function.update_apply, a4])]
    simp [Function.update_apply, y4]
  rw [eval_lett', e5]
  set c0 := L.cnt N0.A (σ xs - L.nι * N0.A) with hc0
  set σ5 := Function.update σ4 (u + 15) c0 with h5
  have g5 : Ag B σ₀ σ5 := g4.upd (by omega) _
  rw [eval_lett']
  have e6 : Ex.eval σ5 A (.var (u + 15)) = c0 := by simp [Ex.eval, h5]
  rw [e6]
  set σ6 := Function.update σ5 (u + 22) c0 with h6
  have g6 : Ag B σ₀ σ6 := g5.upd (by omega) _
  rw [eval_lett']
  set nc0 := Ex.eval σ6 A I.ncE with hnc0
  set σ7 := Function.update σ6 (u + 19) nc0 with h7
  have g7 : Ag B σ₀ σ7 := g6.upd (by omega) _
  rw [eval_lett']
  have a6 : σ6 (u + 12) = N0.A := by simp [h6, h5, a4, Function.update_apply]
  have c6 : σ6 (u + 22) = c0 := by simp [h6]
  have a7 : σ7 (u + 22) = c0 := by simp [h7, h6]
  rw [eval_lett']
  set Me0 := Ex.eval σ7 A I.MeE with hMe0
  set σ8 := Function.update σ7 (u + 27) Me0 with h8
  have g8 : Ag B σ₀ σ8 := g7.upd (by omega) _
  have e9 : Ex.eval σ8 A (nprod (u + 91) (.var (u + 27)) (.lit 2)) = 2 ^ Me0 := by
    rw [eval_nprod]
    simp only [Ex.eval]
    have : σ8 (u + 27) = Me0 := by simp [h8]
    rw [this]
    rw [pp_congr (f' := fun _ => 2) (fun i _ => by simp [Function.update_apply]), pp_const]
  rw [eval_lett', e9]
  set σ9 := Function.update σ8 (u + 11) (2 ^ Me0) with h9
  have g9 : Ag B σ₀ σ9 := g8.upd (by omega) _
  have a9 : σ9 (u + 12) = N0.A := by simp [h9, h8, h7, a6, Function.update_apply]
  have c9 : σ9 (u + 15) = c0 := by simp [h9, h8, h7, h6, h5, Function.update_apply]
  have e10 : Ex.eval σ9 A (.add (.mul I.nIE (.var (u + 12))) (offE I (.var (u + 15)))) =
      L.nι * N0.A + L.off N0.A c0 := by
    simp only [Ex.eval, I.hnI σ₀ hC σ9 g9, a9]
    rw [eval_offE I hu hC g9 (n := c0) (by simp [Ex.eval, c9]) (L.cnt_le _ _) a9]
  rw [eval_lett', e10]
  set σ10 := Function.update σ9 (u + 18) (L.nι * N0.A + L.off N0.A c0) with h10
  have g10 : Ag B σ₀ σ10 := g9.upd (by omega) _
  have e11 : Ex.eval σ10 A (.sub (.var xs) (.var (u + 18))) = σ xs - (L.nι * N0.A + L.off N0.A c0) := by
    simp [Ex.eval, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, show xs ≠ u + 18 by omega,
      show xs ≠ u + 11 by omega, show xs ≠ u + 27 by omega, show xs ≠ u + 19 by omega, show xs ≠ u + 22 by omega,
      show xs ≠ u + 15 by omega, show xs ≠ u + 24 by omega, show xs ≠ u + 10 by omega,
      show xs ≠ u + 13 by omega, show xs ≠ u + 12 by omega]
  rw [eval_lett', e11]
  set σ11 := Function.update σ10 (u + 25) (σ xs - (L.nι * N0.A + L.off N0.A c0)) with h11
  have g11 : Ag B σ₀ σ11 := g10.upd (by omega) _
  have a11 : σ11 (u + 12) = N0.A := by simp [h11, h10, h9, h8, h7, h6, h5, h4, a3, Function.update_apply]
  have n11 : σ11 (u + 19) = nc0 := by simp [h11, h10, h9, h8, h7, Function.update_apply]
  have r11 : σ11 (u + 25) = σ xs - (L.nι * N0.A + L.off N0.A c0) := by simp [h11]
  have x11 : σ11 xs = σ xs := by
    simp [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, show xs ≠ u + 18 by omega,
      show xs ≠ u + 11 by omega, show xs ≠ u + 27 by omega, show xs ≠ u + 19 by omega, show xs ≠ u + 22 by omega,
      show xs ≠ u + 15 by omega, show xs ≠ u + 24 by omega, show xs ≠ u + 10 by omega,
      show xs ≠ u + 13 by omega, show xs ≠ u + 12 by omega, show xs ≠ u + 25 by omega]
  set r0 := σ xs - (L.nι * N0.A + L.off N0.A c0) with hr0
  have ek : Ex.eval σ11 A (kcodeE I xs) = decK (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp only [kcodeE, decK, Ex.eval, I.hnI σ₀ hC σ11 g11, a11, n11, r11, x11]
  rw [eval_lett', ek]
  set σ12 := Function.update σ11 (u + 21) (decK (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0) with h12
  have g12 : Ag B σ₀ σ12 := g11.upd (by omega) _
  have a12 : σ12 (u + 12) = N0.A := by simp [h12, a11, Function.update_apply]
  have n12 : σ12 (u + 19) = nc0 := by simp [h12, n11, Function.update_apply]
  have r12 : σ12 (u + 25) = r0 := by simp [h12, r11, Function.update_apply]
  have x12 : σ12 xs = σ xs := by simp [h12, x11, Function.update_apply, show xs ≠ u + 21 by omega]
  have ej : Ex.eval σ12 A (djE I xs) = decJ (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp only [djE, decJ, Ex.eval, I.hnI σ₀ hC σ12 g12, a12, n12, r12, x12]
  rw [ej]
  set σ13 := Function.update σ12 (u + 16) (decJ (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0) with h13
  have g13 : Ag B σ₀ σ13 := g12.upd (by omega) _
  have a13 : σ13 (u + 12) = N0.A := by simp [h13, a12, Function.update_apply]
  have n13 : σ13 (u + 19) = nc0 := by simp [h13, n12, Function.update_apply]
  have r13 : σ13 (u + 25) = r0 := by simp [h13, r12, Function.update_apply]
  have x13 : σ13 xs = σ xs := by simp [h13, x12, Function.update_apply, show xs ≠ u + 16 by omega]
  have es : Ex.eval σ13 A (dsE I xs) = decS (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp only [dsE, decS, Ex.eval, I.hnI σ₀ hC σ13 g13, a13, n13, r13, x13]
  rw [eval_lett' σ13 (u + 17), es]
  set σ14 := Function.update σ13 (u + 17) (decS (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0) with h14
  have g14 : Ag B σ₀ σ14 := g13.upd (by omega) _
  have f21' : σ14 (u + 21) = decK (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp [h14, h13, h12, Function.update_apply]
  have f16' : σ14 (u + 16) = decJ (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp [h14, h13, Function.update_apply]
  have f17' : σ14 (u + 17) = decS (σ xs) (L.nι * N0.A) (nc0 * N0.A) N0.A r0 := by
    simp [h14]
  have f12' : σ14 (u + 12) = N0.A := by
    simp [h14, a13, Function.update_apply]
  have f10' : σ14 (u + 10) = 2 ^ N0.b := by
    simp [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, Function.update_apply]
  have f11' : σ14 (u + 11) = 2 ^ Me0 := by
    simp [h14, h13, h12, h11, h10, h9, Function.update_apply]
  have f13' : σ14 (u + 13) = N0.h := by
    simp [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, Function.update_apply]
  have f15' : σ14 (u + 15) = c0 := by
    simp [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, Function.update_apply]
  have f18' : σ14 (u + 18) = L.nι * N0.A + L.off N0.A c0 := by
    simp [h14, h13, h12, h11, h10, Function.update_apply]
  have f19' : σ14 (u + 19) = nc0 := by
    simp [h14, h13, h12, h11, h10, h9, h8, h7, Function.update_apply]
  have f27' : σ14 (u + 27) = Me0 := by
    simp [h14, h13, h12, h11, h10, h9, h8, Function.update_apply]
  rw [eval_lett', I.hbv σ₀ hC σ14 g14]
  set σ15 := Function.update σ14 (u + 14) N0.b with h15
  have g15 : Ag B σ₀ σ15 := g14.upd (by omega) _
  have s15 : ∀ y, y ≠ u + 14 → σ15 y = σ14 y := fun y hy => by simp [h15, Function.update_apply, hy]
  have f14 : σ15 (u + 14) = N0.b := by simp [h15]
  have f21 := (s15 (u + 21) (by omega)).trans f21'
  have f16 := (s15 (u + 16) (by omega)).trans f16'
  have f17 := (s15 (u + 17) (by omega)).trans f17'
  have f12 := (s15 (u + 12) (by omega)).trans f12'
  have f10 := (s15 (u + 10) (by omega)).trans f10'
  have f11 := (s15 (u + 11) (by omega)).trans f11'
  have f13 := (s15 (u + 13) (by omega)).trans f13'
  have f15 := (s15 (u + 15) (by omega)).trans f15'
  have f18 := (s15 (u + 18) (by omega)).trans f18'
  have f19 := (s15 (u + 19) (by omega)).trans f19'
  have f27 := (s15 (u + 27) (by omega)).trans f27'
  refine ⟨σ15, rfl, g15, ?_, ?_⟩
  · intro y hy
    rw [h15, Function.update_of_ne (by omega), h14, Function.update_of_ne (by omega), h13, Function.update_of_ne (by omega), h12,
      Function.update_of_ne (by omega), h11, Function.update_of_ne (by omega), h10,
      Function.update_of_ne (by omega), h9, Function.update_of_ne (by omega), h8, Function.update_of_ne (by omega),
      h7, Function.update_of_ne (by omega), h6, Function.update_of_ne (by omega), h5,
      Function.update_of_ne (by omega), h4, Function.update_of_ne (by omega), h3, Function.update_of_ne (by omega),
      h2, Function.update_of_ne (by omega), h1, Function.update_of_ne (by omega)]
  have hglob : σ15 (u + 10) = 2 ^ N0.b ∧ σ15 (u + 12) = N0.A ∧ σ15 (u + 13) = N0.h ∧ σ15 (u + 14) = N0.b :=
    ⟨f10, f12, f13, f14⟩
  cases q with
  | src i s =>
    have hxq : σ xs = L.eι i * N0.A + s := by rw [hq, Lay.enum_src]
    have hlt : L.eι i * N0.A + s < L.nι * N0.A := by
      have := (L.eι i).2
      have := s.2
      nlinarith
    obtain ⟨k0, j0, s0⟩ := dec_src (nA := nc0 * N0.A) (r := r0) s.2 hlt
    refine ⟨?_, ?_, ?_, by simp [idOf], hglob⟩
    · rw [f21, hxq, k0]; rfl
    · rw [f16, hxq, j0]; rfl
    · rw [f17, hxq, s0]; rfl
  | gt c g =>
    have hq' : σ xs = L.nι * N0.A + (L.off N0.A c + (L.gateE N0.A c g : ℕ)) := by rw [hq, Lay.enum_gt]
    have hge := (L.gateE N0.A c g).2
    have hc0eq : c0 = c.val := by
      rw [hc0]
      refine L.cnt_eq N0.A c.2 (by omega) ?_
      rw [Lay.off_lt_succ]; unfold Lay.blk at hge ⊢; omega
    have hnc0 : nc0 = L.nc c := I.hnc σ₀ hC σ6 g6 c (by rw [c6, hc0eq])
    have hMe : Me0 = (NP N0 w c).M := I.hMe σ₀ hC σ7 g7 c (by rw [a7, hc0eq])
    have hr0 : r0 = (L.gateE N0.A c g : ℕ) := by rw [hr0, hq', hc0eq]; omega
    have hpar : ∀ c', idOf (CG.gt c g : CG ι ιc N0.A) = some c' → σ15 (u + 10) = 2 ^ N0.b ∧ σ15 (u + 11) = 2 ^ (NP N0 w c').M ∧
        σ15 (u + 12) = N0.A ∧ σ15 (u + 13) = N0.h ∧ σ15 (u + 15) = c'.val ∧
        σ15 (u + 18) = L.nι * N0.A + L.off N0.A c' ∧ σ15 (u + 19) = L.nc c' ∧ σ15 (u + 27) = (NP N0 w c').M ∧ σ15 (u + 14) = N0.b := by
      intro c' hc'
      simp only [idOf, Option.some.injEq] at hc'
      subst hc'
      exact ⟨f10, by rw [f11, hMe], f12, f13, by rw [f15, hc0eq], by rw [f18, hc0eq], by rw [f19, hnc0], by rw [f27, hMe], f14⟩
    rw [hnc0, hr0, hq'] at f21 f16 f17
    cases g with
    | fa j s =>
      rw [Lay.gateE_fa] at f21 f16 f17
      obtain ⟨k0, j0, s0⟩ := dec_fa (S := L.nι * N0.A) (nc := L.nc c) (o := L.off N0.A c) s.2 (L.ecc c j).2
      exact ⟨by rw [f21, k0]; rfl, by rw [f16, j0]; rfl, by rw [f17, s0]; rfl, hpar, hglob⟩
    | mid k =>
      rw [Lay.gateE_mid] at f21 f16 f17
      obtain ⟨k0, j0, s0⟩ := dec_mid (S := L.nι * N0.A) (nc := L.nc c) (o := L.off N0.A c) k.2
      exact ⟨by rw [f21, k0]; rfl, by rw [f16, j0]; rfl, by rw [f17, s0]; rfl, hpar, hglob⟩
    | ib j =>
      rw [Lay.gateE_ib] at f21 f16 f17
      obtain ⟨k0, j0, s0⟩ := dec_ib (S := L.nι * N0.A) (nc := L.nc c) (o := L.off N0.A c) j.2
      exact ⟨by rw [f21, k0]; rfl, by rw [f16, j0]; rfl, by rw [f17, s0]; rfl, hpar, hglob⟩
    | car j =>
      rw [Lay.gateE_car] at f21 f16 f17
      obtain ⟨k0, j0, s0⟩ := dec_car (S := L.nι * N0.A) (nc := L.nc c) (o := L.off N0.A c) (k := j.val)
      exact ⟨by rw [f21, k0]; rfl, by rw [f16, j0]; rfl, by rw [f17, s0]; rfl, hpar, hglob⟩

end dec
end inst

end ECDLP.L73
end
