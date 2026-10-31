import ECDLP.L92_Tree

/-!
# L92 / Look: the lookup command for short inputs (`len < T0`) and its correctness on `FrameIn'` states

The pattern of nonzero cells `1..len` of arrays `0,1,2,4,5,9,6` determines `(p, a, b, xR, yR, |τ|, τ)` of the reduced input
(`Reads72n`), hence the answer `[0 < Zc]`; `lookCmd` is the decision tree over all such patterns.
-/
namespace ECDLP.L92
open ECDLP ECDLP.L61 ECDLP.L51 ECDLP.L65 ECDLP.L70 ECDLP.L80 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

theorem bval_numCells (f : ℕ → ℕ) : ∀ (n o : ℕ), bval ((List.range n).map fun j => decide (f (o + j) ≠ 0)) = numCells f o n
  | 0, o => by simp [bval, numCells]
  | n + 1, o => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, numCells_succ, bval]
      have := bval_numCells f n (o + 1)
      have e : ((fun j => decide (f (o + j) ≠ 0)) ∘ Nat.succ) = fun j => decide (f (o + 1 + j) ≠ 0) := by
        funext j; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]
      rw [e, this]
      by_cases h : f (o + 0) = 0 <;> simp [h]

def seg (a ℓ : ℕ) : List (ℕ × ℕ) := (List.range ℓ).map fun j => (a, 1 + j)

theorem probeBits_seg (st : St) (a ℓ : ℕ) :
    probeBits st (seg a ℓ) = (List.range ℓ).map fun j => decide (st.ar a (1 + j) ≠ 0) := by
  simp [probeBits, seg, List.map_map, Function.comp]

theorem length_probeBits_seg (st : St) (a ℓ : ℕ) : (probeBits st (seg a ℓ)).length = ℓ := by
  simp [probeBits_seg]

/-- the probed cells for length `ℓ` -/
def probesL (ℓ : ℕ) : List (ℕ × ℕ) :=
  seg 0 ℓ ++ (seg 1 ℓ ++ (seg 2 ℓ ++ (seg 4 ℓ ++ (seg 5 ℓ ++ (seg 9 ℓ ++ seg 6 ℓ)))))

theorem length_probesL (ℓ : ℕ) : (probesL ℓ).length = 7 * ℓ := by
  simp [probesL, seg]; omega

/-- decode a probe pattern into `(p, a, b, xR, yR, π)` -/
def decode (ℓ : ℕ) (bs : List Bool) : ℕ × ℕ × ℕ × ℕ × ℕ × List Bool :=
  let r0 := bs.drop ℓ
  let r1 := r0.drop ℓ
  let r2 := r1.drop ℓ
  let r3 := r2.drop ℓ
  let r4 := r3.drop ℓ
  let r5 := r4.drop ℓ
  (bval (bs.take ℓ), bval (r0.take ℓ), bval (r1.take ℓ), bval (r2.take ℓ), bval (r3.take ℓ),
    (r5.take ℓ).take (bval (r4.take ℓ)))

/-- the table: the answer bit for a pattern -/
noncomputable def tabAns (m ℓ : ℕ) (bs : List Bool) : ℕ :=
  open Classical in
  let d := decode ℓ bs
  if 0 < Zc m (d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, []) d.2.2.2.2.2 then 0 else 1

theorem decode_probes (st : St) (ℓ : ℕ) :
    decode ℓ (probeBits st (probesL ℓ)) =
      (numCells (st.ar 0) 1 ℓ, numCells (st.ar 1) 1 ℓ, numCells (st.ar 2) 1 ℓ, numCells (st.ar 4) 1 ℓ,
        numCells (st.ar 5) 1 ℓ,
        ((List.range ℓ).map fun j => decide (st.ar 6 (1 + j) ≠ 0)).take (numCells (st.ar 9) 1 ℓ)) := by
  have hp : probeBits st (probesL ℓ) = probeBits st (seg 0 ℓ) ++ (probeBits st (seg 1 ℓ) ++ (probeBits st (seg 2 ℓ) ++
      (probeBits st (seg 4 ℓ) ++ (probeBits st (seg 5 ℓ) ++ (probeBits st (seg 9 ℓ) ++ probeBits st (seg 6 ℓ)))))) := by
    simp [probeBits, probesL]
  rw [hp]
  have l0 := length_probeBits_seg st 0 ℓ
  have l1 := length_probeBits_seg st 1 ℓ
  have l2 := length_probeBits_seg st 2 ℓ
  have l4 := length_probeBits_seg st 4 ℓ
  have l5 := length_probeBits_seg st 5 ℓ
  have l9 := length_probeBits_seg st 9 ℓ
  simp only [decode, List.take_left' l0, List.drop_left' l0, List.take_left' l1, List.drop_left' l1,
    List.take_left' l2, List.drop_left' l2, List.take_left' l4, List.drop_left' l4, List.take_left' l5,
    List.drop_left' l5, List.take_left' l9, List.drop_left' l9]
  simp only [probeBits_seg]
  have l6 : ((List.range ℓ).map fun j => decide (st.ar 6 (1 + j) ≠ 0)).length = ℓ := by simp
  rw [List.take_of_length_le l6.le]
  simp only [bval_numCells]

end ECDLP.L92
