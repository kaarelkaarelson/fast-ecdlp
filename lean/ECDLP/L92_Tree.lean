import ECDLP.L92_Merge

/-!
# L92 / Tree: generic bounded lookup commands (decision tree over probed cells, dispatch on `sc 0`)
`dtree P f` reads the cells `P` (pairs `(array, index)`), and sets scalar `3` to `f (nonzero-pattern of the cells)`.
`dispatch leaf k` runs `leaf (sc 0)` when `sc 0 < k`.
Both use only scalars `20, 21, 22` besides `3`, and never write arrays.
-/
namespace ECDLP.L92
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def dtree : List (ℕ × ℕ) → (List Bool → ℕ) → Cmd
  | [], f => .setK 3 (f [])
  | (a, i) :: ps, f => .seq (.setK 20 0) (.seq (.rd 21 a 20 i)
      (.ifZero 21 (dtree ps (fun bs => f (false :: bs))) (dtree ps (fun bs => f (true :: bs)))))

def probeBits (st : St) (P : List (ℕ × ℕ)) : List Bool := P.map fun q => decide (st.ar q.1 q.2 ≠ 0)

theorem dtree_run : ∀ (P : List (ℕ × ℕ)) (f : List Bool → ℕ) (st : St),
    (Cmd.run (dtree P f) st).1.sc 3 = f (probeBits st P) ∧ (Cmd.run (dtree P f) st).2 ≤ 5 * P.length + 1
  | [], f, st => by simp [dtree, probeBits, Cmd.run_setK]
  | (a, i) :: ps, f, st => by
      simp only [dtree, Cmd.run_seq, Cmd.run_setK, Cmd.run_rd, Cmd.run_ifZero, St.setSc_sc, St.setSc_ar,
        Function.update_self, zero_add, List.length_cons]
      have e21 : ((st.setSc 20 0).setSc 21 (st.ar a i)).sc 21 = st.ar a i := by simp
      have e21' : (((st.setSc 20 0).setSc 21 ((st.setSc 20 0).ar a ((st.setSc 20 0).sc 20 + i))).sc 21) = st.ar a i := by
        simp
      by_cases h0 : st.ar a i = 0
      · have := dtree_run ps (fun bs => f (false :: bs)) ((st.setSc 20 0).setSc 21 (st.ar a i))
        simp [h0, probeBits] at this ⊢
        obtain ⟨h1, h2⟩ := this
        refine ⟨h1, ?_⟩
        omega
      · have := dtree_run ps (fun bs => f (true :: bs)) ((st.setSc 20 0).setSc 21 (st.ar a i))
        simp [h0, probeBits] at this ⊢
        obtain ⟨h1, h2⟩ := this
        refine ⟨h1, ?_⟩
        omega

def dispatch (leaf : ℕ → Cmd) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (.setK 22 k) (.ifLt 0 22 (dispatch leaf k) (leaf k))

theorem dispatch_run (leaf : ℕ → Cmd) (G : ℕ → St → ℕ) (K cc : ℕ)
    (hl : ∀ ℓ (st : St), ℓ < K → (Cmd.run (leaf ℓ) st).1.sc 3 = G ℓ st ∧ (Cmd.run (leaf ℓ) st).2 ≤ cc)
    (hG : ∀ ℓ (st : St) (v : ℕ), G ℓ (st.setSc 22 v) = G ℓ st) :
    ∀ (k : ℕ) (st : St), k ≤ K → st.sc 0 < k →
      (Cmd.run (dispatch leaf k) st).1.sc 3 = G (st.sc 0) st ∧ (Cmd.run (dispatch leaf k) st).2 ≤ 3 * k + cc
  | 0, st, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, st, hK, h => by
      have e0 : (st.setSc 22 k).sc 0 = st.sc 0 := by simp [St.setSc, Function.update_of_ne]
      have e22 : (st.setSc 22 k).sc 22 = k := by simp [St.setSc]
      simp only [dispatch, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, e0, e22]
      by_cases hk : st.sc 0 < k
      · have := dispatch_run leaf G K cc hl hG k (st.setSc 22 k) (by omega) (by rw [e0]; exact hk)
        rw [e0, hG] at this
        simp only [hk, if_true]
        exact ⟨this.1, by omega⟩
      · have hk' : st.sc 0 = k := by omega
        have := hl k (st.setSc 22 k) (by omega)
        rw [hG] at this
        simp only [hk, if_false]
        refine ⟨by rw [hk', this.1], by omega⟩

end ECDLP.L92
