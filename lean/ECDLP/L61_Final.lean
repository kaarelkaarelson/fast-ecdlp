import ECDLP.L61_Driver
import ECDLP.L61_Machine

/-!
# L61 / Final: the Turing-machine driver for the audit statement, from an abstract zero-test oracle

`ZSpec m c T` : the oracle command `c` (a `Cmd` of Rudich's source language) decides `0 < Zc m x τ`
(the number of strings of the instance `x` with prefix `τ`) within `T (|enc x|)` source steps, for the prefixes `τ`
the driver asks about.  Then (`driver_machine`) there is ONE `TM2ComputableInTime encB encOut (lexLeast m)`
with explicit time `cc * (Q * (L + k0 + drvBound m L (T L) + 1)^2 + L + 1)^3 + 1`, i.e.
`≤ C (L+1)^6 (T L + 1)^6` (`driver_time_poly`), and `p^{o(1)}` oracle bounds give `p^{o(1)}` time (`driver_subexp`).
-/
namespace ECDLP.L61
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Turing Computability

/-- The prefixes the driver asks about. -/
def okInst (m : ℕ) (x : Inst) (τ : List Bool) : Prop :=
  pre x <+: τ ∧ τ.length ≤ max (nlen m x + 1) (pre x).length

/-- **The oracle contract.**  `c` preserves scalars `< 10` (except the answer scalar `3`) and arrays `< 3`; on a state
holding the input code of `x` in array 0 (length in scalar 0), the prefix `τ` in array 1 (bits as `0/1`, length in
scalar 2), with `τ` an extension of the prefix of `x` of length `≤ max (n+1) |π|` (`n` the string length), it leaves
`[0 < Zc m x τ]` in scalar 3 within `T |enc x|` source steps. -/
structure ZSpec (m : ℕ) (c : Cmd) (T : ℕ → ℕ) : Prop where
  keep : Keep c
  spec : ∀ (x : Inst) (st : St) (τ : List Bool), st.sc 0 = (encB x).length →
    st.ar 0 = startingMemory (encB x) → st.sc 2 = τ.length →
    (∀ j, j < τ.length → st.ar 1 j = bitN (τ.getD j false)) → okInst m x τ →
    (Cmd.run c st).1.sc 3 = (if 0 < Zc m x τ then 1 else 0) ∧ (Cmd.run c st).2 ≤ T (encB x).length

theorem Zc_pos_len (m : ℕ) (x : Inst) (τ : List Bool) (h : 0 < Zc m x τ) : τ.length ≤ nlen m x := by
  have hne : (strings m (withPre x τ)).Nonempty := Set.nonempty_of_ncard_ne_zero (by unfold Zc at h; omega)
  obtain ⟨s, hs⟩ := hne
  have h1 := (strings_pre m (withPre x τ) hs).length_le
  have h2 := strings_len'' m x τ hs
  exact h2 ▸ h1

theorem walk_inv (m : ℕ) (x : Inst) (h0 : 0 < Zc m x (pre x)) :
    ∀ i, pre x <+: ((stepF (Zc m x))^[i] (pre x, false)).1 ∧
      (((stepF (Zc m x))^[i] (pre x, false)).2 = false → 0 < Zc m x ((stepF (Zc m x))^[i] (pre x, false)).1)
  | 0 => ⟨List.prefix_refl _, fun _ => h0⟩
  | i + 1 => by
      rw [Function.iterate_succ_apply']
      obtain ⟨hp, hz⟩ := walk_inv m x h0 i
      generalize (stepF (Zc m x))^[i] (pre x, false) = q at hp hz
      obtain ⟨τ, d⟩ := q
      cases d
      · have hz' := hz rfl
        simp only at hp hz'
        by_cases h1 : 0 < Zc m x (τ ++ [false])
        · have hst : stepF (Zc m x) (τ, false) = (τ ++ [false], false) := by simp [stepF, h1]
          rw [hst]
          exact ⟨hp.trans (List.prefix_append _ _), fun _ => h1⟩
        · by_cases h2 : 0 < Zc m x (τ ++ [true])
          · have hst : stepF (Zc m x) (τ, false) = (τ ++ [true], false) := by simp [stepF, h1, h2]
            rw [hst]
            exact ⟨hp.trans (List.prefix_append _ _), fun _ => h2⟩
          · have hst : stepF (Zc m x) (τ, false) = (τ, true) := by simp [stepF, h1, h2]
            rw [hst]
            exact ⟨hp, fun h => absurd h (by simp)⟩
      · simp only [stepF]
        exact ⟨hp, fun h => absurd h (by simp)⟩

theorem len_encB_ge (p a b x y : ℕ) (π : List Bool) :
    (encodeNat p).length ≤ (encB (p, a, b, x, y, π)).length := by
  have := block_length (encodeNat p)
  simp only [encB, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  omega

theorem pre_len_le (x : Inst) : (pre x).length ≤ (encB x).length := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  have := block_length π
  simp only [pre, encB, List.length_append]
  omega

theorem driver_out (m : ℕ) (c : Cmd) (T : ℕ → ℕ) (h : ZSpec m c T) (x : Inst) :
    outOf ((srcOut (drvZ m c) (encB x)).ar 2) = encOut (lexLeast m x) ∧
      srcCost (drvZ m c) (encB x) ≤ drvBound m (encB x).length (T (encB x).length) := by
  obtain ⟨p, a, b, xR, yR, π⟩ := x
  set x : Inst := (p, a, b, xR, yR, π) with hx
  have hxs : encB x = block (pre x) ++ [p, a, b, xR, yR].flatMap (fun n => block (encodeNat n)) := rfl
  set L := (encB x).length with hL
  have ho : Orc (c) (startingMemory (encB x)) L (Zc m x) (okInst m x) (T L) :=
    ⟨fun st τ h0 hA h2 hc hok => h.spec x st τ h0 hA h2 hc hok⟩
  have hπ : okInst m x (pre x) := ⟨List.prefix_refl _, le_max_right _ _⟩
  have hW : 0 < Zc m x (pre x) → ∀ i, i < m * (L + 1) + 1 → ((stepF (Zc m x))^[i] (pre x, false)).2 = false →
      okInst m x (((stepF (Zc m x))^[i] (pre x, false)).1 ++ [false]) ∧
      okInst m x (((stepF (Zc m x))^[i] (pre x, false)).1 ++ [true]) := by
    intro h0 i _ hd
    obtain ⟨hp, hz⟩ := walk_inv m x h0 i
    have hl := Zc_pos_len m x _ (hz hd)
    refine ⟨⟨hp.trans (List.prefix_append _ _), ?_⟩, ⟨hp.trans (List.prefix_append _ _), ?_⟩⟩ <;>
      simp only [List.length_append, List.length_singleton] <;> omega
  obtain ⟨h1, h2⟩ := drvZ_spec m c (encB x) (pre x) _ hxs (Zc m x) (okInst m x) (T L) h.keep ho hπ hW
  refine ⟨?_, h2⟩
  rw [h1]
  congr 1
  rw [lexLeast_eq_iter m x (m * (L + 1) + 1)]
  intro hpos
  have := Zc_pos_len m x _ hpos
  have hn : nlen m x ≤ m * ((encodeNat p).length + 1) := nlen_le m p a b xR yR π
  have hp : (encodeNat p).length ≤ L := len_encB_ge p a b xR yR π
  have : m * ((encodeNat p).length + 1) ≤ m * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

end ECDLP.L61
