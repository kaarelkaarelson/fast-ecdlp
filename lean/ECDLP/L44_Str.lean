import ECDLP.L44_Gen

/-!
# L44 / Str: the prefix predicate on L35's string

`strOf p ℓ P` is L35's string of a tuple of points (for each point: the `ℓ` bits of `x` big-endian, then
`[(p-1)/2 < y]`), with `ℓ = Nat.size B`.  `prefix_iff_QP`: for a prefix `π` of length `≤ (n+1)(ℓ+1)`,
`π <+: strOf p ℓ P ↔ QP p (xcOf ℓ π) (sgOf ℓ π) P`.
-/
namespace ECDLP.L44

/-- the bits of one point -/
def chunk (p ℓ : ℕ) (pt : ZMod p × ZMod p) : List Bool :=
  (List.range ℓ).reverse.map (fun j => pt.1.val.testBit j) ++ [decide ((p - 1) / 2 < pt.2.val)]

/-- the string of a tuple (as in `ECDLP.strings`, L35) -/
def strOf {n : ℕ} (p ℓ : ℕ) (P : Fin (n + 1) → ZMod p × ZMod p) : List Bool :=
  (List.ofFn fun i => chunk p ℓ (P i)).flatten

theorem chunk_length (p ℓ : ℕ) (pt : ZMod p × ZMod p) : (chunk p ℓ pt).length = ℓ + 1 := by
  simp [chunk]

theorem chunk_get_x (p ℓ : ℕ) (pt : ZMod p × ZMod p) {q : ℕ} (hq : q < ℓ) :
    (chunk p ℓ pt)[q]? = some (pt.1.val.testBit (ℓ - 1 - q)) := by
  unfold chunk
  rw [List.getElem?_append_left (by simpa using hq)]
  simp [hq]

theorem chunk_get_s (p ℓ : ℕ) (pt : ZMod p × ZMod p) :
    (chunk p ℓ pt)[ℓ]? = some (decide ((p - 1) / 2 < pt.2.val)) := by
  unfold chunk
  rw [List.getElem?_append_right (by simp)]
  simp

theorem flat_get {m c : ℕ} (f : Fin m → List Bool) (hf : ∀ i, (f i).length = c) :
    ∀ pos (h : pos < m * c), (List.ofFn f).flatten[pos]? =
      (f ⟨pos / c, (Nat.div_lt_iff_lt_mul (by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · subst h0; simp at h
        · exact h0)).2 h⟩)[pos % c]? := by
  induction m with
  | zero => intro pos h; simp at h
  | succ m ih =>
    intro pos h
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at h
      · exact h0
    rw [List.ofFn_succ, List.flatten_cons]
    by_cases hp : pos < c
    · rw [List.getElem?_append_left (by rw [hf 0]; exact hp)]
      have e1 : pos / c = 0 := Nat.div_eq_of_lt hp
      have e2 : pos % c = pos := Nat.mod_eq_of_lt hp
      simp only [e2]
      congr 2
      exact Fin.ext e1.symm
    · rw [not_lt] at hp
      rw [List.getElem?_append_right (by rw [hf 0]; exact hp), hf 0]
      have h' : pos - c < m * c := by
        have : (m + 1) * c = m * c + c := by ring
        omega
      rw [ih (fun i => f i.succ) (fun i => hf _) (pos - c) h']
      have e1 : (pos - c) / c + 1 = pos / c := by
        have := Nat.add_div_right (pos - c) hc
        rw [Nat.sub_add_cancel hp] at this
        exact this.symm
      have e2 : (pos - c) % c = pos % c := by
        have := Nat.add_mod_right (pos - c) c
        rw [Nat.sub_add_cancel hp] at this
        exact this.symm
      simp only [e2]
      congr 2
      exact Fin.ext e1

/-- `x`-bit constraints of point `i` induced by a prefix -/
def xcOf (ℓ : ℕ) (π : List Bool) (i : ℕ) : List (ℕ × Bool) :=
  (List.range ℓ).filterMap fun q => (π[i * (ℓ + 1) + q]?).map fun β => (ℓ - 1 - q, β)

/-- sign requirement of point `i` induced by a prefix -/
def sgOf (ℓ : ℕ) (π : List Bool) (i : ℕ) : Sg :=
  match π[i * (ℓ + 1) + ℓ]? with
  | none => .none
  | some true => .pos
  | some false => .neg

theorem divmod (i q c : ℕ) (hq : q < c) : (i * c + q) / c = i ∧ (i * c + q) % c = q := by
  have hc : 0 < c := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hq]; simp
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem prefix_iff_QP {n : ℕ} (p ℓ : ℕ) (π : List Bool) (hlen : π.length ≤ (n + 1) * (ℓ + 1))
    (P : Fin (n + 1) → ZMod p × ZMod p) :
    π <+: strOf p ℓ P ↔ QP p (fun i : Fin (n + 1) => xcOf ℓ π i) (fun i : Fin (n + 1) => sgOf ℓ π i) P := by
  have hget : ∀ pos (h : pos < (n + 1) * (ℓ + 1)), (strOf p ℓ P)[pos]? =
      (chunk p ℓ (P ⟨pos / (ℓ + 1), (Nat.div_lt_iff_lt_mul (by omega)).2 h⟩))[pos % (ℓ + 1)]? :=
    fun pos h => flat_get (fun i => chunk p ℓ (P i)) (fun i => chunk_length p ℓ _) pos h
  have hat : ∀ (i : Fin (n + 1)) (q : ℕ), q ≤ ℓ → ∀ β, π[i * (ℓ + 1) + q]? = some β →
      i * (ℓ + 1) + q < π.length ∧ (strOf p ℓ P)[i * (ℓ + 1) + q]? = (chunk p ℓ (P i))[q]? := by
    intro i q hq β hβ
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hβ
    refine ⟨hlt, ?_⟩
    have hlt' : i * (ℓ + 1) + q < (n + 1) * (ℓ + 1) := lt_of_lt_of_le hlt hlen
    rw [hget _ hlt']
    obtain ⟨d1, d2⟩ := divmod i q (ℓ + 1) (by omega)
    simp only [d2]
    congr 3
    exact Fin.ext d1
  rw [List.prefix_iff_getElem?]
  constructor
  · intro H i
    refine ⟨fun jb hjb => ?_, ?_⟩
    · simp only [xcOf, List.mem_filterMap, List.mem_range] at hjb
      obtain ⟨q, hq, hπ⟩ := hjb
      cases hq' : π[i * (ℓ + 1) + q]? with
      | none => simp [hq'] at hπ
      | some β =>
        simp only [hq', Option.map_some, Option.some.injEq] at hπ
        subst hπ
        obtain ⟨hlt, he⟩ := hat i q hq.le β hq'
        have h1 := H _ hlt
        rw [he, chunk_get_x p ℓ _ hq] at h1
        have h2 : π[i * (ℓ + 1) + q] = β := by
          have := List.getElem?_eq_getElem hlt (l := π)
          rw [hq'] at this
          exact (Option.some.inj this).symm
        rw [h2] at h1
        exact Option.some.inj h1
    · show SgN p (sgOf ℓ π i) _
      cases hq' : π[i * (ℓ + 1) + ℓ]? with
      | none => simp [sgOf, hq', SgN]
      | some β =>
        obtain ⟨hlt, he⟩ := hat i ℓ le_rfl β hq'
        have h1 := H _ hlt
        rw [he, chunk_get_s] at h1
        have h2 : π[i * (ℓ + 1) + ℓ] = β := by
          have := List.getElem?_eq_getElem hlt (l := π)
          rw [hq'] at this
          exact (Option.some.inj this).symm
        rw [h2] at h1
        have h3 := Option.some.inj h1
        cases β
        · simp only [sgOf, hq', SgN]
          simpa using h3
        · simp only [sgOf, hq', SgN]
          simpa using h3
  · intro Q pos hpos
    have hlt' : pos < (n + 1) * (ℓ + 1) := lt_of_lt_of_le hpos hlen
    rw [hget pos hlt']
    set i : Fin (n + 1) := ⟨pos / (ℓ + 1), (Nat.div_lt_iff_lt_mul (by omega)).2 hlt'⟩ with hi
    have hdm : pos = i * (ℓ + 1) + pos % (ℓ + 1) := (Nat.div_add_mod' pos (ℓ + 1)).symm
    have hr : pos % (ℓ + 1) < ℓ + 1 := Nat.mod_lt _ (by omega)
    have hπ : π[pos]? = some π[pos] := List.getElem?_eq_getElem hpos
    by_cases hq : pos % (ℓ + 1) < ℓ
    · rw [chunk_get_x p ℓ _ hq]
      have hmem : (ℓ - 1 - pos % (ℓ + 1), π[pos]) ∈ xcOf ℓ π i := by
        simp only [xcOf, List.mem_filterMap, List.mem_range]
        refine ⟨pos % (ℓ + 1), hq, ?_⟩
        rw [← hdm, hπ]; rfl
      exact congrArg some (by simpa using ((Q i).1 _ hmem))
    · have hqe : pos % (ℓ + 1) = ℓ := by omega
      rw [hqe, chunk_get_s]
      have hs := (Q i).2
      have hpos' : i * (ℓ + 1) + ℓ = pos := by rw [hqe] at hdm; exact hdm.symm
      have hπ' : π[i * (ℓ + 1) + ℓ]? = some π[pos] := by rw [hpos']; exact hπ
      change SgN p (sgOf ℓ π i) _ at hs
      simp only [sgOf, hπ'] at hs
      cases hb : π[pos]
      · rw [hb] at hs
        simp only [SgN] at hs
        simpa using hs
      · rw [hb] at hs
        simp only [SgN] at hs
        simpa using hs

end ECDLP.L44
