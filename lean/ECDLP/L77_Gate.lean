import ECDLP.L77_Top
import ECDLP.L71_Guard

/-!
# L77 / Gate: the one-time gate from L71's primality guard plus an abstract hook for the input-layer checks

* `envelope` : a family of bounds `C_k 2^(L/k)` collapses into one function `Tg` with `cost ≤ Tg L` and `Tg L ≤ C_k 2^(L/k)`.
* `gate_prime` : `GateSpec Prime (guardPrime S q) 1204 Tg` (the parser's preconditions survive the guard: syntactic frames
  `Cmd.run_sc_frame`/`Cmd.run_ar_frame` for `feed`, `primePre`, `cmpC`, and `LowEq S` for the shifted `minFac` subroutine).
* `HookSpec` / `gate_hook` : `G = guardPrime ; ifZero 1204 (setK fl 0) (H ; copy fl fl2)`, `H` an abstract command
  (L76's input layer: `Δ ≠ 0`, `R` nonsingular, ...) specified from ANY state holding the input; flag `fl ≠ 0` iff `Prime ∧ F2`.
-/
namespace ECDLP.L77
open ECDLP ECDLP.L61 ECDLP.L71 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

theorem envelope (C : ℕ → ℕ) : ∃ Tg : ℕ → ℕ, (∀ L v, (∀ k, 1 ≤ k → v ≤ C k * 2 ^ (L / k)) → v ≤ Tg L) ∧
    ∀ k, 1 ≤ k → ∀ L, Tg L ≤ C k * 2 ^ (L / k) := by
  refine ⟨fun L => ⨅ k : ℕ, C (k + 1) * 2 ^ (L / (k + 1)), fun L v hv => ?_, fun k hk L => ?_⟩
  · exact le_ciInf fun k => hv (k + 1) (by omega)
  · have := ciInf_le (OrderBot.bddBelow (Set.range fun k' : ℕ => C (k' + 1) * 2 ^ (L / (k' + 1)))) (k - 1)
    have e : k - 1 + 1 = k := by omega
    simpa [e] using this

theorem sc_frame_feed (S q y : ℕ) (hS : 1400 ≤ S) (hy : y < 1200) : y ∉ (feed S q).wsc := by
  simp only [feed, feedBody, feedFin, Cmd.wsc, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem ar_frame_feed (S q : ℕ) (hq : 1 ≤ q) (hqS : q < S) : 0 ∉ (feed S q).war := by
  simp only [feed, feedBody, feedFin, Cmd.war, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem sc_frame_prime (q y : ℕ) (hy : y < 1200) : y ∉ (primePre q).wsc := by
  simp only [primePre, Cmd.wsc, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem sc_frame_cmp (q o y : ℕ) (hy : y < 1200) : y ∉ (cmpC q o).wsc := by
  simp only [cmpC, cmpPre, cmpBody, neqSet, normB, Cmd.wsc, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem ar_frame_prime (q : ℕ) : 0 ∉ (primePre q).war := by simp [primePre, Cmd.war]

theorem ar_frame_cmp (q o : ℕ) : 0 ∉ (cmpC q o).war := by
  simp [cmpC, cmpPre, cmpBody, neqSet, normB, Cmd.war]

theorem init_unshift (S : ℕ) (hS : 1 ≤ S) (xs : List Bool) : unshift S (St.init xs) = St.init [] := by
  apply St.ext
  · funext i; simp [unshift, St.init]; intro h; exact absurd h (by omega)
  · funext a
    have hS0 : S ≠ 0 := by omega
    have e : startingMemory ([] : List Bool) = fun _ => 0 := by
      funext i; simp [startingMemory]
    simp [unshift, St.init, hS0, e]

/-- low part of the guard's effect on `St.init (encB x)`: scalars `< 1200` and array `0` are untouched -/
theorem guardPrime_low (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (st : St) :
    (∀ y, y < 1200 → (Cmd.run (guardPrime S q) st).1.sc y = st.sc y) ∧
    (Cmd.run (guardPrime S q) st).1.ar 0 = st.ar 0 := by
  have h1 := run_shift S (drvC (uniC UP))
  constructor
  · intro y hy
    simp only [guardPrime, primeFlag, Cmd.run_seq]
    rw [Cmd.run_sc_frame (cmpC q (S + 2)) _ y (sc_frame_cmp _ _ y hy)]
    have hm := (run_shift S (drvC (uniC UP)) (Cmd.run (primePre q) (Cmd.run (feed S q) st).1).1).2.2
    rw [show minFacCmd S = (drvC (uniC UP)).shift S from rfl]
    rw [← hm.1 y (by omega)]
    rw [Cmd.run_sc_frame _ _ y (sc_frame_prime q y hy), Cmd.run_sc_frame _ _ y (sc_frame_feed S q y hS hy)]
  · simp only [guardPrime, primeFlag, Cmd.run_seq]
    rw [Cmd.run_ar_frame (cmpC q (S + 2)) _ 0 (ar_frame_cmp _ _)]
    have hm := (run_shift S (drvC (uniC UP)) (Cmd.run (primePre q) (Cmd.run (feed S q) st).1).1).2.2
    rw [show minFacCmd S = (drvC (uniC UP)).shift S from rfl]
    rw [← hm.2 0 (by omega)]
    rw [Cmd.run_ar_frame _ _ 0 (ar_frame_prime q), Cmd.run_ar_frame _ _ 0 (ar_frame_feed S q hq1 hqS)]

theorem gate_prime (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) :
    ∃ Tg : ℕ → ℕ, GateSpec (fun x => x.1.Prime) (guardPrime S q) 1204 Tg ∧
      ∀ k, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k) := by
  classical
  choose! C hC using fun k (hk : 1 ≤ k) => guardPrime_spec S q hS hq1 hqS k hk
  obtain ⟨Tg, hT1, hT2⟩ := envelope C
  refine ⟨Tg, ⟨fun x => ?_⟩, fun k hk => ⟨C k, hT2 k hk⟩⟩
  have h0 : (St.init (encB x)).sc 0 = (encB x).length := rfl
  have hA : (St.init (encB x)).ar 0 = startingMemory (encB x) := rfl
  have hlow := guardPrime_low S q hS hq1 hqS (St.init (encB x))
  have hsc : ∀ y, y ≠ 0 → y < 1200 → (St.init (encB x)).sc y = 0 := fun y hy _ => by simp [St.init, hy]
  have key : ∀ k, 1 ≤ k → _ := fun k hk => hC k hk x (St.init (encB x)) h0 hA (init_unshift S (by omega) _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlow.1 0 (by norm_num)]; exact h0
  · rw [hlow.2]; exact hA
  · rw [hlow.1 2 (by norm_num)]; exact hsc 2 (by norm_num) (by norm_num)
  · rw [hlow.1 5 (by norm_num)]; exact hsc 5 (by norm_num) (by norm_num)
  · rw [hlow.1 7 (by norm_num)]; exact hsc 7 (by norm_num) (by norm_num)
  · rw [hlow.1 8 (by norm_num)]; exact hsc 8 (by norm_num) (by norm_num)
  · have := (key 1 le_rfl).1
    rw [this]
    by_cases hp : x.1.Prime <;> simp [hp]
  · exact hT1 _ _ fun k hk => (key k hk).2

/-- **The hook** (abstract; L76's input layer): a command run AFTER the primality guard, from any state that holds the input
(`sc 0`, `ar 0`), on prime-`p` instances; it keeps the parser's preconditions and puts `[F2 x]` in scalar `fl2`
(`0` iff `¬ F2 x`) within `Th |encB x|` steps. -/
structure HookSpec (F1 F2 : Inst → Prop) (H : Cmd) (fl2 : ℕ) (Th : ℕ → ℕ) : Prop where
  keep_sc : ∀ (st : St) (y : ℕ), (y = 0 ∨ y = 2 ∨ y = 5 ∨ y = 7 ∨ y = 8) → (Cmd.run H st).1.sc y = st.sc y
  keep_ar : ∀ st : St, (Cmd.run H st).1.ar 0 = st.ar 0
  spec : ∀ (x : Inst) (st : St), F1 x → st.sc 0 = (encB x).length → st.ar 0 = startingMemory (encB x) →
    ((Cmd.run H st).1.sc fl2 = 0 ↔ ¬ F2 x) ∧ (Cmd.run H st).2 ≤ Th (encB x).length

/-- `guardPrime ; ifZero 1204 (fl := 0) (H ; fl := fl2)`. -/
def gateCmd (S q : ℕ) (H : Cmd) (fl fl2 : ℕ) : Cmd :=
  .seq (guardPrime S q) (.ifZero 1204 (.setK fl 0) (.seq H (.copy fl fl2)))

theorem gate_hook (S q : ℕ) (hS : 1400 ≤ S) (hq1 : 1 ≤ q) (hqS : q < S) (F2 : Inst → Prop) (H : Cmd) (fl fl2 : ℕ)
    (hfl : 10 ≤ fl) (Th : ℕ → ℕ) (hH : HookSpec (fun x => x.1.Prime) F2 H fl2 Th) :
    ∃ Tg : ℕ → ℕ, GateSpec (fun x => x.1.Prime ∧ F2 x) (gateCmd S q H fl fl2) fl Tg ∧
      ((∀ k, 1 ≤ k → ∃ C : ℕ, ∀ L, Th L ≤ C * 2 ^ (L / k)) →
        ∀ k, 1 ≤ k → ∃ C : ℕ, ∀ L, Tg L ≤ C * 2 ^ (L / k)) := by
  classical
  obtain ⟨Tp, hP, hPs⟩ := gate_prime S q hS hq1 hqS
  refine ⟨fun L => Tp L + Th L + 5, ⟨fun x => ?_⟩, fun hT k hk => ?_⟩
  · obtain ⟨g0, gA, g2, g5, g7, g8, gf, gc⟩ := hP.spec x
    simp only [gateCmd, Cmd.run_seq, Cmd.run_ifZero]
    generalize Cmd.run (guardPrime S q) (St.init (encB x)) = r at g0 gA g2 g5 g7 g8 gf gc ⊢
    by_cases hp : x.1.Prime
    · have hz : r.1.sc 1204 ≠ 0 := fun h => (gf.1 h) hp
      simp only [hz, if_false, Cmd.run_seq, Cmd.run_copy]
      obtain ⟨hf, hc⟩ := hH.spec x r.1 hp g0 gA
      have k := fun y hy => hH.keep_sc r.1 y hy
      simp only [St.setSc_sc, Function.update_apply, St.setSc_ar]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [if_neg (by omega), k 0 (by simp), g0]
      · rw [hH.keep_ar, gA]
      · rw [if_neg (by omega), k 2 (by simp), g2]
      · rw [if_neg (by omega), k 5 (by simp), g5]
      · rw [if_neg (by omega), k 7 (by simp), g7]
      · rw [if_neg (by omega), k 8 (by simp), g8]
      · simp only [if_true]; rw [hf]; simp [hp]
      · omega
    · have hz : r.1.sc 1204 = 0 := gf.2 hp
      simp only [hz, if_true, Cmd.run_setK]
      simp only [St.setSc_sc, Function.update_apply, St.setSc_ar]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [if_neg (by omega), g0]
      · exact gA
      · rw [if_neg (by omega), g2]
      · rw [if_neg (by omega), g5]
      · rw [if_neg (by omega), g7]
      · rw [if_neg (by omega), g8]
      · simp [hp]
      · omega
  · obtain ⟨C1, h1⟩ := hPs k hk
    obtain ⟨C2, h2⟩ := hT k hk
    refine ⟨C1 + C2 + 5, fun L => ?_⟩
    have p1 : 1 ≤ 2 ^ (L / k) := Nat.one_le_two_pow
    have := h1 L
    have := h2 L
    nlinarith

end ECDLP.L77
