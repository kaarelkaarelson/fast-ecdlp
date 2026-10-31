import ECDLP.L102_Loops

/-!
# L102 / Eng: the m = 1 engine `eng1` : value and cost
-/
namespace ECDLP.L102
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L71

def outC : Cmd := .ifZero 21 (.setK 3 1) (.setK 3 0)

def eng1 : Cmd := .seq stage1 (.seq stage2 (.seq stage3 (.seq prep (.seq stage5 outC))))

def S1 (s : St) : St := (Cmd.run stage1 s).1
def S2 (s : St) : St := (Cmd.run stage2 (S1 s)).1
def S3 (s : St) : St := (Cmd.run stage3 (S2 s)).1
def S4 (s : St) : St := (Cmd.run prep (S3 s)).1
def S5 (s : St) : St := (Cmd.run stage5 (S4 s)).1

theorem run_eng1 (s : St) :
    (Cmd.run eng1 s).1 = (Cmd.run outC (S5 s)).1 ∧
    (Cmd.run eng1 s).2 = (Cmd.run stage1 s).2 + ((Cmd.run stage2 (S1 s)).2 + ((Cmd.run stage3 (S2 s)).2 +
      ((Cmd.run prep (S3 s)).2 + ((Cmd.run stage5 (S4 s)).2 + (Cmd.run outC (S5 s)).2 + 1) + 1) + 1) + 1) + 1 := by
  simp only [eng1, S1, S2, S3, S4, S5, Cmd.run_seq]
  exact ⟨trivial, trivial⟩

theorem outC_sc3 (t : St) : (Cmd.run outC t).1.sc 3 = if t.sc 21 = 0 then 1 else 0 := by
  by_cases h : t.sc 21 = 0 <;> simp [outC, Cmd.run_ifZero, Cmd.run_setK, h]

theorem outC_cost (t : St) : (Cmd.run outC t).2 ≤ 2 := by
  by_cases h : t.sc 21 = 0 <;> simp [outC, Cmd.run_ifZero, Cmd.run_setK, h]

/-! ### facts, for every state -/

theorem S1_facts (s : St) : (S1 s).sc 10 = Nat.size (numCells (s.ar 0) 1 (s.sc 0)) ∧ (S1 s).ar = s.ar ∧
    (S1 s).sc 0 = s.sc 0 := by
  obtain ⟨a, b, c, -⟩ := stage1_run s
  exact ⟨a, b, c 0 (by norm_num) (by norm_num) (by norm_num)⟩

theorem S2_facts (s : St) : (S2 s).sc 14 = numCells (s.ar 9) 1 (Nat.size (s.sc 0)) ∧ (S2 s).ar = s.ar ∧
    (S2 s).sc 0 = s.sc 0 ∧ (S2 s).sc 10 = (S1 s).sc 10 := by
  obtain ⟨-, a, b, c, -⟩ := stage2_run (S1 s)
  obtain ⟨d, e, f⟩ := S1_facts s
  obtain ⟨a', -, -, -, -⟩ := stage2_run (S1 s)
  refine ⟨?_, by rw [S2, b, e], ?_, ?_⟩
  · have := (stage2_run (S1 s)).2.1
    rw [S2, this, e, f]
  · rw [S2, c 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), f]
  · rw [S2, c 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

theorem S3_facts (s : St) : (S3 s).sc 18 = (if numCells (s.ar 0) 1 (s.sc 0) ≤ Bs (s.ar 5) (s.sc 0) then 1 else 0) ∧
    (S3 s).ar = s.ar ∧ (S3 s).sc 0 = s.sc 0 ∧ (S3 s).sc 10 = (S1 s).sc 10 ∧ (S3 s).sc 14 = (S2 s).sc 14 := by
  obtain ⟨a, b, c, -⟩ := stage3_run (S2 s)
  obtain ⟨d1, d2, d3, d4⟩ := S2_facts s
  refine ⟨?_, by rw [S3, b, d2], ?_, ?_, ?_⟩
  · rw [S3, a, d2, d3]
  · rw [S3, c 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), d3]
  · rw [S3, c 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num), d4]
  · rw [S3, c 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

theorem S4_facts (s : St) : (S4 s).sc 21 = (if (S1 s).sc 10 + 1 < (S2 s).sc 14 then 0 else 1) ∧
    (S4 s).sc 22 = (S1 s).sc 10 ∧ (S4 s).sc 17 = (if (S1 s).sc 10 + 1 < (S2 s).sc 14 then 0 else (S2 s).sc 14) ∧
    (S4 s).sc 10 = (S1 s).sc 10 ∧ (S4 s).sc 18 = (S3 s).sc 18 ∧ (S4 s).ar = s.ar := by
  obtain ⟨a, b, c, d, e, f, g, -⟩ := prep_run (S3 s)
  obtain ⟨h1, h2, h3, h4, h5⟩ := S3_facts s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S4, a, h4, h5]
  · rw [S4, b, h4]
  · rw [S4, c, h4, h5]
  · rw [S4, d, h4]
  · rw [S4, e]
  · rw [S4, g, h2]

theorem arith_cost (L k1 k2 k3 k4 k5 k6 bb : ℕ) (h1 : k1 ≤ 7 * L + 3) (h2 : k2 ≤ L * (8 * L + 30) + 6)
    (h3 : k3 ≤ 15 * L + 3) (h4 : k4 ≤ 12) (h5 : k5 ≤ bb * 21 + 1) (h6 : k6 ≤ 2) (hb : bb ≤ L + 1) :
    k1 + (k2 + (k3 + (k4 + (k5 + k6 + 1) + 1) + 1) + 1) + 1 ≤ 100 * (L + 1) ^ 2 := by
  have : bb * 21 ≤ (L + 1) * 21 := Nat.mul_le_mul_right _ hb
  nlinarith [Nat.zero_le L]

theorem eng1_cost (s : St) : (Cmd.run eng1 s).2 ≤ 100 * (s.sc 0 + 1) ^ 2 := by
  obtain ⟨-, hc⟩ := run_eng1 s
  rw [hc]
  obtain ⟨a1, b1, c1⟩ := S1_facts s
  obtain ⟨a2, b2, c2, d2⟩ := S2_facts s
  have s1c := (stage1_run s).2.2.2
  have s2c := (stage2_run (S1 s)).2.2.2.2
  have s3c := (stage3_run (S2 s)).2.2.2
  have pc := (prep_run (S3 s)).2.2.2.2.2.2.2
  have s5c := stage5_cost (S4 s)
  have oc := outC_cost (S5 s)
  obtain ⟨-, -, f3, -⟩ := S4_facts s
  rw [c1] at s2c
  rw [c2] at s3c
  have hW : (S1 s).sc 10 ≤ s.sc 0 := by rw [a1]; exact size_numCells_le _ _ _
  have h17 : (S4 s).sc 17 ≤ (S1 s).sc 10 + 1 := by
    rw [f3]; split_ifs <;> omega
  exact arith_cost _ _ _ _ _ _ _ _ s1c s2c s3c pc s5c oc (by omega)

end ECDLP.L102
