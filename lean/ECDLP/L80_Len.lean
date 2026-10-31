import ECDLP.L80_Val

/-!
# L80 / Len: the sizes and the input length `len` of the reduced instance (scalars 810 .. 817)
`lenC` : scalar 810..814 := sizes of `p, a%p, b%p, xR%p, yR%p` (arrays 30, 21..24 of the work area), 815 := `len`, 817 := `2 len + 1`.
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def lenC : Cmd :=
  .seq (sizeList [(30, 810), (21, 811), (22, 812), (23, 813), (24, 814)])
    (.seq (.setK 815 1) (.seq (addList 815 816 [810, 811, 812, 813, 814, 2])
      (.seq (.setK 817 1) (addList 817 816 [815, 815]))))

def Zlen (y : ℕ) : Prop := y = 780 ∨ y = 781 ∨ (810 ≤ y ∧ y ≤ 817)

set_option maxHeartbeats 2000000 in
theorem lenC_run (s : St) (W p a b x y n2 : ℕ) (hW : s.sc 710 = W) (h30 : V (s.ar 30) W = p) (h21 : V (s.ar 21) W = a)
    (h22 : V (s.ar 22) W = b) (h23 : V (s.ar 23) W = x) (h24 : V (s.ar 24) W = y) (h2 : s.sc 2 = n2) :
    let r := Cmd.run lenC s
    r.1.sc 810 = Nat.size p ∧ r.1.sc 811 = Nat.size a ∧ r.1.sc 812 = Nat.size b ∧ r.1.sc 813 = Nat.size x ∧ r.1.sc 814 = Nat.size y ∧
    r.1.sc 815 = Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + n2 + 1 ∧
    r.1.sc 817 = 2 * r.1.sc 815 + 1 ∧ r.1.ar = s.ar ∧ (∀ z, ¬ Zlen z → r.1.sc z = s.sc z) ∧
    r.2 ≤ 35 * W + 6 * (Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + n2) + 100 := by
  intro r
  obtain ⟨A1, A2, A3, A4⟩ := sizeList_run W [(30, 810), (21, 811), (22, 812), (23, 813), (24, 814)] s hW
    (by intro q hq; simp at hq; rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp) (by simp)
  generalize hA : Cmd.run (sizeList [(30, 810), (21, 811), (22, 812), (23, 813), (24, 814)]) s = A at A1 A2 A3 A4
  have a810 : A.1.sc 810 = Nat.size p := by rw [A1 (30, 810) (by simp)]; dsimp only; rw [h30]
  have a811 : A.1.sc 811 = Nat.size a := by rw [A1 (21, 811) (by simp)]; dsimp only; rw [h21]
  have a812 : A.1.sc 812 = Nat.size b := by rw [A1 (22, 812) (by simp)]; dsimp only; rw [h22]
  have a813 : A.1.sc 813 = Nat.size x := by rw [A1 (23, 813) (by simp)]; dsimp only; rw [h23]
  have a814 : A.1.sc 814 = Nat.size y := by rw [A1 (24, 814) (by simp)]; dsimp only; rw [h24]
  have a2 : A.1.sc 2 = n2 := by rw [A3 2 (by norm_num) (by norm_num) (by simp), h2]
  have b815 : (A.1.setSc 815 1).sc 815 = 1 := by simp [St.setSc]
  have bk : ∀ z, z ≠ 815 → (A.1.setSc 815 1).sc z = A.1.sc z := fun z hz => by simp [St.setSc, hz]
  obtain ⟨C1, C2, C3, C4⟩ := addList_run 815 816 (by norm_num) [810, 811, 812, 813, 814, 2] (A.1.setSc 815 1) (by simp)
  have hsum : ([810, 811, 812, 813, 814, 2].map (A.1.setSc 815 1).sc).sum = Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + n2 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [bk 810 (by norm_num), bk 811 (by norm_num), bk 812 (by norm_num), bk 813 (by norm_num), bk 814 (by norm_num),
      bk 2 (by norm_num), a810, a811, a812, a813, a814, a2]
    omega
  rw [hsum, b815] at C1
  rw [hsum] at C4
  generalize hC : Cmd.run (addList 815 816 [810, 811, 812, 813, 814, 2]) (A.1.setSc 815 1) = C at C1 C2 C3 C4
  have d817 : (C.1.setSc 817 1).sc 817 = 1 := by simp [St.setSc]
  have dk : ∀ z, z ≠ 817 → (C.1.setSc 817 1).sc z = C.1.sc z := fun z hz => by simp [St.setSc, hz]
  obtain ⟨E1, E2, E3, E4⟩ := addList_run 817 816 (by norm_num) [815, 815] (C.1.setSc 817 1) (by simp)
  have hsum2 : ([815, 815].map (C.1.setSc 817 1).sc).sum = 2 * C.1.sc 815 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [dk 815 (by norm_num)]; omega
  rw [hsum2, d817] at E1
  rw [hsum2] at E4
  have hr : r = ((Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).1, A.2 + (1 + (C.2 + (1 + (Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).2 + 1) + 1) + 1) + 1) := by
    simp only [r, lenC, Cmd.run_seq, Cmd.run_setK, hA, hC]
  have c815 : C.1.sc 815 = Nat.size p + Nat.size a + Nat.size b + Nat.size x + Nat.size y + n2 + 1 := by rw [C1]; omega
  have hz : ∀ z, ¬ Zlen z → (Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).1.sc z = s.sc z := by
    intro z hz
    have h1 : z ≠ 817 := fun h => hz (by subst h; unfold Zlen; omega)
    have h3 : z ≠ 815 := fun h => hz (by subst h; unfold Zlen; omega)
    have h2 : z ≠ 816 := fun h => hz (by subst h; unfold Zlen; omega)
    have h4 : z ≠ 780 := fun h => hz (by subst h; unfold Zlen; omega)
    have h5 : z ≠ 781 := fun h => hz (by subst h; unfold Zlen; omega)
    rw [E3 z h1 h2, dk z h1, C3 z h3 h2, bk z h3, A3 z h4 h5]
    intro hm; simp at hm; rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact hz (by unfold Zlen; omega)
  rw [hr]
  have fin : ∀ z, z ≠ 817 → z ≠ 815 → z ≠ 816 → z ≠ 780 → z ≠ 781 → z ∉ [810, 811, 812, 813, 814] →
      (Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).1.sc z = A.1.sc z := by
    intro z h1 h2 h3 h4 h5 _
    rw [E3 z h1 h3, dk z h1, C3 z h2 h3, bk z h2]
  have g : ∀ z v, z ∈ [810, 811, 812, 813, 814] → A.1.sc z = v →
      (Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).1.sc z = v := by
    intro z v hz hv
    have h1 : z ≠ 817 := by simp at hz; omega
    have h2 : z ≠ 815 := by simp at hz; omega
    have h3 : z ≠ 816 := by simp at hz; omega
    rw [E3 z h1 h3, dk z h1, C3 z h2 h3, bk z h2, hv]
  have e815 : (Cmd.run (addList 817 816 [815, 815]) (C.1.setSc 817 1)).1.sc 815 = C.1.sc 815 := by
    rw [E3 815 (by norm_num) (by norm_num), dk 815 (by norm_num)]
  refine ⟨g 810 _ (by simp) a810, g 811 _ (by simp) a811, g 812 _ (by simp) a812, g 813 _ (by simp) a813, g 814 _ (by simp) a814,
    ?_, ?_, ?_, hz, ?_⟩
  · rw [e815, c815]
  · rw [E1, e815]; ring
  · rw [E2]; simp only [St.setSc]; rw [C2]; simp only [St.setSc]; exact A2
  · simp only [List.length_cons, List.length_nil] at A4 C4 E4
    omega

end ECDLP.L80
