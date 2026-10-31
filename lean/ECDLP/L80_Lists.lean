import ECDLP.L80_BW

/-!
# L80 / Lists: chains of `sizeC`, `addS`, `padCopy` calls, by induction on the list
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-! ### sums of scalars -/

def addList (z c : ℕ) : List ℕ → Cmd
  | [] => .skip
  | x :: xs => .seq (addS z x c) (addList z c xs)

theorem addList_run (z c : ℕ) (hzc : z ≠ c) : ∀ (xs : List ℕ) (st : St), (∀ x ∈ xs, x ≠ z ∧ x ≠ c) →
    let r := Cmd.run (addList z c xs) st
    r.1.sc z = st.sc z + (xs.map st.sc).sum ∧ r.1.ar = st.ar ∧ (∀ y, y ≠ z → y ≠ c → r.1.sc y = st.sc y) ∧
    r.2 ≤ 2 * (xs.map st.sc).sum + 2 * xs.length + 1 := by
  intro xs
  induction xs with
  | nil => intro st _; simp [addList, Cmd.run_skip]
  | cons x xs ih =>
    intro st hx
    have hx' := hx x (by simp)
    obtain ⟨a1, a2, a3, a4⟩ := addS_run z x c (Ne.symm hx'.1) hx'.2 hzc st
    obtain ⟨i1, i2, i3, i4⟩ := ih (Cmd.run (addS z x c) st).1 (fun y hy => hx y (by simp [hy]))
    have hmap : xs.map (Cmd.run (addS z x c) st).1.sc = xs.map st.sc :=
      List.map_congr_left (fun y hy => a3 y (hx y (by simp [hy])).1 (hx y (by simp [hy])).2)
    rw [hmap] at i1 i4
    simp only [addList, Cmd.run_seq, List.map_cons, List.sum_cons, List.length_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [i1, a1]; ring
    · rw [i2, a2]
    · intro y h1 h2; rw [i3 y h1 h2, a3 y h1 h2]
    · omega

/-! ### sizes -/

def sizeList : List (ℕ × ℕ) → Cmd
  | [] => .skip
  | (arr, z) :: l => .seq (sizeC arr z) (sizeList l)

theorem sizeList_run (W : ℕ) : ∀ (l : List (ℕ × ℕ)) (st : St), st.sc 710 = W →
    (∀ q ∈ l, q.2 ≠ 780 ∧ q.2 ≠ 781 ∧ q.2 ≠ 710) → (l.map (·.2)).Nodup →
    let r := Cmd.run (sizeList l) st
    (∀ q ∈ l, r.1.sc q.2 = Nat.size (V (st.ar q.1) W)) ∧ r.1.ar = st.ar ∧
    (∀ y, y ≠ 780 → y ≠ 781 → y ∉ l.map (·.2) → r.1.sc y = st.sc y) ∧ r.2 ≤ l.length * (7 * W + 5) + 1 := by
  intro l
  induction l with
  | nil => intro st _ _ _; simp [sizeList, Cmd.run_skip]
  | cons q l ih =>
    intro st hW hq hnd
    obtain ⟨arr, z⟩ := q
    have hz := hq (arr, z) (by simp)
    have hnd' : (z :: l.map (·.2)).Nodup := by simpa using hnd
    have hznot : z ∉ l.map (·.2) := (List.nodup_cons.1 hnd').1
    obtain ⟨a1, a2, a3, a4⟩ := sizeC_run arr z ⟨hz.1, hz.2.1⟩ st W hW hz.2.2
    obtain ⟨i1, i2, i3, i4⟩ := ih (Cmd.run (sizeC arr z) st).1
      (by rw [a3 710 (by norm_num) (by norm_num) (Ne.symm hz.2.2)]; exact hW)
      (fun q' hq' => hq q' (by simp [hq'])) (List.nodup_cons.1 hnd').2
    simp only [sizeList, Cmd.run_seq, List.length_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hl
      · dsimp only
        rw [i3 z hz.1 hz.2.1 hznot, a1]
      · rw [i1 q' hl, a2]
    · rw [i2, a2]
    · intro y h1 h2 h3
      simp only [List.map_cons, List.mem_cons, not_or] at h3
      rw [i3 y h1 h2 h3.2, a3 y h1 h2 h3.1]
    · nlinarith [a4, i4]

/-! ### zero-padded copies -/

def padList (wS : ℕ) : List (ℕ × ℕ × ℕ) → Cmd
  | [] => .skip
  | (d, s, n) :: l => .seq (padCopy d s n wS) (padList wS l)

theorem padList_run (wS : ℕ) (hwS : wS ≠ 818 ∧ wS ≠ 819) (w : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ)) (st : St), st.sc wS = w →
    (∀ q ∈ l, q.1 ≠ q.2.1 ∧ q.2.2 ≠ 818 ∧ q.2.2 ≠ 819) → (l.map (·.1)).Nodup →
    (∀ q ∈ l, ∀ q' ∈ l, q'.2.1 ≠ q.1) →
    let r := Cmd.run (padList wS l) st
    (∀ q ∈ l, ∀ i, 1 ≤ i → i ≤ st.sc q.2.2 → r.1.ar q.1 i = if i ≤ w then bt (st.ar q.2.1) i else 0) ∧
    (∀ a, a ∉ l.map (·.1) → r.1.ar a = st.ar a) ∧ ScKeep ZP2 st r.1 ∧
    r.2 ≤ (l.map (fun q => st.sc q.2.2 * 9 + 2)).sum + 1 := by
  intro l
  induction l with
  | nil => intro st _ _ _ _; simp [padList, Cmd.run_skip, ScKeep]
  | cons q l ih =>
    intro st hw hq hnd hsrc
    obtain ⟨d, s, n⟩ := q
    have hq0 := hq (d, s, n) (by simp)
    have hnd' : (d :: l.map (·.1)).Nodup := by simpa using hnd
    have hd_not : d ∉ l.map (·.1) := (List.nodup_cons.1 hnd').1
    obtain ⟨a1, a2, a3, a4, a5⟩ := padCopy_run d s n wS hq0.1 st (st.sc n) w rfl hw hwS
    have hn_keep : ∀ q' ∈ l, (Cmd.run (padCopy d s n wS) st).1.sc q'.2.2 = st.sc q'.2.2 := fun q' hq' =>
      a4 _ (by have := hq q' (by simp [hq']); unfold ZP2; omega)
    obtain ⟨i1, i2, i3, i4⟩ := ih (Cmd.run (padCopy d s n wS) st).1
      (by rw [a4 wS (by unfold ZP2; omega)]; exact hw) (fun q' hq' => hq q' (by simp [hq'])) (List.nodup_cons.1 hnd').2
      (fun q1 h1 q2 h2 => hsrc q1 (by simp [h1]) q2 (by simp [h2]))
    have hsrc_keep : ∀ q' ∈ l, (Cmd.run (padCopy d s n wS) st).1.ar q'.2.1 = st.ar q'.2.1 := fun q' hq' =>
      a3 _ (fun h => hsrc (d, s, n) (by simp) q' (by simp [hq']) h)
    simp only [padList, Cmd.run_seq, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q' hq' i h1 h2
      rcases List.mem_cons.1 hq' with rfl | hl
      · dsimp only at h2 ⊢
        rw [i2 _ hd_not, a2 i h1 h2]
      · have h2' : i ≤ (Cmd.run (padCopy d s n wS) st).1.sc q'.2.2 := by rw [hn_keep q' hl]; exact h2
        rw [i1 q' hl i h1 h2', hsrc_keep q' hl]
    · intro a ha
      simp only [List.map_cons, List.mem_cons, not_or] at ha
      rw [i2 a ha.2, a3 a ha.1]
    · intro y hy
      rw [i3 y hy, a4 y hy]
    · have hmap : l.map (fun q => (Cmd.run (padCopy d s n wS) st).1.sc q.2.2 * 9 + 2) = l.map (fun q => st.sc q.2.2 * 9 + 2) :=
        List.map_congr_left (fun q' hq' => by rw [hn_keep q' hq'])
      rw [hmap] at i4
      omega

end ECDLP.L80
