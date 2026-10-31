import ECDLP.L102_Eng

/-!
# L102 / Val: the value of `eng1` on a state that reads `(p, x, y, τ)`
-/
namespace ECDLP.L102
open ECDLP Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib ECDLP.L71

theorem eng1_val (s : St) (p x y : ℕ) (τ : List Bool)
    (hp : numCells (s.ar 0) 1 (s.sc 0) = p) (hx : numCells (s.ar 4) 1 (s.sc 0) = x)
    (hy : numCells (s.ar 5) 1 (s.sc 0) = y) (hn : numCells (s.ar 9) 1 (s.sc 0) = τ.length)
    (hpi : ∀ q (h : q < τ.length), (s.ar 6 (q + 1) ≠ 0 ↔ τ[q] = true))
    (hp2 : 2 ≤ p) (hyp : y < p) (hlen : Nat.size p + 1 ≤ s.sc 0) (hτ : τ.length ≤ Nat.size p + 1) :
    (Cmd.run eng1 s).1.sc 3 = if τ <+: bitsR p x y then 0 else 1 := by
  obtain ⟨hc, -⟩ := run_eng1 s
  rw [hc, outC_sc3]
  obtain ⟨a1, b1, c1⟩ := S1_facts s
  obtain ⟨a2, b2, c2, d2⟩ := S2_facts s
  obtain ⟨a3, b3, c3, d3, e3⟩ := S3_facts s
  obtain ⟨a4, b4, c4, d4, e4, f4⟩ := S4_facts s
  set ℓ := s.sc 0 with hℓ
  have hW : (S1 s).sc 10 = Nat.size p := by rw [a1, hp]
  have hNN : (S2 s).sc 14 = τ.length := by
    rw [a2, numCells_trunc (s.ar 9) 1 ℓ (by rw [hn]; omega), hn]
  have hBs : Bs (s.ar 5) ℓ = 2 * y := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have h1 : 2 ^ Nat.size p ≤ 2 ^ (ℓ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : p < 2 ^ Nat.size p := Nat.lt_size_self p
    have h3 := numCells_trunc1 (s.ar 5) 1 ℓ (by omega) (by rw [hy]; omega)
    rw [hy] at h3
    rw [hk, Bs_eq, ← hk] at *
    rw [hk] at h3
    simp only [Nat.add_sub_cancel] at h3
    rw [h3]
  have hRES : (S3 s).sc 18 = if p ≤ 2 * y then 1 else 0 := by
    rw [a3, hp, hBs]
  have hRES2 : (S3 s).sc 18 = 0 ∨ (S3 s).sc 18 = 1 := by rw [hRES]; split_ifs <;> simp
  have hs21 : (S4 s).sc 21 = 1 := by rw [a4, hW, hNN]; rw [if_neg]; omega
  have hs17 : (S4 s).sc 17 = τ.length := by rw [c4, hW, hNN, if_neg (by omega)]
  have key := stage5_val (S4 s) (eF p x y) (Nat.size p) ((S3 s).sc 18) (by rw [d4, hW]) e4 (by rw [b4, hW]) hs21 hRES2
    (fun q hq => by
      have hq' : q < Nat.size p := hq
      unfold eF
      rw [if_pos hq', f4, ← hx, testBit_numCells (s.ar 4) ℓ 1 _ (by omega)]
      rw [show 1 + (Nat.size p - 1 - q) = Nat.size p - q by omega])
    (fun q hq => by
      unfold eF
      rw [if_neg (by omega), hRES, decide_eq_true_eq, p_le_iff p y hp2]
      by_cases h : p ≤ 2 * y <;> simp [h])
  have e5 : (S5 s).sc 21 = (Cmd.run stage5 (S4 s)).1.sc 21 := by rw [S5]
  rw [e5, key, hs17, f4]
  have hiff : (∀ q, q < τ.length → (s.ar 6 (q + 1) ≠ 0 ↔ eF p x y q = true)) ↔ (τ <+: bitsR p x y) := by
    rw [prefix_bitsR]
    constructor
    · intro H
      refine ⟨hτ, fun q h => ?_⟩
      have h1 := H q h
      exact Bool.eq_iff_iff.mpr (by rw [← hpi q h]; exact h1)
    · rintro ⟨-, H⟩ q hq
      rw [hpi q hq, H q hq]
  by_cases hpf : τ <+: bitsR p x y
  · rw [if_pos (hiff.mpr hpf), if_pos hpf]; simp
  · have : ¬ ∀ q, q < τ.length → (s.ar 6 (q + 1) ≠ 0 ↔ eF p x y q = true) := fun H => hpf (hiff.mp H)
    rw [if_neg this, if_neg hpf]; simp

end ECDLP.L102
