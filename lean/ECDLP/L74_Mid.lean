import ECDLP.L74_Fa

/-!
# L74 / Mid: the MID gate of `edgeNetM` at the node level, and its `hout` / `hwt` obligations

`out_mid_q`: for a node `q = gt c (mid k)` the code of the message sent to a child `gt c' (ib j₁)` is the `ZMod.val`
of `midMsg (F c) k Y j₁`, where `Y i s` is the (ring) message of the parent `fa i s` (`ZMod.val` = `pm z (fa i s)`).
`mid_hout`: the local expression (`midE` with `Y` read from the setting code by `digE`) evaluates to that code.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L74
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem mid_child (c : Fin K) (k : Fin N0.A) {b : CG ι ιc N0.A}
    (h : CG.gt c (Gate.mid k) ∈ paC (w := w) φ b) : ∃ j₁, b = CG.gt c (Gate.ib j₁) := by
  cases b with
  | src i s' => simp [paC] at h
  | gt c' g' =>
    simp only [paC] at h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 h
      cases hqe
      cases g' with
      | fa _ _ => simp only [paG] at hq; exact absurd hq (Finset.notMem_empty _)
      | mid k' =>
        simp only [paG] at hq
        obtain ⟨_, _, h⟩ := Finset.mem_image.1 hq; cases h
      | ib j₁ => exact ⟨j₁, rfl⟩
      | car jj =>
        simp only [paG] at hq
        rcases Finset.mem_insert.1 hq with h | h
        · cases h
        · split_ifs at h with h0
          · exact absurd (Finset.mem_singleton.1 h) (by intro h; cases h)
          · exact absurd h (Finset.notMem_empty _)
    · cases g' <;> simp [extraPa] at h

theorem mid_fa_mem (c : Fin K) (k : Fin N0.A) (i : ιc c) (s : Fin N0.A) :
    CG.gt c (Gate.fa i s) ∈ paC (w := w) φ (CG.gt c (Gate.mid k)) :=
  mem_paC_gt φ c (Finset.mem_image.2 ⟨(i, s), Finset.mem_univ _, rfl⟩)

theorem out_mid_q (m : ℕ) (c : Fin K) (k : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.mid k))
    (z : (edgeNetM (w := w) φ F ok m).S q) (c' : Fin K) (j₁ : Fin N0.A) (ch : CG ι ιc N0.A)
    (hch : ch = CG.gt c' (Gate.ib j₁)) :
    ∃ Y : ιc c → ℕ → (NP N0 w c).Rg,
      (∀ (i : ιc c) (s : Fin N0.A), ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.fa i s)) = (Y i s).val) ∧
      ec (ι := ι) (ιc := ιc) (w := w) q ((edgeNetM (w := w) φ F ok m).out q z ch) =
        ((NP N0 w c).midMsg (F c) k Y j₁).val := by
  subst hq hch
  refine ⟨fun i => NPar.exA (fun s : Fin N0.A => (show (NP N0 w c).Rg from
    z.2 ⟨CG.gt c (Gate.fa i s), mid_fa_mem φ c k i s⟩)), ?_, rfl⟩
  intro i s
  unfold ECDLP.L68.pm
  rw [dif_pos (mid_fa_mem (w := w) φ c k i s)]
  show _ = ZMod.val (NPar.exA (fun s' : Fin N0.A => (show (NP N0 w c).Rg from
    z.2 ⟨CG.gt c (Gate.fa i s'), mid_fa_mem φ c k i s'⟩)) (s : ℕ))
  rw [NPar.exA_of_lt]
  rfl

end
end ECDLP.L74
end
