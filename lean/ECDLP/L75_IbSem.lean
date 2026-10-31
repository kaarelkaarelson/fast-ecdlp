import ECDLP.L68_CarPEx

/-!
# L75 / IbSem: the `ib` gate of `edgeNetM` at the node level

* `ib_pa_iff`, `ib_child`: the parents of `ib c j1` are exactly the `mid c k`; its children are exactly the
  `car c j` with `j % A = j1`.
* `ib_nf`, `ib_nm`, `ib_w`: free count `1`, message count `2^M + 1`, message width `clog (2^M+1)`.
* `out_ib_q`: the code of the message sent to `car j` is the `ZMod.val` of `ibOut A ωi tInv Z (j / A)` with `Z i` the
  ring element received from `mid i` (read through `pm`, the digit of the setting code).
* `w_ib_q`: the weight is `1`.
-/
noncomputable section
namespace ECDLP.L75
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L57 ECDLP.L58 ECDLP.L64 ECDLP.L68

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] (φ : ∀ c, ιc c → ι)
  (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop)

theorem mid_mem_ib (c : Fin K) (j1 k : Fin N0.A) :
    CG.gt c (Gate.mid k) ∈ paC (w := w) φ (CG.gt c (Gate.ib j1)) :=
  mem_paC_gt φ c (Finset.mem_image.2 ⟨k, mem_univ _, rfl⟩)

theorem ib_pa_iff (c : Fin K) (j1 : Fin N0.A) (x : CG ι ιc N0.A) :
    x ∈ paC (w := w) φ (CG.gt c (Gate.ib j1)) ↔ ∃ k : Fin N0.A, x = CG.gt c (Gate.mid k) := by
  constructor
  · intro h
    rcases mem_pa_gt φ h with ⟨q, hq, rfl⟩ | h
    · obtain ⟨k, rfl⟩ := (mem_paG_ib (NP N0 w c) j1 q).1 hq
      exact ⟨k, rfl⟩
    · simp [extraPa] at h
  · rintro ⟨k, rfl⟩
    exact mid_mem_ib φ c j1 k

theorem ib_child (c : Fin K) (j1 : Fin N0.A) (b : CG ι ιc N0.A)
    (h : CG.gt c (Gate.ib j1) ∈ paC (w := w) φ b) :
    ∃ j : Fin (N0.A * N0.A), b = CG.gt c (Gate.car j) ∧ j.val % N0.A = j1.val := by
  obtain ⟨g', rfl, hg⟩ := child_gt φ h
  cases g' with
  | fa j s => exact absurd hg (not_mem_paG_fa _ _ _ _)
  | mid k => exact absurd ((mem_paG_mid (NP N0 w c) k _).1 hg) (by rintro ⟨p, hp⟩; cases hp)
  | ib j' => exact absurd ((mem_paG_ib (NP N0 w c) j' _).1 hg) (by rintro ⟨p, hp⟩; cases hp)
  | car j =>
    rcases (mem_paG_car (NP N0 w c) j _).1 hg with h1 | ⟨_, h2⟩
    · refine ⟨j, rfl, ?_⟩
      have := congrArg Fin.val (Gate.ib.inj h1)
      exact this.symm
    · cases h2

theorem ib_nf (m : ℕ) (c : Fin K) (j1 : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Free (CG.gt c (Gate.ib j1))) = 1 := by
  show Fintype.card Unit = 1
  simp

theorem ib_nm (m : ℕ) (c : Fin K) (j1 : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.ib j1))) = 2 ^ (NP N0 w c).M + 1 := by
  show Fintype.card (ZMod (2 ^ (NP N0 w c).M + 1)) = _
  exact ZMod.card _

theorem ib_w (m : ℕ) (c : Fin K) (j1 : Fin N0.A) :
    (edgeNetM (w := w) φ F ok m).w (CG.gt c (Gate.ib j1)) = Nat.clog 2 (2 ^ (NP N0 w c).M + 1) := by
  unfold PForced.w
  rw [ib_nm]

/-- the ring element received from `mid k`, as a natural number code -/
theorem pm_mid_cast (m : ℕ) (c : Fin K) (j1 k : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.ib j1))
    (z : (edgeNetM (w := w) φ F ok m).S q) :
    (((ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.mid k)) : ℕ)) : (NP N0 w c).Rg) =
      (show (NP N0 w c).Rg from (hq ▸ z : (edgeNetM (w := w) φ F ok m).S (CG.gt c (Gate.ib j1))).2
        ⟨CG.gt c (Gate.mid k), mid_mem_ib φ c j1 k⟩) := by
  subst hq
  have : NeZero (2 ^ (NP N0 w c).M + 1) := ⟨Nat.succ_ne_zero _⟩
  unfold ECDLP.L68.pm
  rw [dite_cond_eq_true (eq_true (mid_mem_ib φ c j1 k))]
  show (((ZMod.val (n := 2 ^ (NP N0 w c).M + 1) (z.2 ⟨CG.gt c (Gate.mid k), mid_mem_ib φ c j1 k⟩) : ℕ)) : ZMod (2 ^ (NP N0 w c).M + 1)) = _
  exact ZMod.natCast_zmod_val _

theorem pm_mid_lt (m : ℕ) (c : Fin K) (j1 k : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.ib j1))
    (z : (edgeNetM (w := w) φ F ok m).S q) :
    ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.mid k)) < 2 ^ (NP N0 w c).M + 1 := by
  subst hq
  have : NeZero (2 ^ (NP N0 w c).M + 1) := ⟨Nat.succ_ne_zero _⟩
  unfold ECDLP.L68.pm
  rw [dite_cond_eq_true (eq_true (mid_mem_ib φ c j1 k))]
  exact ZMod.val_lt (n := 2 ^ (NP N0 w c).M + 1) _

/-- the vector read by the `ib` gate, as a function on `ℕ` (zero-padded) of the codes of the digits -/
def ibZ (m : ℕ) (c : Fin K) (j1 : Fin N0.A) {q : CG ι ιc N0.A} (z : (edgeNetM (w := w) φ F ok m).S q) :
    ℕ → (NP N0 w c).Rg :=
  fun i => if h : i < N0.A then (((ECDLP.L68.pm (w := w) φ F ok m z (CG.gt c (Gate.mid ⟨i, h⟩)) : ℕ)) : (NP N0 w c).Rg) else 0

theorem out_ib_q (m : ℕ) (c : Fin K) (j1 : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.ib j1))
    (z : (edgeNetM (w := w) φ F ok m).S q) (c' : Fin K) (j : Fin (N0.A * N0.A)) :
    ec (ι := ι) (ιc := ιc) (w := w) q ((edgeNetM (w := w) φ F ok m).out q z (CG.gt c' (Gate.car j))) =
      (ibOut N0.A (NP N0 w c).ωi (NP N0 w c).tInv (ibZ (w := w) φ F ok m c j1 z) (j.val / N0.A)).val := by
  have hcast := fun k => pm_mid_cast (w := w) φ F ok m c j1 k q hq z
  subst hq
  show ((ECDLP.L68.zCode (2 ^ (NP N0 w c).M + 1)) (ibOut N0.A (NP N0 w c).ωi (NP N0 w c).tInv
      (NPar.exA (fun k : Fin N0.A => (show (NP N0 w c).Rg from
        z.2 ⟨CG.gt c (Gate.mid k), mid_mem_ib φ c j1 k⟩))) (j.val / N0.A)) : ℕ) = _
  rw [ECDLP.L68.zCode_val]
  congr 1
  refine NPar.ibOut_congr _ (fun r hr => ?_) _
  have hr' : r < N0.A := hr
  refine (NPar.exA_of_lt _ ⟨r, hr⟩).trans ?_
  unfold ibZ
  rw [dif_pos hr']
  exact (hcast ⟨r, hr⟩).symm

theorem w_ib_q (m : ℕ) (c : Fin K) (_j1 : Fin N0.A) (q : CG ι ιc N0.A) (hq : q = CG.gt c (Gate.ib _j1))
    (z : (edgeNetM (w := w) φ F ok m).S q) :
    (if (edgeNetM (w := w) φ F ok m).W q z = 1 then 1 else 0 : ℕ) = 1 := by
  subst hq
  show (if (Int.castRingHom (ZMod m)) (1 : ℤ) = 1 then 1 else 0 : ℕ) = 1
  simp

end
end ECDLP.L75
end
