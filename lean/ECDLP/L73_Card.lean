import ECDLP.L73_Iface

/-!
# L73 / Card: the sizes of free values and messages of `edgeNetM`, and the message widths
-/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ECDLP.L73
open Finset Factoring.Aux ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58

section
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι]
  (φ : ∀ c, ιc c → ι) (F : ∀ c, Form (ιc c)) (ok : ι → Fin N0.A → Dg N0 → Prop) (m : ℕ)

theorem card_free_src (i : ι) (s : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Free (CG.src i s)) = (2 ^ N0.b) ^ N0.h := by
  show Fintype.card (Dg N0) = _
  simp [Dg]

theorem card_free_gt (c : Fin K) (g : Gate (ιc c) N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Free (CG.gt c g)) = 1 := by
  show Fintype.card Unit = 1
  simp

theorem card_msg_src (i : ι) (s : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.src i s)) = (2 ^ N0.b) ^ N0.h := by
  show Fintype.card (Dg N0) = _
  simp [Dg]

theorem card_msg_fa (c : Fin K) (j : ιc c) (s : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.fa j s))) = 2 ^ (NP N0 w c).M + 1 := by
  show Fintype.card (NP N0 w c).Rg = _
  exact ZMod.card _
theorem card_msg_mid (c : Fin K) (k : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.mid k))) = 2 ^ (NP N0 w c).M + 1 := by
  show Fintype.card (NP N0 w c).Rg = _
  exact ZMod.card _
theorem card_msg_ib (c : Fin K) (k : Fin N0.A) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.ib k))) = 2 ^ (NP N0 w c).M + 1 := by
  show Fintype.card (NP N0 w c).Rg = _
  exact ZMod.card _
theorem card_msg_car (c : Fin K) (j : Fin (N0.A * N0.A)) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg (CG.gt c (Gate.car j))) = 2 ^ ((NP N0 w c).M + 3) := by
  show Fintype.card (Fin (2 ^ ((NP N0 w c).M + 3))) = _
  simp

theorem clog_ring (M : ℕ) : Nat.clog 2 (2 ^ M + 1) = M + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]
    have := Nat.one_le_two_pow (n := M)
    omega
  · by_contra h
    have h' : Nat.clog 2 (2 ^ M + 1) ≤ M := by omega
    rw [Nat.clog_le_iff_le_pow (by norm_num)] at h'
    omega

theorem clog_car (M : ℕ) : Nat.clog 2 (2 ^ (M + 3)) = M + 3 := Nat.clog_pow 2 (M + 3) (by norm_num)

theorem clog_src (b h : ℕ) : Nat.clog 2 ((2 ^ b) ^ h) = b * h := by
  rw [← pow_mul]; exact Nat.clog_pow 2 (b * h) (by norm_num)

end
end ECDLP.L73
end
