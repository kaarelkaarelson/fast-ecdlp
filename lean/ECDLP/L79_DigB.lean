import ECDLP.L79_Dig2
import ECDLP.L74_B0

/-!
# L79 / DigB: the power `Q^(idx - d0)` read by `digCmid` / `digCib` is bounded by the setting-count bound `V`
(it equals the product `pp (nA a) idx` of radices, which is at most `sN a`).
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  {V : ℕ}

theorem mid_Qpow_le (hsN : ∀ a : ℕ, ECDLP.L64.sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V)  {a kk : Fin (L.gTot N0.A)} {c : Fin K} {k : Fin N0.A} {i : ιc c} {s : Fin N0.A}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.mid k)) (hkk : (L.enum N0.A).symm kk = CG.gt c (Gate.fa i s)) :
    (2 ^ (NP N0 w c).M + 1) ^ (kk.val - (L.nι * N0.A + L.off N0.A c)) ≤ V := by
  haveI := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  have hmem : (L.enum N0.A).symm kk ∈ paC (w := w) φ (CG.gt c (Gate.mid k)) := by
    rw [hkk]; exact ECDLP.L74.mid_fa_mem (w := w) φ c k i s
  have hint := (mid_parents (w := w) (φ := φ) L c k kk).1 hmem
  have h1 := pp_nA_interval (P := edgeNetM (w := w) φ F ok m) (e := L.enum N0.A) a (d0 := L.nι * N0.A + L.off N0.A c)
    (n := L.nc c * N0.A) (Q := 2 ^ (NP N0 w c).M + 1) (mid_off_le L c k)
    (fun j => by rw [hka]; exact mid_parents (w := w) (φ := φ) L c k j)
    (fun j hj => by rw [hka] at hj; exact mid_radix (w := w) (φ := φ) (F := F) (ok := ok) L c k j hj)
    (kk.val - (L.nι * N0.A + L.off N0.A c)) (by omega)
  rw [show L.nι * N0.A + L.off N0.A c + (kk.val - (L.nι * N0.A + L.off N0.A c)) = kk.val by omega] at h1
  rw [← h1]
  refine le_trans (Factoring.Aux.pp_mono_le (fun i => ECDLP.L64.nA_pos _ _ _ i) (j := kk.val) (n := L.gTot N0.A) kk.2.le) ?_
  refine le_trans (ECDLP.L69.pp_le_sN _ _ a.1) ?_
  exact hsN a.1

theorem ib_Qpow_le (hsN : ∀ a : ℕ, ECDLP.L64.sN (edgeNetM (w := w) φ F ok m) (L.enum N0.A) a ≤ V)  {a kk : Fin (L.gTot N0.A)} {c : Fin K} {j1 : Fin N0.A} {k : Fin N0.A}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.ib j1)) (hkk : (L.enum N0.A).symm kk = CG.gt c (Gate.mid k)) :
    (2 ^ (NP N0 w c).M + 1) ^ (kk.val - (L.nι * N0.A + L.off N0.A c + L.nc c * N0.A)) ≤ V := by
  haveI := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  have hint : L.nι * N0.A + L.off N0.A c + L.nc c * N0.A ≤ kk.val ∧
      kk.val < L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A := by
    have := congrArg (fun q => (L.enum N0.A q : ℕ)) hkk
    simp only [Equiv.apply_symm_apply, Lay.enum_gt, Lay.gateE_mid] at this
    have := k.2
    omega
  have hlt : L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A ≤ L.gTot N0.A := by
    have := enum_lt_gTot L (CG.gt c (Gate.ib j1))
    rw [Lay.enum_gt, Lay.gateE_ib] at this
    have := j1.2
    omega
  have h1 := pp_nA_interval (P := edgeNetM (w := w) φ F ok m) (e := L.enum N0.A) a
    (d0 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A) (n := N0.A) (Q := 2 ^ (NP N0 w c).M + 1) hlt
    (fun j => by rw [hka]; exact ib_parents (w := w) (φ := φ) L c j1 j)
    (fun j hj => by rw [hka] at hj; exact ib_radix (w := w) (φ := φ) (F := F) (ok := ok) L c j1 j hj)
    (kk.val - (L.nι * N0.A + L.off N0.A c + L.nc c * N0.A)) (by omega)
  rw [show L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + (kk.val - (L.nι * N0.A + L.off N0.A c + L.nc c * N0.A)) = kk.val by omega] at h1
  rw [← h1]
  refine le_trans (Factoring.Aux.pp_mono_le (fun i => ECDLP.L64.nA_pos _ _ _ i) (j := kk.val) (n := L.gTot N0.A) kk.2.le) ?_
  refine le_trans (ECDLP.L69.pp_le_sN _ _ a.1) ?_
  exact hsN a.1

end
end ECDLP.L79
end
