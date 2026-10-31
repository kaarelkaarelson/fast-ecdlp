import ECDLP.L79_Dig

/-!
# L79 / Dig2: the shallow digit expressions `digCfa`, `digCmid`, `digCib` of the edge network, equal to `digE` where the kinds use it

fa:  `z % (2^b)^h`                                   (one parent `src (phi c j) s`, radix `(2^b)^h`)
mid: `(z / (2^M+1)^(idx - dbase)) % (2^M+1)`        (parents `fa(i,s)` = `[dbase, dbase + nc A)`, radix `2^M+1`)
ib:  `(z / (2^M+1)^(idx - dbase - nc A)) % (2^M+1)` (parents `mid k` = `[dbase + nc A, + A)`)
Slots as in L73's decode: `u+2` = code `z`, `u+1` = index of the parent read, `u+10 = 2^b`, `u+11 = 2^M`, `u+13 = h`, `u+18 = dbase`, `u+19 = nc`, `u+12 = A`.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L79
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73

def digCfa (u : ℕ) : Ex := .mod (.var (u + 2)) (nprod (u + 8) (.var (u + 13)) (.var (u + 10)))
def digCmid (u : ℕ) : Ex :=
  .mod (.div (.var (u + 2)) (nprod (u + 8) (.sub (.var (u + 1)) (.var (u + 18))) (.add (.var (u + 11)) (.lit 1))))
    (.add (.var (u + 11)) (.lit 1))
def digCib (u : ℕ) : Ex :=
  .mod (.div (.var (u + 2)) (nprod (u + 8) (.sub (.var (u + 1)) (.add (.var (u + 18)) (.mul (.var (u + 19)) (.var (u + 12)))))
    (.add (.var (u + 11)) (.lit 1)))) (.add (.var (u + 11)) (.lit 1))

theorem dp_digCfa (u : ℕ) : Ex.dp (digCfa u) = 3 := by simp [digCfa, nprod, Ex.dp]
theorem dp_digCmid (u : ℕ) : Ex.dp (digCmid u) = 5 := by simp [digCmid, nprod, Ex.dp]
theorem dp_digCib (u : ℕ) : Ex.dp (digCib u) = 7 := by simp [digCib, nprod, Ex.dp]

section
variable {m B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {ι : Type} {K : ℕ} {ιc : Fin K → Type}
  {N0 : NPar} {w : Fin K → ℕ}
  [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)] [Fintype ι] [DecidableEq ι] {φ : ∀ c, ιc c → ι}
  {F : ∀ c, Form (ιc c)} {ok : ι → Fin N0.A → Dg N0 → Prop} {u : ℕ}
  (L : Lay ι ιc)
  (X : PEx0 (B := B) (Ctx := Ctx) (A := A) (edgeNetM (w := w) φ F ok m) (L.enum N0.A) u)

theorem enum_lt_gTot (q : CG ι ιc N0.A) : (L.enum N0.A q : ℕ) < L.gTot N0.A := (L.enum N0.A q).2

/-- parents of a mid node: the interval `[dbase, dbase + nc A)` of fa gates, all of radix `2^M+1` -/
theorem mid_parents (c : Fin K) (k : Fin N0.A) (j : Fin (L.gTot N0.A)) :
    (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.mid k)) ↔
      (L.nι * N0.A + L.off N0.A c ≤ j.val ∧ j.val < L.nι * N0.A + L.off N0.A c + L.nc c * N0.A) := by
  rw [pa_iff (L := L) (w := w) φ]
  simp [PA]

theorem mid_radix (c : Fin K) (k : Fin N0.A) (j : Fin (L.gTot N0.A))
    (h : (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.mid k))) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg ((L.enum N0.A).symm j)) = 2 ^ (NP N0 w c).M + 1 := by
  rcases (mem_paC_iff (w := w) φ c (Gate.mid k) _).1 h with ⟨q, hq, hh⟩ | h'
  · obtain ⟨i, s, rfl⟩ := (paG_mid (w := w) c k q).1 hq
    rw [hh]; exact card_msg_fa φ F ok m c i s
  · exact absurd ((extra_mid φ c k _).1 h') id

theorem ib_parents (c : Fin K) (k : Fin N0.A) (j : Fin (L.gTot N0.A)) :
    (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.ib k)) ↔
      (L.nι * N0.A + L.off N0.A c + L.nc c * N0.A ≤ j.val ∧ j.val < L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A) := by
  rw [pa_iff (L := L) (w := w) φ]
  simp [PA]

theorem ib_radix (c : Fin K) (k : Fin N0.A) (j : Fin (L.gTot N0.A))
    (h : (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.ib k))) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg ((L.enum N0.A).symm j)) = 2 ^ (NP N0 w c).M + 1 := by
  rcases (mem_paC_iff (w := w) φ c (Gate.ib k) _).1 h with ⟨q, hq, hh⟩ | h'
  · obtain ⟨k', rfl⟩ := (paG_ib (w := w) c k q).1 hq
    rw [hh]; exact card_msg_mid φ F ok m c k'
  · exact absurd ((extra_ib φ c k _).1 h') id

theorem fa_parents (c : Fin K) (i : ιc c) (s : Fin N0.A) (j : Fin (L.gTot N0.A)) :
    (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.fa i s)) ↔
      (L.eι (φ c i) * N0.A + s ≤ j.val ∧ j.val < L.eι (φ c i) * N0.A + s + 1) := by
  rw [pa_iff (L := L) (w := w) φ]
  simp [PA]
  omega

theorem fa_radix (c : Fin K) (i : ιc c) (s : Fin N0.A) (j : Fin (L.gTot N0.A))
    (h : (L.enum N0.A).symm j ∈ paC (w := w) φ (CG.gt c (Gate.fa i s))) :
    Fintype.card ((edgeNetM (w := w) φ F ok m).Msg ((L.enum N0.A).symm j)) = (2 ^ N0.b) ^ N0.h := by
  rcases (mem_paC_iff (w := w) φ c (Gate.fa i s) _).1 h with ⟨q, hq, hh⟩ | h'
  · exact absurd ((paG_fa (w := w) c i s q).1 hq) id
  · rw [(extra_fa φ c i s _).1 h']
    exact card_msg_src φ F ok m (φ c i) s

theorem mid_off_le (c : Fin K) (k : Fin N0.A) :
    L.nι * N0.A + L.off N0.A c + L.nc c * N0.A ≤ L.gTot N0.A := by
  have := enum_lt_gTot L (CG.gt c (Gate.mid k))
  rw [Lay.enum_gt, Lay.gateE_mid] at this
  omega

variable {V : ℕ} {σ₀ : ℕ → ℕ} {σ : ℕ → ℕ} (hu : B ≤ u) (hC : Ctx σ₀) (hσ : Ag B σ₀ σ)
include hu hC hσ

/-- **`digCmid` is `digE`** at the states where the mid kind evaluates `digE` (node `a = mid k`, parent `fa (i, s)` at `kk`) -/
theorem digCmid_eq_digE {a kk : Fin (L.gTot N0.A)} {c : Fin K} {k : Fin N0.A} {i : ιc c} {s : Fin N0.A}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.mid k)) (hkk : (L.enum N0.A).symm kk = CG.gt c (Gate.fa i s))
    (ha : σ u = a) (hk1 : σ (u + 1) = kk) (h11 : σ (u + 11) = 2 ^ (NP N0 w c).M)
    (h18 : σ (u + 18) = L.nι * N0.A + L.off N0.A c) :
    Ex.eval σ A (digCmid u) = Ex.eval σ A (digE X u (u + 1)) := by
  haveI := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  have hmem : (L.enum N0.A).symm kk ∈ paC (w := w) φ (CG.gt c (Gate.mid k)) := by
    rw [hkk]; exact ECDLP.L74.mid_fa_mem (w := w) φ c k i s
  have hint := (mid_parents (w := w) (φ := φ) L c k kk).1 hmem
  have hd := eval_digE_interval X hu hC hσ (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := kk) ha hk1
    (d0 := L.nι * N0.A + L.off N0.A c) (n := L.nc c * N0.A) (Q := 2 ^ (NP N0 w c).M + 1)
    (mid_off_le L c k) (by rw [hka]; exact card_free_gt φ F ok m c _)
    (fun j => by rw [hka]; exact mid_parents (w := w) (φ := φ) L c k j)
    (fun j hj => by rw [hka] at hj; exact mid_radix (w := w) (φ := φ) (F := F) (ok := ok) L c k j hj) hint.1 hint.2
  rw [hd]
  simp only [digCmid, Ex.eval]
  rw [eval_nprod_const (c := 2 ^ (NP N0 w c).M + 1) (fun j => by
    simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11])]
  simp only [Ex.eval, hk1, h18, h11]

theorem digCfa_eq_digE {a kk : Fin (L.gTot N0.A)} {c : Fin K} {i : ιc c} {s : Fin N0.A}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.fa i s)) (hkk : (L.enum N0.A).symm kk = CG.src (φ c i) s)
    (ha : σ u = a) (hk1 : σ (u + 1) = kk) (h10 : σ (u + 10) = 2 ^ N0.b) (h13 : σ (u + 13) = N0.h) :
    Ex.eval σ A (digCfa u) = Ex.eval σ A (digE X u (u + 1)) := by
  haveI := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  have hmem : (L.enum N0.A).symm kk ∈ paC (w := w) φ (CG.gt c (Gate.fa i s)) := by
    rw [hkk]; exact ECDLP.L74.fa_src_mem (w := w) φ c i s
  have hint := (fa_parents (w := w) (φ := φ) L c i s kk).1 hmem
  have hlt : L.eι (φ c i) * N0.A + s + 1 ≤ L.gTot N0.A := by
    have := enum_lt_gTot L (CG.src (φ c i) s)
    rw [Lay.enum_src] at this
    omega
  have hd := eval_digE_interval X hu hC hσ (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := kk) ha hk1
    (d0 := L.eι (φ c i) * N0.A + s) (n := 1) (Q := (2 ^ N0.b) ^ N0.h)
    hlt (by rw [hka]; exact card_free_gt φ F ok m c _)
    (fun j => by rw [hka]; exact fa_parents (w := w) (φ := φ) L c i s j)
    (fun j hj => by rw [hka] at hj; exact fa_radix (w := w) (φ := φ) (F := F) (ok := ok) L c i s j hj) hint.1 hint.2
  rw [hd]
  have : kk.val - (L.eι (φ c i) * N0.A + s) = 0 := by omega
  rw [this]
  simp only [digCfa, Ex.eval, pow_zero, Nat.div_one]
  rw [eval_pw (by omega)]
  simp only [Ex.eval, h10, h13]

theorem digCib_eq_digE {a kk : Fin (L.gTot N0.A)} {c : Fin K} {j1 k : Fin N0.A}
    (hka : (L.enum N0.A).symm a = CG.gt c (Gate.ib j1)) (hkk : (L.enum N0.A).symm kk = CG.gt c (Gate.mid k))
    (ha : σ u = a) (hk1 : σ (u + 1) = kk) (h11 : σ (u + 11) = 2 ^ (NP N0 w c).M)
    (h18 : σ (u + 18) = L.nι * N0.A + L.off N0.A c) (h19 : σ (u + 19) = L.nc c) (h12 : σ (u + 12) = N0.A) :
    Ex.eval σ A (digCib u) = Ex.eval σ A (digE X u (u + 1)) := by
  haveI := ECDLP.L64.edge_free_nonempty (w := w) φ F ok m
  have hmem : (L.enum N0.A).symm kk ∈ paC (w := w) φ (CG.gt c (Gate.ib j1)) := by
    exact (ib_parents (w := w) (φ := φ) L c j1 kk).2 (by
      have := congrArg (fun q => (L.enum N0.A q : ℕ)) hkk
      simp only [Equiv.apply_symm_apply, Lay.enum_gt, Lay.gateE_mid] at this
      omega)
  have hint := (ib_parents (w := w) (φ := φ) L c j1 kk).1 hmem
  have hlt : L.nι * N0.A + L.off N0.A c + L.nc c * N0.A + N0.A ≤ L.gTot N0.A := by
    have := enum_lt_gTot L (CG.gt c (Gate.ib j1))
    rw [Lay.enum_gt, Lay.gateE_ib] at this
    have := j1.2
    omega
  have hd := eval_digE_interval X hu hC hσ (fr := u) (tt := u + 1) (by omega) (by omega) (a := a) (k := kk) ha hk1
    (d0 := L.nι * N0.A + L.off N0.A c + L.nc c * N0.A) (n := N0.A) (Q := 2 ^ (NP N0 w c).M + 1)
    hlt (by rw [hka]; exact card_free_gt φ F ok m c _)
    (fun j => by rw [hka]; exact ib_parents (w := w) (φ := φ) L c j1 j)
    (fun j hj => by rw [hka] at hj; exact ib_radix (w := w) (φ := φ) (F := F) (ok := ok) L c j1 j hj) hint.1 hint.2
  rw [hd]
  simp only [digCib, Ex.eval]
  rw [eval_nprod_const (c := 2 ^ (NP N0 w c).M + 1) (fun j => by
    simp only [Ex.eval]; rw [Function.update_of_ne (by omega), h11])]
  simp only [Ex.eval, hk1, h18, h19, h12, h11]


end
end ECDLP.L79
end
