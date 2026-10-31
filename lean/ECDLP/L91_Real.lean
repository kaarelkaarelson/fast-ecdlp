import ECDLP.L91_Final

/-!
# L91 / Real: `ExSyn 200` for the REAL ECDLP network (L83's instance data, L79's repaired kinds, L81's source weight), `u = 16`
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 3200000
noncomputable section
namespace ECDLP.L91
open Finset Factoring.Aux Ex ECDLP.L81 ECDLP.L44 ECDLP.L59 ECDLP.L63 ECDLP.L76 ECDLP.L73 ECDLP.L54 ECDLP.L34 ECDLP.L68 ECDLP.L56 ECDLP.L64
  ECDLP.L83 Slot Cst

section
variable {n : ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop} {A : ℕ → ℕ → ℕ} {p a b X xR yR : ℕ} {π : List Bool} {ℓ bW : ℕ}
  (hB : 0 < B) (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (hu : B ≤ 16)

theorem instSy_real : InstSy (instEx (n := n) 16 hB hR) :=
  ⟨Sy_lit _, Sy_lit _, Sy_AEx, Sy_hEx, Sy_pbEx, Sy_bEx, Sy_ncEx n, Sy_MEx⟩

/-- the three kind expressions of `kindsC` for the real oracles are `Sy` and of depth `<= 100` -/
theorem kinds_real_sy (n : ℕ) :
    Sy (ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39)))) ∧
    Sy (ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx n 31 59 16) (lEx n 31 59) (rEx n 31 59))) ∧
    Sy (ECDLP.L79.ibOutIC (u := 16)) :=
  ⟨Sy_guardE (Sy_faKindEC (Sy_phiWrap (Sy_phiEx n))),
   Sy_guardE (Sy_midKindEC (Sy_nEx n) (Sy_epsEx n) (Sy_lEx n) (Sy_rEx n)), Sy_ibOutIC⟩

theorem kinds_real_dp (n : ℕ) :
    Ex.dp (ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39)))) ≤ 100 ∧
    Ex.dp (ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx n 31 59 16) (lEx n 31 59) (rEx n 31 59))) ≤ 100 ∧
    Ex.dp (ECDLP.L79.ibOutIC (u := 16)) ≤ 100 := by
  have h1 := ECDLP.L79.dp_faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39))
  have h2 := ECDLP.L79.dp_midKindEC_le (u := 16) (d := 75) (by norm_num) (nEx n 31) (epsEx n 31 59 16) (lEx n 31 59) (rEx n 31 59)
    (by rw [dp_nEx]; norm_num) (by rw [dp_epsEx]; norm_num) (by rw [dp_lEx]; norm_num) (by rw [dp_rEx]; norm_num)
  have h3 := ECDLP.L79.dp_ibOutIC (u := 16)
  have hp : Ex.dp (ECDLP.L79.phiWrap 16 (phiEx n 38 39)) = 23 := by
    simp only [ECDLP.L79.phiWrap, Ex.dp, dp_phiEx]; norm_num
  rw [hp] at h1
  refine ⟨by omega, by omega, by omega⟩


variable {m : ℕ} (hm1 : 1 < m) (ok : Slot n → Fin (NParE (Nat.size p)).A → Dg (NParE (Nat.size p)) → Prop)

/-- **`ExSyn 200` for the REAL network** (`u = 16`): the five `E` fields of `edge_nrep` with the real instance data (`instEx`, `phiExInst`),
any kinds whose three expressions are L79's `kindsC` expressions with the real oracles (`hfa hmid hib`, true by `rfl` for `kindsReal`),
any source weight whose expression is L81's `srcE 16 (badE 16 n)` (`hSw`, true for `srcWtSlot`), and `gE = gEx I`.
Only `btE` is a hypothesis (`hb`, `hdb`: binders >= 10, variables < 990, reads only as `0 < rd`, depth <= 40). -/
theorem exSyn200_real
    (Kd : Kinds (w := fun _ => wP (Nat.size p)) (m := m)
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu))
    (hfa : Kd.fa.outE = ECDLP.L79.guardE 16 (ECDLP.L79.faKindEC (u := 16) (ECDLP.L79.phiWrap 16 (phiEx n 38 39))))
    (hmid : Kd.mid.outE = ECDLP.L79.guardE 16 (ECDLP.L79.midKindEC (u := 16) (nEx n 31) (epsEx n 31 59 16) (lEx n 31 59) (rEx n 31 59)))
    (hib : Kd.ib.outE = ECDLP.L79.ibOutIC (u := 16))
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu))
    (hSw : Sw.srcE = srcE 16 (badE 16 n))
    (btE : Ex) (hb : Sy btE) (hdb : Ex.dp btE ≤ 40) :
    haveI := edge_free_nonempty (w := fun _ => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m
    let P := pexEdge (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu hm1 Kd Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE btE := by
  obtain ⟨k1, k2, k3⟩ := kinds_real_sy n
  obtain ⟨q1, q2, q3⟩ := kinds_real_dp n
  have hphi : Sy (phiExInst (n := n) (A := A) (Ctx := Ctx) (p := p) (a := a) (b := b) (X := X) (xR := xR) (yR := yR) (π := π) (ℓ := ℓ) (bW := bW) 16 hB hR).phiE := Sy_phiEx n
  refine exSyn200_edge (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu (instSy_real hB hR) hphi hm1 Kd Sw
    (hfa ▸ k1) (hmid ▸ k2) (hib ▸ k3) (hSw ▸ Sy_srcE n) (dI := 21) (dphi := 21) (by norm_num) (by norm_num)
    (dp_AEx 16 ▸ (by norm_num)) (dp_hEx 16 ▸ (by norm_num)) (dp_pbEx 16 ▸ (by norm_num)) (by simp [instEx, Ex.dp])
    (by simp [instEx, Ex.dp]) (by show Ex.dp (ncEx n 16) ≤ 21; rw [dp_ncEx]) (by show Ex.dp (MEx 16) ≤ 21; rw [dp_MEx]; norm_num)
    (dp_bEx 16 ▸ (by norm_num)) (by show Ex.dp (phiEx n (16 + 22) (16 + 23)) ≤ 21; rw [dp_phiEx]) (by rw [hSw]; exact dp_srcE n)
    (hfa ▸ q1) (hmid ▸ q2) (hib ▸ q3) btE hb hdb


/-- the same for L83's `kindsReal` (with its `hne`) -/
theorem exSyn200_kindsReal
    (hne : ∀ c : Fin (18 * n + 12), 0 < (layOf (sgR n ℓ π)).nc c)
    (Sw : SrcWt (w := fun _ => wP (Nat.size p))
      (pex0 (F := frF (sgR n ℓ π) (cnEquiv n)) (ok := ok) (m := m) (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu))
    (hSw : Sw.srcE = srcE 16 (badE 16 n))
    (btE : Ex) (hb : Sy btE) (hdb : Ex.dp btE ≤ 40) :
    haveI := edge_free_nonempty (w := fun _ => wP (Nat.size p)) (phiR n ℓ π) (frF (sgR n ℓ π) (cnEquiv n)) ok m
    let P := pexEdge (instEx (n := n) 16 hB hR) (phiExInst 16 hB hR) hu hm1 (kindsReal hB hR hu m ok hne) Sw
    ECDLP.L85B.ExSyn 200 ⟨szEx P, WEx P, cEx P, msgTest (mMsg P 16 (16 + 1)) (cEx P) (16 + 3) (16 + 9),
      msgTest (mMsg P (16 + 1) 16) (cEx P) (16 + 3) (16 + 9)⟩ P.gE btE :=
  exSyn200_real hB hR hu hm1 ok (kindsReal hB hR hu m ok hne) rfl rfl rfl Sw hSw btE hb hdb

end

section
open ECDLP.L51 ECDLP.L35 ECDLP.L38 ECDLP.L56 ECDLP.L58
variable {K : ℕ} {ιc : Fin K → Type} {N0 : NPar} {w : Fin K → ℕ} {B : ℕ} {Ctx : (ℕ → ℕ) → Prop}
  {A : ℕ → ℕ → ℕ} [∀ c, Fintype (ιc c)] [∀ c, DecidableEq (ιc c)]
  {n : ℕ} {L : Lay (Slot n) ιc} {φ : ∀ c, ιc c → Slot n} {F : ∀ c, Form (ιc c)} {m : ℕ}

/-- L81's `srcWtSlot` has the source expression `srcE u (badE u n)` (so `hSw` holds for it) -/
theorem srcWtSlot_srcE {p a b X xR yR mm : ℕ} {π : List Bool} {ℓ bW : ℕ} (hm1 : 1 < m) (hB : 0 < B) (hu : B ≤ 16)
    (hb0 : 0 < N0.b) (hbW : bW = N0.b * 2 ^ N0.k) (hI : SlotIdx n (fun i => (L.eι i : ℕ)))
    (hR : ∀ σ₀, Ctx σ₀ → ECDLP.L72.Reads72 σ₀ A p a b X xR yR π ℓ bW) (hX : X = Bd p mm) (hodd : p % 2 = 1)
    (Xp : PEx0 (B := B) (Ctx := Ctx) (A := A)
      (edgeNetM (w := w) φ F (okC N0 (Cl (instOf p a b xR yR mm) (N0.b * 2 ^ N0.k)
        (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i))) m) (L.enum N0.A) 16) :
    (srcWtSlot (L := L) (φ := φ) (F := F) hm1 hB hu hb0 hbW hI hR hX hodd Xp).srcE = srcE 16 (badE 16 n) := rfl

end
end ECDLP.L91
end
