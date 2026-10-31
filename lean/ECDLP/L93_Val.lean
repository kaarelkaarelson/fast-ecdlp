import FactoringAux.EngineNet
import FactoringAux.EngineCoarsenEx

/-!
# L93 / Val: the value of a coded network is determined by its expression representation (`NRep`)

If two coded networks `(N, κ)`, `(N', κ')` over `ZMod m` on the same node set `Fin g` are both represented (`NRep`, same
expressions, same context, same memory) then they have the same value.  So the value of the network `C.D` of an `EdgeCore`
is the value of ANY network represented by the same expressions (e.g. the real edge network of `edge_nrep`).
-/
noncomputable section
namespace ECDLP.L93
open Finset Factoring.Aux

/-- the assignment with the four argument variables set -/
def mk (σ₀ : ℕ → ℕ) (v : NVars) (a b z q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update σ₀ v.a a) v.b b) v.z z) v.q q

/-- distinct argument variables above the context bound -/
structure VOk (B : ℕ) (v : NVars) : Prop where
  ha : B ≤ v.a
  hb : B ≤ v.b
  hz : B ≤ v.z
  hq : B ≤ v.q
  ab : v.a ≠ v.b
  az : v.a ≠ v.z
  aq : v.a ≠ v.q
  bz : v.b ≠ v.z
  bq : v.b ≠ v.q
  zq : v.z ≠ v.q

theorem VOk.std {B u : ℕ} (h : B ≤ u) : VOk B (NVars.std u) :=
  ⟨h, by simp [NVars.std]; omega, by simp [NVars.std]; omega, by simp [NVars.std]; omega,
    by simp [NVars.std], by simp [NVars.std], by simp [NVars.std], by simp [NVars.std], by simp [NVars.std],
    by simp [NVars.std]⟩

theorem mk_ag {B : ℕ} {v : NVars} (hv : VOk B v) (σ₀ : ℕ → ℕ) (a b z q : ℕ) : Ag B σ₀ (mk σ₀ v a b z q) :=
  (((((Ag.refl B σ₀).upd hv.ha a).upd hv.hb b).upd hv.hz z).upd hv.hq q)

theorem mk_a {B : ℕ} {v : NVars} (hv : VOk B v) (σ₀ : ℕ → ℕ) (a b z q : ℕ) : mk σ₀ v a b z q v.a = a := by
  simp [mk, Function.update_apply, hv.ab, hv.az, hv.aq]
theorem mk_b {B : ℕ} {v : NVars} (hv : VOk B v) (σ₀ : ℕ → ℕ) (a b z q : ℕ) : mk σ₀ v a b z q v.b = b := by
  simp [mk, Function.update_apply, hv.bz, hv.bq]
theorem mk_z {B : ℕ} {v : NVars} (hv : VOk B v) (σ₀ : ℕ → ℕ) (a b z q : ℕ) : mk σ₀ v a b z q v.z = z := by
  simp [mk, Function.update_apply, hv.zq]
theorem mk_q {B : ℕ} {v : NVars} (hv : VOk B v) (σ₀ : ℕ → ℕ) (a b z q : ℕ) : mk σ₀ v a b z q v.q = q := by
  simp [mk]

theorem fac_eval_eq {R : Type*} [CommSemiring R] {X Y X' Y' : Type*} {c c' : ℕ} (hc : c = c')
    (F : Fac R X Y c) (F' : Fac R X' Y' c') (x : X) (y : Y) (x' : X') (y' : Y')
    (hl : ∀ q, F.l x (bdec c q) = F'.l x' (bdec c' q)) (hr : ∀ q, F.r y (bdec c q) = F'.r y' (bdec c' q)) :
    F.eval x y = F'.eval x' y' := by
  subst hc
  unfold Fac.eval
  refine Finset.sum_congr rfl fun θ _ => ?_
  have h1 := hl (bnum θ)
  have h2 := hr (bnum θ)
  rw [bdec_bnum] at h1 h2
  rw [h1, h2]

/-- **The value of a coded network is determined by its representing expressions.** -/
theorem value_eq_of_nrep {m vm B : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    {N N' : Net (ZMod m) g} {κ : Coding N} {κ' : Coding N'} (hv : VOk B v)
    (h : NRep m vm B σ₀ A v E N κ) (h' : NRep m vm B σ₀ A v E N' κ') : N.value = N'.value := by
  have hs : ∀ a : Fin g, κ.s a = κ'.s a := fun a => by
    rw [← h.sz _ (mk_ag hv σ₀ a 0 0 0) a (mk_a hv ..), ← h'.sz _ (mk_ag hv σ₀ a 0 0 0) a (mk_a hv ..)]
  have hc : ∀ a b : Fin g, a < b → N.c a b = N'.c a b := fun a b hab => by
    rw [← h.c _ (mk_ag hv σ₀ a b 0 0) a b hab (mk_a hv ..) (mk_b hv ..),
      ← h'.c _ (mk_ag hv σ₀ a b 0 0) a b hab (mk_a hv ..) (mk_b hv ..)]
  let Φ : (∀ a, N.S a) ≃ (∀ a, N'.S a) :=
    Equiv.piCongrRight fun a => (κ.e a).trans ((finCongr (hs a)).trans (κ'.e a).symm)
  have hcode : ∀ (z : ∀ a, N.S a) a, ((κ'.e a (Φ z a) : Fin _) : ℕ) = ((κ.e a (z a) : Fin _) : ℕ) := by
    intro z a
    simp [Φ]
  unfold Net.value
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    exact (h.W _ (mk_ag hv σ₀ a 0 ((κ.e a (z a) : Fin _) : ℕ) 0) a (z a) (mk_a hv ..) (mk_z hv ..)).eq
      (h'.W _ (mk_ag hv σ₀ a 0 ((κ.e a (z a) : Fin _) : ℕ) 0) a (Φ z a) (mk_a hv ..)
        (by rw [mk_z hv, hcode]))
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hab := mem_pairs.1 hp
    obtain ⟨a, b⟩ := p
    simp only at hab
    unfold Net.Ψ
    refine fac_eval_eq (hc a b hab) _ _ _ _ _ _ (fun q => ?_) (fun q => ?_)
    · exact (h.l _ (mk_ag hv σ₀ a b ((κ.e a (z a) : Fin _) : ℕ) q) a b hab (z a) q (mk_a hv ..) (mk_b hv ..)
        (mk_z hv ..) (mk_q hv ..)).eq
        (h'.l _ (mk_ag hv σ₀ a b ((κ.e a (z a) : Fin _) : ℕ) q) a b hab (Φ z a) q (mk_a hv ..) (mk_b hv ..)
          (by rw [mk_z hv, hcode]) (mk_q hv ..))
    · exact (h.r _ (mk_ag hv σ₀ a b ((κ.e b (z b) : Fin _) : ℕ) q) a b hab (z b) q (mk_a hv ..) (mk_b hv ..)
        (mk_z hv ..) (mk_q hv ..)).eq
        (h'.r _ (mk_ag hv σ₀ a b ((κ.e b (z b) : Fin _) : ℕ) q) a b hab (Φ z b) q (mk_a hv ..) (mk_b hv ..)
          (by rw [mk_z hv, hcode]) (mk_q hv ..))

end ECDLP.L93
end
