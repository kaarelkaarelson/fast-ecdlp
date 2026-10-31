import ECDLP.L92_Hr

/-!
# L92 / Hr2: `famH r` meets `NetFamily.Spec`, `TopIface` for `famH r` without `hr`, and the transfer of `UniReq`.
-/
noncomputable section
namespace ECDLP.L85B
set_option linter.unusedSectionVars false
open Finset Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex SB UCost85 ECDLP.L65 ECDLP.L60 ECDLP.L58
  ECDLP.L57 ECDLP.L85A

theorem Ub_le_two_pow_extra (r n : ℕ) : Ub r n ≤ 2 ^ (Uc r + 4 * Xs n) := by
  have h1 : Uc r ≤ 2 ^ Uc r := Nat.lt_two_pow_self.le
  have h2 : Xs n ^ 4 ≤ 2 ^ (4 * Xs n) := pow_le_two_pow_mul _
  calc Ub r n = Uc r * Xs n ^ 4 := rfl
    _ ≤ 2 ^ Uc r * 2 ^ (4 * Xs n) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (Uc r + 4 * Xs n) := (pow_add _ _ _).symm

theorem famH_eTop (r K0 ℓ n mb : ℕ) :
    (famH r).eTop K0 ℓ n mb = (edgeFamily r).eTop K0 ℓ n mb + (Uc r + 4 * Xs n) := by
  unfold NetFamily.eTop
  show eFamE r _ _ n + (Uc r + 4 * Xs n) + (edgeFamily r).ePoly _ _ n mb = _
  simp only [edgeFamily]
  ring

theorem famH_spec (r : ℕ) : (famH r).Spec where
  n_le := (edgeFamily_spec r).n_le
  X4_le := (edgeFamily_spec r).X4_le
  nodes_le := (edgeFamily_spec r).nodes_le
  total_le := (edgeFamily_spec r).total_le
  eFam_le K g n h2 h3 := by
    have h := eOf_bound (Ub r n) (Wm r n) (Sb n) K g h2 h3
    show K * (eFamE r K g n + (Uc r + 4 * Xs n)) ≤ cE r * Xs n ^ 4 + K * (cE r * (g * Xs n ^ 3) + cE r * Xs n ^ 3)
    unfold eFamE
    have hX1 := Xs_pos n
    have hX3 : Xs n ≤ Xs n ^ 3 := Nat.le_self_pow (by norm_num) _
    have hX3' : 1 ≤ Xs n ^ 3 := Nat.one_le_pow _ _ hX1
    have e1 : Uc r + 4 * Xs n ≤ 1544836 * (r + 1) * Xs n ^ 3 := by
      unfold Uc; nlinarith [Nat.zero_le r, Nat.zero_le (r * Xs n ^ 3)]
    have e2 : K * (Uc r + 4 * Xs n) ≤ K * (1544836 * (r + 1) * Xs n ^ 3) := Nat.mul_le_mul_left _ e1
    simp only [Ub, Wm, Sb, Uc, Wcn, Scn] at h e2 ⊢
    unfold cE
    have h1 : 0 ≤ (r + 1) * Xs n ^ 4 := Nat.zero_le _
    have h2' : K * ((r + 1) * Xs n ^ 3) ≤ K * (g * ((r + 1) * Xs n ^ 3)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have h3' : g * ((r + 1) * Xs n ^ 3) ≤ K * (g * ((r + 1) * Xs n ^ 3)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.mul_add]
    nlinarith [Nat.zero_le (K * ((r + 1) * Xs n ^ 3)), Nat.zero_le (g * ((r + 1) * Xs n ^ 3))]
  req_of_exp {V m mb K0 ℓ n Z} hK hm hmb hZ hD hV := by
    rw [famH_eTop] at hZ
    have hZ0 : (edgeFamily r).eTop K0 ℓ n mb ≤ Z := by omega
    refine ⟨edgeReq_of hK hm hmb hZ0 hD hV, ?_⟩
    exact le_trans (Ub_le_two_pow_extra r n) (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hV)
  ok_mono h hVW := ⟨EdgeReq.mono h.1 hVW, le_trans h.2 hVW⟩

end ECDLP.L85B
end
