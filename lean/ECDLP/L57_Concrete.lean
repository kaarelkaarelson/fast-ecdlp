import ECDLP.L57_Inst

/-!
# L57 / Concrete: the engine size conditions for the actual ECDLP decomposition network

`ecdlp_engine_conditions`: for L44's instance system (identities `Cn n`, `K = card (Cn n) ≤ 18 (n+1)`, slots `Slot n`),
every `Z` (bits per shared slot) with `ℓ ≤ Z ≤ L` and all constants `< Z`, and every `G` with `G⁴ ≤ L`:
there are gadget parameters `(N0, w)` (`ParOK'`: exactly the hypotheses under which `edge_value`/`main_count_edge`
hold) such that the `edgeNet` of the instance, coarsened into `G` clusters, has
* the same value as `edgeValue I N0 w π ℓ e eg` (L56),
* `Net.total ≤ 183168 (n+1) L`,
* `Net.Fits P` for some `P` with `G · P ≤ 185244 (n+1) L`.
Constants are crude (worst-case incidences `≤ 12` slots per identity, `≤ K` identities per slot).
-/
noncomputable section
namespace ECDLP.L57
open Finset ECDLP.L30 ECDLP.L44 ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 Factoring.Aux

variable {n K : ℕ}

open Classical in
theorem ecdlp_engine_conditions (I : ECDLP.L44.Inst) (ℓ : ℕ) (π : List Bool) (e : Cn n ≃ Fin K)
    (Z L G : ℕ) (hZ1 : 1 ≤ Z) (hZL : Z ≤ L) (hℓ : ℓ ≤ Z) (hcv : ∀ c, I.cv c < (Z : ℤ))
    (hG : 0 < G) (hG4 : G ^ 4 ≤ L) :
    ∃ (N0 : NPar) (w : Fin K → ℕ), ParOK' I ℓ π e N0 w ∧
      ∀ {g : ℕ} (eg : CG (Slot n) (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) N0.A ≃ Fin g),
        ∃ χ : Fin g → Fin G,
          (∃ P : ℕ, ((((edgeNet (w := w) (fun c => Subtype.val)
              (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
              (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
                (fun i : Fin (n + 1) => xcOf ℓ π i)))).toGNet).toNet eg).coarsen χ).Fits P ∧
              G * P ≤ 185244 * (n + 1) * L) ∧
          ((((edgeNet (w := w) (fun c => Subtype.val)
              (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
              (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
                (fun i : Fin (n + 1) => xcOf ℓ π i)))).toGNet).toNet eg).coarsen χ).total ≤
            183168 * (n + 1) * L ∧
          ((((edgeNet (w := w) (fun c => Subtype.val)
              (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
              (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i)
                (fun i : Fin (n + 1) => xcOf ℓ π i)))).toGNet).toNet eg).coarsen χ).value =
            edgeValue I N0 w π ℓ e eg := by
  obtain ⟨N0, hb1, hZb, hbD, hDZ, h1, h2, h3⟩ := par_efficient Z hZ1
  set w : Fin K → ℕ := fun _ => 5 with hw
  have hS : ∀ c, (NP N0 w c).SizeOK (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e c) :=
    fun c => sizeOK_fr _ e N0 w c h1 h2 h3
  have hcv' : ∀ c, I.cv c < 2 ^ (N0.b * 2 ^ N0.k) := by
    intro c
    have h4 : (Z : ℤ) < 2 ^ Z := by exact_mod_cast Nat.lt_two_pow_self
    have h5 : (2 : ℤ) ^ Z ≤ 2 ^ (N0.b * 2 ^ N0.k) := pow_le_pow_right₀ (by norm_num) hZb
    exact (hcv c).trans (h4.trans_le h5)
  have hpar : ParOK' I ℓ π e N0 w := ⟨hb1, hℓ.trans hZb, hcv', hS⟩
  refine ⟨N0, w, hpar, fun {g} eg => ?_⟩
  have hKc : K ≤ 18 * (n + 1) := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin] at h
    have h2 := card_Cn_le (n := n)
    omega
  have hnn : ∀ c, Fintype.card (UC (fun i : Fin (n + 1) => sgOf ℓ π i) e c) ≤ 12 := fun c => card_UC_le _ e c
  have hocc : ∀ i, occ (ιc := UC (fun i : Fin (n + 1) => sgOf ℓ π i) e) (fun c => Subtype.val) i ≤ 18 * (n + 1) :=
    fun i => (occ_le_K (fun c => Subtype.val) (fun c => Subtype.val_injective) i).trans hKc
  have hDL : 2 ^ N0.k * 2 ^ N0.k ≤ 16 * L := hDZ.trans (Nat.mul_le_mul_left _ hZL)
  have hb : N0.b ≤ 1 * 2 ^ N0.k := by omega
  have hθ : 4 * 16 ^ 3 ≤ 12 ^ 4 := by norm_num
  obtain ⟨χ, hF, hT, hGP, hV⟩ := edgeNet_engine_fits (w := w) (fun c => Subtype.val)
    (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
    (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i)))
    12 (18 * (n + 1)) 1 5 18 16 12 (n + 1) L G hnn hocc (fun c => le_rfl) hb hDL hKc hθ hG hG4 hS hb1 eg
  refine ⟨χ, ⟨_, hF, ?_⟩, ?_, ?_⟩
  · refine hGP.trans ?_
    have hm : 1 ≤ n + 1 := by omega
    nlinarith [Nat.mul_le_mul_right L hm, Nat.zero_le (n * L)]
  · refine hT.trans (le_of_eq ?_)
    ring
  · rw [hV]
    exact (edge_value (w := w) (fun c => Subtype.val) (frF (fun i : Fin (n + 1) => sgOf ℓ π i) e)
      (okC N0 (Cl I (N0.b * 2 ^ N0.k) (fun i : Fin (n + 1) => sgOf ℓ π i) (fun i : Fin (n + 1) => xcOf ℓ π i)))
      hS hb1 eg).symm

end ECDLP.L57
end

#print axioms ECDLP.L57.ecdlp_engine_conditions
