import Mathlib

/-!
# L114 / Ev: tag evaluation and reduction of the relation lattice to a prime-power part

Abstract setting: `G` a finite additive abelian group, `N • g = 0` for all `g`, `V : Fin k → G`
(in the application `(H₁, H₂, P, Q)`).  Tags live in `(ZMod N)^k`; `ev a = ∑ a_j • V_j`.
For a prime power `q ∣ N` with `M = N / q` coprime to `q`, the `ℓ`-projection is `π_ℓ = M • ·` and the
local evaluation is `evL μ = ∑ μ_j • (M • V_j)` on `(ZMod q)^k`.
* `evHom_intCast` : evaluation on integer lifts.
* `ev_local_compat` : `evL (ρ a) = M • ev a`  (`ρ` = reduction mod `q`).
* `ker_reduces` : `ρ (ker ev) = ker evL`  (the relation lattice `Rel_ℓ` is the reduction of the global one).
-/
namespace ECDLP.L114

open Finset

variable {G : Type*} [AddCommGroup G] {k : ℕ}

/-- the additive hom `ZMod n → G`, `x ↦ x • w`, for `n • w = 0` -/
def liftW (n : ℕ) (w : G) (h : n • w = 0) : ZMod n →+ G :=
  ZMod.lift n ⟨zmultiplesHom G w, by simpa using h⟩

theorem liftW_intCast (n : ℕ) (w : G) (h : n • w = 0) (z : ℤ) : liftW n w h (z : ZMod n) = z • w := by
  simp [liftW, ZMod.lift_coe]

/-- evaluation `(ZMod n)^k →+ G`, `μ ↦ ∑ μ_j • W_j`. -/
def evHom (n : ℕ) (W : Fin k → G) (hW : ∀ j, n • W j = 0) : (Fin k → ZMod n) →+ G where
  toFun μ := ∑ j, liftW n (W j) (hW j) (μ j)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem evHom_intCast (n : ℕ) (W : Fin k → G) (hW : ∀ j, n • W j = 0) (z : Fin k → ℤ) :
    evHom n W hW (fun j => (z j : ZMod n)) = ∑ j, z j • W j := by
  simp [evHom, liftW_intCast]

/-- every vector over `ZMod n` is the reduction of an integer vector -/
theorem exists_lift (n : ℕ) (μ : Fin k → ZMod n) : ∃ z : Fin k → ℤ, (fun j => (z j : ZMod n)) = μ :=
  ⟨fun j => ((μ j).cast : ℤ), by funext j; simp⟩

section loc
variable {N q M : ℕ}

/-- the local weights `M • V_j` are `q`-torsion when `q * M = N`. -/
theorem local_torsion (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N) (j : Fin k) :
    q • (M • V j) = 0 := by
  rw [← mul_nsmul', hqM]; exact hN _

/-- reduction mod `q` of tags. -/
def rho (hdvd : q ∣ N) : (Fin k → ZMod N) →+ (Fin k → ZMod q) :=
  AddMonoidHom.compLeft (ZMod.castHom hdvd (ZMod q)).toAddMonoidHom (Fin k)

theorem rho_intCast (hdvd : q ∣ N) (z : Fin k → ℤ) :
    rho hdvd (fun j => (z j : ZMod N)) = fun j => (z j : ZMod q) := by
  funext j; simp [rho]

theorem rho_surjective (hdvd : q ∣ N) : Function.Surjective (rho (k := k) hdvd) := by
  intro μ
  obtain ⟨z, rfl⟩ := exists_lift q μ
  exact ⟨fun j => (z j : ZMod N), rho_intCast hdvd z⟩

/-- the global and local evaluations (`hN : N • g = 0`, `q * M = N`). -/
def evG (V : Fin k → G) (hN : ∀ g : G, N • g = 0) : (Fin k → ZMod N) →+ G := evHom N V (fun _ => hN _)

def evL (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N) : (Fin k → ZMod q) →+ G :=
  evHom q (fun j => M • V j) (local_torsion V hN hqM)

/-- **compatibility**: `evL (ρ a) = M • ev a`  (the `ℓ`-projection `π_ℓ = M •`). -/
theorem ev_local_compat (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (a : Fin k → ZMod N) : evL V hN hqM (rho (Dvd.intro _ hqM) a) = M • evG V hN a := by
  obtain ⟨z, rfl⟩ := exists_lift N a
  rw [rho_intCast, evL, evG, evHom_intCast, evHom_intCast, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm]

/-- **the kernel reduces onto the local relation lattice**: every `μ` with `evL μ = 0` is the
reduction of a global relation `a ∈ ker ev` (needs `gcd(M, q) = 1`). -/
theorem ker_reduces (V : Fin k → G) (hN : ∀ g : G, N • g = 0) (hqM : q * M = N)
    (hcop : Nat.Coprime M q) (μ : Fin k → ZMod q) (hμ : evL V hN hqM μ = 0) :
    ∃ a : Fin k → ZMod N, evG V hN a = 0 ∧ rho (Dvd.intro _ hqM) a = μ := by
  obtain ⟨z, rfl⟩ := exists_lift q μ
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.isCoprime hcop : IsCoprime (M : ℤ) (q : ℤ))
  refine ⟨fun j => ((u * M * z j : ℤ) : ZMod N), ?_, ?_⟩
  · rw [evG, evHom_intCast]
    rw [evL, evHom_intCast] at hμ
    have : ∑ j, (u * M * z j) • V j = u • ∑ j, z j • (M • V j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, mul_smul]; congr 1; rw [mul_smul, natCast_zsmul, smul_comm]
    rw [this, hμ, smul_zero]
  · rw [rho_intCast]
    funext j
    have h1 : ((u * M : ℤ) : ZMod q) = 1 := by
      have : (u * M : ℤ) = 1 - q * v := by linarith
      rw [this]; simp
    have : ((u * M * z j : ℤ) : ZMod q) = ((u * M : ℤ) : ZMod q) * (z j : ZMod q) := by push_cast; ring
    rw [this, h1, one_mul]

end loc

end ECDLP.L114
