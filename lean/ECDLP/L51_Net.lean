import Mathlib
import ECDLP.L51_Strings
import ECDLP.L44_Exists

/-!
# L51 / Net: the value of L44's network equals `ncard (strings …)`

`net_eq_ncard` : for the instance `instOf` built from L35's input `(p,a,b,xR,yR,π)`, any parameters
`(N, B)` satisfying L44's size conditions (`ParOK`, which `par_exists` shows can always be met) give
`packedValue = (strings (n+1) (p,a,b,xR,yR,π)).ncard`.
-/
noncomputable section
namespace ECDLP.L51
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38

/-- `B = ⌈p^{1/(n+1)}⌉` as in L35 -/
def Bd (p n : ℕ) : ℕ := sInf {B | p ≤ B ^ (n + 1)}

/-- bit length of `B` -/
def ell (p n : ℕ) : ℕ := Nat.size (Bd p n)

/-- L44's instance for L35's input -/
def instOf (p a b xR yR n : ℕ) : ECDLP.L44.Inst :=
  ⟨p, (a : ℤ), (b : ℤ), Bd p n, 2 * (p : ℤ), 4 * (p : ℤ) + 1, ((xR : ℤ), (yR : ℤ))⟩

theorem Bd_mem {p : ℕ} (hp : 0 < p) (n : ℕ) : p ≤ Bd p n ^ (n + 1) :=
  Nat.sInf_mem (s := {B | p ≤ B ^ (n + 1)}) ⟨p, Nat.le_self_pow (by omega) p⟩

theorem Bd_le {p : ℕ} (hp : 0 < p) (n : ℕ) : Bd p n ≤ p :=
  Nat.sInf_le (show p ∈ {B | p ≤ B ^ (n + 1)} from Nat.le_self_pow (by omega) p)

theorem Bd_xx {p : ℕ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) (x : ℤ) (hx0 : 0 ≤ x) (hx : x < Bd p n) :
    x * x ≤ p := by
  lift x to ℕ using hx0
  have hx' : x < Bd p n := by exact_mod_cast hx
  have hnot : ¬ p ≤ x ^ (n + 1) := fun h =>
    absurd (Nat.sInf_le (show x ∈ {B | p ≤ B ^ (n + 1)} from h)) (by unfold Bd at hx'; omega)
  have : x * x ≤ x ^ (n + 1) := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · subst h0; simp
    · calc x * x = x ^ 2 := by ring
        _ ≤ x ^ (n + 1) := Nat.pow_le_pow_right h0 (by omega)
  have : x * x < p := by omega
  exact_mod_cast this.le

theorem shortW_eq (p a b : ℕ) : shortW p (a : ℤ) (b : ℤ) = Wc p a b := by
  simp [shortW, Wc]

/-- parameter conditions of `main_count` for the prefix `π` -/
def ParOK {n K : ℕ} (I : ECDLP.L44.Inst) (ℓ : ℕ) (π : List Bool) (e : Cn n ≃ Fin K) (N : NPar) (B : ℤ) : Prop :=
  1 ≤ N.b ∧ ℓ ≤ N.b * 2 ^ N.k ∧ (∀ c, I.cv c < 2 ^ (N.b * 2 ^ N.k)) ∧ 0 < B ∧
    (∀ c, ((famF (fun i : Fin (n + 1) => sgOf ℓ π i) e c).mass : ℤ) *
      ((2 ^ (N.b * 2 ^ N.k) : ℕ) : ℤ) ^ 2 < B) ∧
    N.SizeOK (combine (famF (fun i : Fin (n + 1) => sgOf ℓ π i) e) B)

theorem par_exists {n K : ℕ} (I : ECDLP.L44.Inst) (ℓ : ℕ) (π : List Bool) (e : Cn n ≃ Fin K) :
    ∃ (N : NPar) (B : ℤ), ParOK I ℓ π e N B := by
  set Z : ℕ := ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 with hZdef
  have hZ : ∀ c, I.cv c < Z := by
    intro c
    have h1 : (I.cv c).toNat ≤ Finset.univ.sup fun c : Cst => (I.cv c).toNat :=
      Finset.le_sup (f := fun c : Cst => (I.cv c).toNat) (Finset.mem_univ c)
    have h2 := Int.self_le_toNat (I.cv c)
    have : (I.cv c) < ((ℓ + (Finset.univ.sup fun c : Cst => (I.cv c).toNat) + 1 : ℕ) : ℤ) := by
      push_cast
      have h3 : ((I.cv c).toNat : ℤ) ≤ ((Finset.univ.sup fun c : Cst => (I.cv c).toNat : ℕ) : ℤ) := by
        exact_mod_cast h1
      have : (0 : ℤ) ≤ ℓ := by positivity
      linarith
    exact this
  obtain ⟨N, B, hb1, hℓN, hcvB, hB, hBd, hS⟩ := params_exist I (fun i : Fin (n + 1) => sgOf ℓ π i) e ℓ Z hZ
    (by omega)
  exact ⟨N, B, hb1, hℓN, hcvB, hB, hBd, hS⟩

theorem genfilter_congr {p : ℕ} [Fact p.Prime] (W1 W2 : WeierstrassCurve.Affine (ZMod p)) (h : W1 = W2)
    (FB : ZMod p → Prop) (R R' : ZMod p × ZMod p) (hR : R = R') (n : ℕ)
    (ψ : (Fin (n + 1) → ZMod p × ZMod p) → Prop) [DecidablePred ψ] :
    ((GenSet W1 FB R n).filter ψ).card = ((GenSet W2 FB R' n).filter ψ).card := by
  subst h hR; rfl

open Classical in
/-- **Network value = number of L35 strings with prefix `π`.** -/
theorem net_eq_ncard {n K : ℕ} (p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (π : List Bool) (hlen : π.length ≤ (n + 1) * (ell p n + 1)) (e : Cn n ≃ Fin K)
    (N : NPar) (B : ℤ) (hok : ParOK (instOf p a b xR yR n) (ell p n) π e N B) :
    packedValue (instOf p a b xR yR n) N B π (ell p n) e (Fintype.equivFin _) =
      ((ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard : ℤ) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨hb1, hℓ, hcv, hB, hBd, hS⟩ := hok
  haveI hpI : Fact (instOf p a b xR yR n).p.Prime := hp
  haveI hell : (shortW (instOf p a b xR yR n).p (instOf p a b xR yR n).a
      (instOf p a b xR yR n).b).IsElliptic := by
    show (shortW p (a : ℤ) (b : ℤ)).IsElliptic
    rw [shortW_eq]
    exact ⟨isUnit_iff_ne_zero.2 hΔ⟩
  have key := main_count (instOf p a b xR yR n) N π (ell p n) hℓ hlen e
    (by simp [instOf]) (by simpa [instOf] using ha) (by simp [instOf]) (by simpa [instOf] using hb)
    (by simpa [instOf] using Bd_le hp0 n)
    (fun x h0 h1 => Bd_xx hp0 hn x h0 (by simpa [instOf] using h1))
    (by simp [instOf]) (by simp [instOf]; omega)
    (by simp [instOf]; exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩)
    (by show (shortW p (a : ℤ) (b : ℤ)).Nonsingular (((xR : ℤ) : ZMod p)) (((yR : ℤ) : ZMod p))
        rw [shortW_eq]; simpa using hRns)
    hcv B hB hBd hS hb1 (Fintype.equivFin _)
  have e1 := ncard_strings_eq (p := p) n a b xR yR π hΔ hRns
  have h3 := genfilter_congr (shortW p (a : ℤ) (b : ℤ)) (Wc p a b) (shortW_eq p a b)
    (fun x : ZMod p => x.val < Bd p n) (((xR : ℤ) : ZMod p), ((yR : ℤ) : ZMod p))
    ((xR : ZMod p), (yR : ZMod p)) (by simp) n (fun P => π <+: strOf p (ell p n) P)
  have key' : packedValue (instOf p a b xR yR n) N B π (ell p n) e (Fintype.equivFin _) =
      ((((GenSet (shortW p (a : ℤ) (b : ℤ)) (fun x : ZMod p => x.val < Bd p n)
        (((xR : ℤ) : ZMod p), ((yR : ℤ) : ZMod p)) n).filter
          (fun P => π <+: strOf p (ell p n) P)).card : ℕ) : ℤ) := key
  have h5 : ((GenSet (Wc p a b) (fun x : ZMod p => x.val < Bd p n) ((xR : ZMod p), (yR : ZMod p)) n).filter
          (fun P => π <+: strOf p (ell p n) P)).card =
      (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard := e1.symm
  rw [key']
  have h6 := h3.trans h5
  exact_mod_cast h6

end ECDLP.L51

#print axioms ECDLP.L51.net_eq_ncard
