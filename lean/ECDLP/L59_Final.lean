import ECDLP.L59_ParOK

/-!
# L59 / Final: L56's end theorem with explicit parameters and no parameter hypotheses
-/
noncomputable section
namespace ECDLP.L59
open Finset ECDLP.L44 ECDLP.L30 ECDLP.L34 ECDLP.L38 ECDLP.L51 ECDLP.L35 ECDLP.L54 ECDLP.L56

variable {n : ℕ}

/-- Edge-network counts with the explicit parameters (`NParE (size p)`, `w = wP (size p)`). -/
def netCountX (p a b xR yR n : ℕ) (π : List Bool) : ℕ :=
  netCountE p a b xR yR (Fintype.equivFin (Cn n)) (fun _ => parOf p) π

theorem net_count_eq_ncardX (p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p))
    (π : List Bool) (hlen : π.length ≤ (n + 1) * (ell p n + 1)) :
    netCountX p a b xR yR n π = (ECDLP.strings (n + 1) (p, a, b, xR, yR, π)).ncard :=
  net_count_eq_ncardE p hn a b xR yR ha hb hx hy hΔ hRns (Fintype.equivFin (Cn n)) (fun _ => parOf p) π hlen
    (parOK_explicit p a b xR yR n hp.out.pos ha hb hx hy π _)

/-- **Main theorem, explicit parameters.**  The prefix search of L31 driven by the counts of the edge network
(child-specific messages, tight pair widths) with the explicit parameters `NParE (Nat.size p)`,
`w = wP (Nat.size p)` returns `lexLeast`.  No hypothesis on the parameters. -/
theorem search_computes_lexLeast_explicit (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (a b xR yR : ℕ)
    (ha : a < p) (hb : b < p) (hx : xR < p) (hy : yR < p)
    (hΔ : (Wc p a b).Δ ≠ 0)
    (hRns : (Wc p a b).toAffine.Nonsingular (xR : ZMod p) (yR : ZMod p)) :
    ECDLP.lexLeast (n + 1) (p, a, b, xR, yR, []) =
      if 0 < netCountX p a b xR yR n [] then
        some (ECDLP.L31.search (netCountX p a b xR yR n) ((n + 1) * (ell p n + 1)))
      else none :=
  search_computes_lexLeast_edge p hn a b xR yR ha hb hx hy hΔ hRns (Fintype.equivFin (Cn n)) (fun _ => parOf p)
    (fun π _ => parOK_explicit p a b xR yR n (Fact.out : p.Prime).pos ha hb hx hy π _)

end ECDLP.L59
end
