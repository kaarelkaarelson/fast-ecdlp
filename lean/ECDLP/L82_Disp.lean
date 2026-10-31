import ECDLP.L82_Floor

/-!
# L82 / Disp: a shallow dispatch with the guard merged into the kind test

L73's `outEx = decodeE I (u+5) (lett (u+20) dqE (outChain ..))`, `outChain` = linear 4-deep `ifLt` chain over the kind code `u+21`
with the guarded mid expression `guardE u E` in the third position (+1 more level).  `disp2` is a semantically equal (for ALL states)
dispatch in which the mid expression `E` sits directly under ONE test (kind = 2 and `dq < A`, one `ifLt`), and the other kinds sit in a
balanced tree.  `eval_disp2` : equal for all `sigma`; `dp_disp2`: exact depth.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace ECDLP.L82
open Finset Factoring.Aux Ex ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56 ECDLP.L58 ECDLP.L68 ECDLP.L73
open ECDLP.L79

/-- the original dispatch (L73's `outChain`, with the source branch `Es` and a guarded mid) -/
def chain0 (u : ℕ) (Es Efa Emid Eib Ecar : Ex) : Ex :=
  (.ifLt (.var (u + 21)) (.lit 1) Es
    (.ifLt (.var (u + 21)) (.lit 2) Efa
      (.ifLt (.var (u + 21)) (.lit 3) (guardE u Emid)
        (.ifLt (.var (u + 21)) (.lit 4) Eib Ecar))))

/-- the test "kind = 2 and dq < A" as a single comparison `|k-2| + (dq + 1 - A) < 1` -/
def midTest (u : ℕ) : Ex :=
  .add (.add (.sub (.var (u + 21)) (.lit 2)) (.sub (.lit 2) (.var (u + 21))))
    (.sub (.add (.var (u + 20)) (.lit 1)) (.var (u + 12)))

/-- the shallow dispatch -/
def disp2 (u : ℕ) (Es Efa Emid Eib Ecar : Ex) : Ex :=
  .ifLt (midTest u) (.lit 1) Emid
    (.ifLt (.var (u + 21)) (.lit 2) (.ifLt (.var (u + 21)) (.lit 1) Es Efa)
      (.ifLt (.var (u + 21)) (.lit 3) (.lit 0) (.ifLt (.var (u + 21)) (.lit 4) Eib Ecar)))

theorem disp2_aux (k d a vs vf vm vi vc : ℕ) :
    (if k - 2 + (2 - k) + (d + 1 - a) < 1 then vm
      else if k < 2 then (if k < 1 then vs else vf)
        else if k < 3 then 0 else if k < 4 then vi else vc) =
    (if k < 1 then vs else if k < 2 then vf else if k < 3 then (if d < a then vm else 0)
      else if k < 4 then vi else vc) := by
  split_ifs <;> first | rfl | (exfalso; omega)

theorem eval_disp2 (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (u : ℕ) (Es Efa Emid Eib Ecar : Ex) :
    Ex.eval σ A (disp2 u Es Efa Emid Eib Ecar) = Ex.eval σ A (chain0 u Es Efa Emid Eib Ecar) := by
  simp only [disp2, chain0, midTest, guardE, Ex.eval]
  exact disp2_aux _ _ _ _ _ _ _ _

theorem dp_disp2 (u : ℕ) (Es Efa Emid Eib Ecar : Ex) :
    Ex.dp (disp2 u Es Efa Emid Eib Ecar) =
      max (max 4 (Ex.dp Emid)) (max (max (Ex.dp Es) (Ex.dp Efa) + 2) (max (Ex.dp Eib) (Ex.dp Ecar) + 3)) + 1 := by
  simp only [disp2, midTest, Ex.dp]
  omega

theorem dp_chain0 (u : ℕ) (Es Efa Emid Eib Ecar : Ex) :
    Ex.dp (chain0 u Es Efa Emid Eib Ecar) =
      max (max (Ex.dp Es + 1) (Ex.dp Efa + 2)) (max (Ex.dp Emid + 4) (max (Ex.dp Eib) (Ex.dp Ecar) + 4)) := by
  have := dpT_pos Emid
  have := dpT_pos Es
  have := dpT_pos Efa
  have := dpT_pos Eib
  have := dpT_pos Ecar
  simp only [chain0, guardE, Ex.dp]
  omega

end ECDLP.L82
end
