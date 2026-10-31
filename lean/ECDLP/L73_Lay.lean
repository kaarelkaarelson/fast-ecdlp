import ECDLP.L56_Edge
import ECDLP.L68_Code

/-!
# L73 / Lay: the gate enumeration of `edgeNet` (explicit, arithmetic)

Layout of `Fin g` (g = nι*A + Σ_c blk c):
* `src (i, s)` at `eι i * A + s`;
* identity block `c` starts at `nι*A + off c`, `off c = Σ_{t<c} blk t`, `blk c = nc*A + (A + (A + A*A))`, ordered
  `fa (j,s)` at `+ ecc j * A + s`, `mid k` at `+ nc*A + k`, `ib j` at `+ nc*A + A + j`, `car j` at `+ nc*A + 2A + j`.
-/
noncomputable section
namespace ECDLP.L73
open Finset ECDLP.L34 ECDLP.L35 ECDLP.L38 ECDLP.L54 ECDLP.L56

/-- slot and per-identity slot numberings -/
structure Lay (ι : Type) {K : ℕ} (ιc : Fin K → Type) where
  nι : ℕ
  eι : ι ≃ Fin nι
  nc : Fin K → ℕ
  ecc : ∀ c, ιc c ≃ Fin (nc c)

namespace Lay
variable {ι : Type} {K : ℕ} {ιc : Fin K → Type} (L : Lay ι ιc) (A : ℕ)

def blk (c : Fin K) : ℕ := L.nc c * A + (A + (A + A * A))

/-- extension of `nc` by `0` -/
def ncN (t : ℕ) : ℕ := if h : t < K then L.nc ⟨t, h⟩ else 0

def blkN (t : ℕ) : ℕ := L.ncN t * A + (A + (A + A * A))

def off (t : ℕ) : ℕ := ∑ s ∈ range t, L.blkN A s

def gTot : ℕ := L.nι * A + L.off A K

theorem blkN_fin (c : Fin K) : L.blkN A c = L.blk A c := by
  simp [blkN, blk, ncN]

theorem sum_blk_eq : ∑ c : Fin K, L.blk A c = L.off A K := by
  rw [off, ← Fin.sum_univ_eq_sum_range (L.blkN A) K]
  exact sum_congr rfl fun c _ => (L.blkN_fin A c).symm

/-- four-block sum -/
def sum4 (a b c d : ℕ) : Fin a ⊕ (Fin b ⊕ (Fin c ⊕ Fin d)) ≃ Fin (a + (b + (c + d))) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

theorem sum4_a {a b c d : ℕ} (x : Fin a) : (sum4 a b c d (.inl x) : ℕ) = x := by
  simp [sum4]
theorem sum4_b {a b c d : ℕ} (x : Fin b) : (sum4 a b c d (.inr (.inl x)) : ℕ) = a + x := by
  simp [sum4]
theorem sum4_c {a b c d : ℕ} (x : Fin c) : (sum4 a b c d (.inr (.inr (.inl x))) : ℕ) = a + (b + x) := by
  simp [sum4]
theorem sum4_d {a b c d : ℕ} (x : Fin d) : (sum4 a b c d (.inr (.inr (.inr x))) : ℕ) = a + (b + (c + x)) := by
  simp [sum4]

/-- gates of one identity -/
def gateE (c : Fin K) : Gate (ιc c) A ≃ Fin (L.blk A c) :=
  (gateEquiv (ιc c) A).trans <|
    (Equiv.sumCongr (((L.ecc c).prodCongr (Equiv.refl (Fin A))).trans finProdFinEquiv) (Equiv.refl _)).trans
      (sum4 (L.nc c * A) A A (A * A))

theorem gateE_fa (c : Fin K) (j : ιc c) (s : Fin A) :
    (L.gateE A c (.fa j s) : ℕ) = (L.ecc c j : ℕ) * A + s := by
  have : L.gateE A c (.fa j s) = sum4 (L.nc c * A) A A (A * A) (.inl (finProdFinEquiv (L.ecc c j, s))) := rfl
  rw [this, sum4_a, finProdFinEquiv_apply_val]; ring

theorem gateE_mid (c : Fin K) (k : Fin A) : (L.gateE A c (.mid k) : ℕ) = L.nc c * A + k := by
  have : L.gateE A c (.mid k) = sum4 (L.nc c * A) A A (A * A) (.inr (.inl k)) := rfl
  rw [this, sum4_b]

theorem gateE_ib (c : Fin K) (j : Fin A) : (L.gateE A c (.ib j) : ℕ) = L.nc c * A + (A + j) := by
  have : L.gateE A c (.ib j) = sum4 (L.nc c * A) A A (A * A) (.inr (.inr (.inl j))) := rfl
  rw [this, sum4_c]

theorem gateE_car (c : Fin K) (j : Fin (A * A)) :
    (L.gateE A c (.car j) : ℕ) = L.nc c * A + (A + (A + j)) := by
  have : L.gateE A c (.car j) = sum4 (L.nc c * A) A A (A * A) (.inr (.inr (.inr j))) := rfl
  rw [this, sum4_d]

/-- the enumeration of all gates -/
def enum : CG ι ιc A ≃ Fin (L.gTot A) :=
  (cgEquiv ι ιc A).trans <|
    (Equiv.sumCongr ((L.eι.prodCongr (Equiv.refl (Fin A))).trans finProdFinEquiv)
      ((Equiv.sigmaCongrRight (L.gateE A)).trans (finSigmaFinEquiv.trans (finCongr (L.sum_blk_eq A))))).trans
    (finSumFinEquiv.trans (finCongr rfl))

theorem enum_src (i : ι) (s : Fin A) : (L.enum A (.src i s) : ℕ) = L.eι i * A + s := by
  have : L.enum A (.src i s) = finSumFinEquiv (.inl (finProdFinEquiv (L.eι i, s))) := rfl
  rw [this]; simp [finProdFinEquiv_apply_val]; ring

theorem enum_gt (c : Fin K) (g : Gate (ιc c) A) :
    (L.enum A (.gt c g) : ℕ) = L.nι * A + (L.off A c + (L.gateE A c g : ℕ)) := by
  have : L.enum A (.gt c g) = finSumFinEquiv (.inr (finCongr (L.sum_blk_eq A) (finSigmaFinEquiv ⟨c, L.gateE A c g⟩))) := rfl
  rw [this]
  rw [finSumFinEquiv_apply_right]
  have h2 := finSigmaFinEquiv_apply (n := L.blk A) ⟨c, L.gateE A c g⟩
  have h3 : (∑ i : Fin c.val, L.blk A (Fin.castLE c.2.le i)) = L.off A c := by
    rw [off, ← Fin.sum_univ_eq_sum_range (L.blkN A) c.val]
    exact sum_congr rfl fun t _ => (L.blkN_fin A _).symm
  show L.nι * A + ((finSigmaFinEquiv ⟨c, L.gateE A c g⟩ : Fin _) : ℕ) = _
  rw [h2]
  simp only [h3]

end Lay
end ECDLP.L73
end
