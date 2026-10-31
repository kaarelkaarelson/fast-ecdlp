import ECDLP.L80_Write
import ECDLP.L80_Lo

/-!
# L80 / FrameRng: the writer touches only scalars `10 .. S+2` and arrays `3 .. S+11` (syntactic frame, unconditional)
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

variable {sLo sHi aLo aHi : ℕ}

theorem Rng.mono {c : Cmd} (h : Rng sLo sHi aLo aHi c) {sLo' sHi' aLo' aHi' : ℕ} (h1 : sLo' ≤ sLo) (h2 : sHi ≤ sHi')
    (h3 : aLo' ≤ aLo) (h4 : aHi ≤ aHi') : Rng sLo' sHi' aLo' aHi' c :=
  ⟨fun y hy => by have := h.1 y hy; omega, fun a ha => by have := h.2 a ha; omega⟩

theorem addList_rng (z c : ℕ) (h : sLo ≤ z ∧ z ≤ sHi) (hc : sLo ≤ c ∧ c ≤ sHi) : ∀ xs, Rng sLo sHi aLo aHi (addList z c xs)
  | [] => Rng.skip
  | x :: xs => Rng.seq (Rng.loop hc (Rng.incr h)) (addList_rng z c h hc xs)

theorem sizeList_rng (h : ∀ q ∈ (l : List (ℕ × ℕ)), sLo ≤ q.2 ∧ q.2 ≤ sHi) (h780 : sLo ≤ 780 ∧ 780 ≤ sHi) (h781 : sLo ≤ 781 ∧ 781 ≤ sHi) :
    Rng sLo sHi aLo aHi (sizeList l) := by
  induction l with
  | nil => exact Rng.skip
  | cons q l ih =>
    obtain ⟨arr, z⟩ := q
    refine Rng.seq ?_ (ih (fun q' hq' => h q' (by simp [hq'])))
    have hz := h (arr, z) (by simp)
    unfold sizeC sizeBody
    exact Rng.seq (Rng.setK hz) (Rng.loop (by omega) (Rng.seq (Rng.rd h781) (Rng.ifZero Rng.skip (Rng.seq (Rng.copy hz) (Rng.incr hz)))))

theorem dblN_rng (z tmp c : ℕ) (hz : sLo ≤ z ∧ z ≤ sHi) (ht : sLo ≤ tmp ∧ tmp ≤ sHi) (hc : sLo ≤ c ∧ c ≤ sHi) :
    ∀ k, Rng sLo sHi aLo aHi (dblN z tmp c k)
  | 0 => Rng.skip
  | k + 1 => Rng.seq (dblN_rng z tmp c hz ht hc k) (Rng.seq (Rng.copy ht) (Rng.loop hc (Rng.incr hz)))

theorem padCopy_rng (dst src nS wS : ℕ) (hd : aLo ≤ dst ∧ dst ≤ aHi) (h818 : sLo ≤ 818 ∧ 818 ≤ sHi) (h819 : sLo ≤ 819 ∧ 819 ≤ sHi) :
    Rng sLo sHi aLo aHi (padCopy dst src nS wS) := by
  unfold padCopy padBody
  exact Rng.loop h818 (Rng.ifLt (Rng.seq (Rng.rd h819) (Rng.seq (Rng.ifZero Rng.skip (Rng.setK h819)) (Rng.wr hd)))
    (Rng.seq (Rng.setK h819) (Rng.wr hd)))

theorem padList_rng (wS : ℕ) (h818 : sLo ≤ 818 ∧ 818 ≤ sHi) (h819 : sLo ≤ 819 ∧ 819 ≤ sHi) :
    ∀ l : List (ℕ × ℕ × ℕ), (∀ q ∈ l, aLo ≤ q.1 ∧ q.1 ≤ aHi) → Rng sLo sHi aLo aHi (padList wS l)
  | [], _ => Rng.skip
  | (d, s, n) :: l, h => Rng.seq (padCopy_rng d s n wS (h (d, s, n) (by simp)) h818 h819)
      (padList_rng wS h818 h819 l (fun q hq => h q (by simp [hq])))

set_option maxHeartbeats 8000000 in
theorem frameW_rng (S : ℕ) (hS : 1400 ≤ S) : Rng 10 (S + 2) 3 (S + 11) (frameW S) := by
  unfold frameW
  rngc

end ECDLP.L80
