import ECDLP.L76_Layer

/-!
# L80 / Lo: unconditional syntactic frame of `checkC` (writes only scalars `>= 10`, arrays `>= 3`)
-/
namespace ECDLP.L80
open ECDLP.L76 Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the scalars written are `>= sLo` and `<= sHi`, the arrays written are `>= aLo` and `<= aHi` -/
def Rng (sLo sHi aLo aHi : ℕ) (c : Cmd) : Prop :=
  (∀ y ∈ c.wsc, sLo ≤ y ∧ y ≤ sHi) ∧ (∀ a ∈ c.war, aLo ≤ a ∧ a ≤ aHi)

variable {sLo sHi aLo aHi : ℕ}

theorem Rng.seq {s t : Cmd} (hs : Rng sLo sHi aLo aHi s) (ht : Rng sLo sHi aLo aHi t) : Rng sLo sHi aLo aHi (.seq s t) := by
  refine ⟨fun y hy => ?_, fun a ha => ?_⟩
  · simp only [Cmd.wsc, List.mem_append] at hy; rcases hy with h | h; exact hs.1 y h; exact ht.1 y h
  · simp only [Cmd.war, List.mem_append] at ha; rcases ha with h | h; exact hs.2 a h; exact ht.2 a h

theorem Rng.loop {b c : ℕ} {body : Cmd} (hc : sLo ≤ c ∧ c ≤ sHi) (h : Rng sLo sHi aLo aHi body) :
    Rng sLo sHi aLo aHi (.loop b c body) := by
  refine ⟨fun y hy => ?_, fun a ha => h.2 a (by simpa [Cmd.war] using ha)⟩
  simp only [Cmd.wsc, List.mem_cons] at hy; rcases hy with rfl | h'; exact hc; exact h.1 y h'

theorem Rng.ifLt {x y : ℕ} {s t : Cmd} (hs : Rng sLo sHi aLo aHi s) (ht : Rng sLo sHi aLo aHi t) :
    Rng sLo sHi aLo aHi (.ifLt x y s t) := by
  refine ⟨fun y hy => ?_, fun a ha => ?_⟩
  · simp only [Cmd.wsc, List.mem_append] at hy; rcases hy with h | h; exact hs.1 y h; exact ht.1 y h
  · simp only [Cmd.war, List.mem_append] at ha; rcases ha with h | h; exact hs.2 a h; exact ht.2 a h

theorem Rng.ifZero {x : ℕ} {s t : Cmd} (hs : Rng sLo sHi aLo aHi s) (ht : Rng sLo sHi aLo aHi t) :
    Rng sLo sHi aLo aHi (.ifZero x s t) := by
  refine ⟨fun y hy => ?_, fun a ha => ?_⟩
  · simp only [Cmd.wsc, List.mem_append] at hy; rcases hy with h | h; exact hs.1 y h; exact ht.1 y h
  · simp only [Cmd.war, List.mem_append] at ha; rcases ha with h | h; exact hs.2 a h; exact ht.2 a h

theorem Rng.skip : Rng sLo sHi aLo aHi .skip := ⟨by simp [Cmd.wsc], by simp [Cmd.war]⟩
theorem Rng.setK {x k : ℕ} (h : sLo ≤ x ∧ x ≤ sHi) : Rng sLo sHi aLo aHi (.setK x k) := ⟨by simpa [Cmd.wsc] using h, by simp [Cmd.war]⟩
theorem Rng.copy {x y : ℕ} (h : sLo ≤ x ∧ x ≤ sHi) : Rng sLo sHi aLo aHi (.copy x y) := ⟨by simpa [Cmd.wsc] using h, by simp [Cmd.war]⟩
theorem Rng.incr {x : ℕ} (h : sLo ≤ x ∧ x ≤ sHi) : Rng sLo sHi aLo aHi (.incr x) := ⟨by simpa [Cmd.wsc] using h, by simp [Cmd.war]⟩
theorem Rng.decr {x : ℕ} (h : sLo ≤ x ∧ x ≤ sHi) : Rng sLo sHi aLo aHi (.decr x) := ⟨by simpa [Cmd.wsc] using h, by simp [Cmd.war]⟩
theorem Rng.rd {x a i o : ℕ} (h : sLo ≤ x ∧ x ≤ sHi) : Rng sLo sHi aLo aHi (.rd x a i o) := ⟨by simpa [Cmd.wsc] using h, by simp [Cmd.war]⟩
theorem Rng.wr {a i o y : ℕ} (h : aLo ≤ a ∧ a ≤ aHi) : Rng sLo sHi aLo aHi (.wr a i o y) := ⟨by simp [Cmd.wsc], by simpa [Cmd.war] using h⟩


/-- the range of the checks: scalars `710..799`, arrays `20..62` -/
abbrev Rc := Rng 710 799 20 62

theorem addC_rng (neg : Bool) (dst src : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) : Rc (addC neg dst src) := by
  unfold addC addBody
  refine Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.setK (by omega)) (Rng.loop (by omega) ?_))
  refine Rng.seq (Rng.rd (by omega)) (Rng.seq (Rng.rd (by omega)) (Rng.seq ?_ (Rng.seq (Rng.copy (by omega)) (Rng.seq (Rng.ifZero Rng.skip (Rng.incr (by omega)))
    (Rng.seq (Rng.ifZero Rng.skip (Rng.incr (by omega))) (Rng.seq (Rng.ifLt (Rng.setK (by omega)) (Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.decr (by omega)) (Rng.decr (by omega))))) (Rng.wr hd)))))))
  cases neg <;> simp only [Bool.false_eq_true, if_false, if_true] <;> first | exact Rng.skip | exact Rng.ifZero (Rng.setK (by omega)) (Rng.setK (by omega))

theorem copyA_rng (dst src : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) : Rc (copyA dst src) := by
  unfold copyA copyBody
  exact Rng.loop (by omega) (Rng.seq (Rng.rd (by omega)) (Rng.seq (Rng.ifZero Rng.skip (Rng.setK (by omega))) (Rng.wr hd)))

theorem zeroA_rng (dst : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) : Rc (zeroA dst) := by
  unfold zeroA zeroBody
  exact Rng.loop (by omega) (Rng.seq (Rng.setK (by omega)) (Rng.wr hd))

theorem condSub_rng (dst src tmp : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) (ht : 20 ≤ tmp ∧ tmp ≤ 62) : Rc (condSub dst src tmp) := by
  unfold condSub
  exact Rng.seq (copyA_rng _ _ ht) (Rng.seq (addC_rng _ _ _ hd) (Rng.ifZero (copyA_rng _ _ hd) Rng.skip))

theorem addMod_rng (dst src P tmp : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) (ht : 20 ≤ tmp ∧ tmp ≤ 62) : Rc (addMod dst src P tmp) := by
  unfold addMod
  exact Rng.seq (addC_rng _ _ _ hd) (condSub_rng _ _ _ hd ht)

theorem dblMod_rng (dst P tmp tmp2 : ℕ) (hd : 20 ≤ dst ∧ dst ≤ 62) (ht : 20 ≤ tmp ∧ tmp ≤ 62) (ht2 : 20 ≤ tmp2 ∧ tmp2 ≤ 62) :
    Rc (dblMod dst P tmp tmp2) := by
  unfold dblMod
  exact Rng.seq (copyA_rng _ _ ht2) (addMod_rng _ _ _ _ hd ht)

theorem mulMod_rng (acc A B P tmp tmp2 : ℕ) (hd : 20 ≤ acc ∧ acc ≤ 62) (ht : 20 ≤ tmp ∧ tmp ≤ 62) (ht2 : 20 ≤ tmp2 ∧ tmp2 ≤ 62) :
    Rc (mulMod acc A B P tmp tmp2) := by
  unfold mulMod mulBody
  exact Rng.seq (zeroA_rng _ hd) (Rng.seq (Rng.copy (by omega)) (Rng.loop (by omega)
    (Rng.seq (dblMod_rng _ _ _ _ hd ht ht2) (Rng.seq (Rng.rd (by omega)) (Rng.seq (Rng.ifZero Rng.skip (addMod_rng _ _ _ _ hd ht)) (Rng.decr (by omega)))))))

theorem geC_rng (tmp A B : ℕ) (ht : 20 ≤ tmp ∧ tmp ≤ 62) : Rc (geC tmp A B) := by
  unfold geC
  exact Rng.seq (copyA_rng _ _ ht) (addC_rng _ _ _ ht)

theorem oneA_rng (arr : ℕ) (h : 20 ≤ arr ∧ arr ≤ 62) : Rc (oneA arr) := by
  unfold oneA
  exact Rng.seq (zeroA_rng _ h) (Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.setK (by omega)) (Rng.wr h)))

theorem powA_rng (arr : ℕ) (h : 20 ≤ arr ∧ arr ≤ 62) : Rc (powA arr) := by
  unfold powA
  exact Rng.seq (zeroA_rng _ h) (Rng.seq (Rng.setK (by omega)) (Rng.wr h))

theorem setBits_rng (arr : ℕ) (h : 20 ≤ arr ∧ arr ≤ 62) : ∀ l, Rc (setBits arr l)
  | [] => Rng.skip
  | i :: l => Rng.seq (setBits_rng arr h l) (by unfold setBit; exact Rng.seq (Rng.setK (by omega)) (Rng.wr h))

theorem constA_rng (arr : ℕ) (l : List ℕ) (h : 20 ≤ arr ∧ arr ≤ 62) : Rc (constA arr l) := by
  unfold constA
  exact Rng.seq (zeroA_rng _ h) (Rng.seq (Rng.setK (by omega)) (setBits_rng arr h l))

theorem powSeq_rng (C T1 T2 Pn tA tB : ℕ) (h1 : 20 ≤ T1 ∧ T1 ≤ 62) (h2 : 20 ≤ T2 ∧ T2 ≤ 62) (hA : 20 ≤ tA ∧ tA ≤ 62)
    (hB : 20 ≤ tB ∧ tB ≤ 62) : ∀ k, Rc (powSeq C T1 T2 Pn tA tB k)
  | 0 => Rng.skip
  | k + 1 => Rng.seq (powSeq_rng C T1 T2 Pn tA tB h1 h2 hA hB k) (by
      unfold powStep; exact Rng.seq (mulMod_rng _ _ _ _ _ _ h2 hA hB) (copyA_rng _ _ h1))

theorem rootC_rng (m C T1 T2 Pn p tA tB : ℕ) (hC : 20 ≤ C ∧ C ≤ 62) (h1 : 20 ≤ T1 ∧ T1 ≤ 62) (h2 : 20 ≤ T2 ∧ T2 ≤ 62)
    (hA : 20 ≤ tA ∧ tA ≤ 62) (hB : 20 ≤ tB ∧ tB ≤ 62) : Rc (rootC m C T1 T2 Pn p tA tB) := by
  unfold rootC rootBody
  exact Rng.seq (zeroA_rng _ hC) (Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.copy (by omega))
    (Rng.loop (by omega) (Rng.seq (Rng.wr hC) (Rng.seq (copyA_rng _ _ h1) (Rng.seq (powSeq_rng C T1 T2 Pn tA tB h1 h2 hA hB _)
      (Rng.seq (geC_rng _ _ _ hA) (Rng.seq (Rng.ifZero Rng.skip (Rng.wr hC)) (Rng.decr (by omega))))))))))) 

theorem blkRd_rng (dst : ℕ) (h : 20 ≤ dst ∧ dst ≤ 62) : Rc (blkRd dst) := by
  unfold blkRd blkBody
  exact Rng.seq (Rng.setK (by omega)) (Rng.seq (Rng.setK (by omega)) (Rng.loop (by omega)
    (Rng.ifZero (Rng.seq (Rng.rd (by omega)) (Rng.ifZero (Rng.seq (Rng.setK (by omega)) (Rng.incr (by omega)))
      (Rng.seq (Rng.rd (by omega)) (Rng.seq (Rng.wr h) (Rng.seq (Rng.incr (by omega)) (Rng.seq (Rng.incr (by omega)) (Rng.incr (by omega))))))))
      Rng.skip)))

theorem parseAll_rng : Rc parseAll := by
  unfold parseAll zero5 aJunk aRP aRA aRB aRX aRY
  exact Rng.seq (Rng.seq (zeroA_rng _ (by omega)) (Rng.seq (zeroA_rng _ (by omega)) (Rng.seq (zeroA_rng _ (by omega))
    (Rng.seq (zeroA_rng _ (by omega)) (zeroA_rng _ (by omega)))))) (Rng.seq (Rng.setK (by omega))
    (Rng.seq (blkRd_rng _ (by omega)) (Rng.seq (blkRd_rng _ (by omega)) (Rng.seq (blkRd_rng _ (by omega))
    (Rng.seq (blkRd_rng _ (by omega)) (Rng.seq (blkRd_rng _ (by omega)) (blkRd_rng _ (by omega))))))))

theorem sizeC_rng (arr z : ℕ) (hz : 710 ≤ z ∧ z ≤ 799) : Rc (sizeC arr z) := by
  unfold sizeC sizeBody
  exact Rng.seq (Rng.setK hz) (Rng.loop (by omega) (Rng.seq (Rng.rd (by omega)) (Rng.ifZero Rng.skip (Rng.seq (Rng.copy hz) (Rng.incr hz)))))

theorem repAdd_rng (l : ℕ) : ∀ k, Rc (repAdd l k)
  | 0 => Rng.skip
  | k + 1 => Rng.seq (repAdd_rng l k) (by unfold addL; exact Rng.seq (Rng.loop (by omega) (Rng.incr (by omega))) (Rng.incr (by omega)))

theorem nlenFlag_rng (m l f : ℕ) (hf : 710 ≤ f ∧ f ≤ 799) : Rc (nlenFlag m l f) := by
  unfold nlenFlag
  exact Rng.seq (Rng.setK (by omega)) (Rng.seq (repAdd_rng l m) (Rng.ifLt (Rng.setK hf) (Rng.setK hf)))

theorem repN_rng : ∀ k, Rc (repN k)
  | 0 => Rng.skip
  | k + 1 => Rng.seq (repN_rng k) (by unfold addN; exact Rng.loop (by omega) (Rng.incr (by omega)))

macro "rngc" : tactic => `(tactic| (repeat' (first
  | apply Rng.seq | apply Rng.ifZero | apply Rng.ifLt | apply Rng.loop | apply Rng.skip | apply Rng.setK
  | apply Rng.copy | apply Rng.rd | apply Rng.incr | apply Rng.decr | apply Rng.wr
  | apply powSeq_rng | apply repN_rng | apply repAdd_rng)) <;> omega)

set_option maxHeartbeats 4000000 in
theorem computeC_rng (m : ℕ) : Rc (computeC m) := by
  unfold computeC
  rngc

set_option maxHeartbeats 4000000 in
theorem checkC_rng (m : ℕ) : Rc (checkC m) := by
  unfold checkC
  refine Rng.seq (by unfold setW; rngc) (Rng.seq parseAll_rng (Rng.seq (computeC_rng m) ?_))
  unfold oddC andFlags
  rngc

end ECDLP.L80
