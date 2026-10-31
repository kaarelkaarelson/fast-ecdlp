import ECDLP.L76_Env

/-!
# L76 / Env2: the library routines as environment transformers
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

theorem env_mulMod (acc A B P tmp tmp2 : ℕ) (hnd : List.Nodup [acc, A, B, P, tmp, tmp2]) (hacc : acc ∈ trk)
    (hA : A ∈ trk) (hB : B ∈ trk) (hP : P ∈ trk) (ht1 : tmp ∈ scr) (ht2 : tmp2 ∈ scr) (s : St) (W : ℕ) (v : ℕ → ℕ)
    (hs : Env s W v) (hlt : v A < v P) (h2 : 2 * v P ≤ 2 ^ W) :
    Env (Cmd.run (mulMod acc A B P tmp tmp2) s).1 W (Function.update v acc ((v A * v B) % v P)) ∧
    ScKeep ZAll s (Cmd.run (mulMod acc A B P tmp tmp2) s).1 ∧ ArK AR s (Cmd.run (mulMod acc A B P tmp tmp2) s).1 ∧
    (Cmd.run (mulMod acc A B P tmp tmp2) s).2 ≤ 300 * W * W + 300 * W + 20 := by
  have eA := hs.2 A hA
  have eB := hs.2 B hB
  have eP := hs.2 P hP
  obtain ⟨m1, m2, m3, m4, m5⟩ := mulMod_run acc A B P tmp tmp2 hnd s W hs.1 (by rw [eA, eP]; exact hlt) (by rw [eP]; exact h2)
  have hz : ScKeep ZAll s (Cmd.run (mulMod acc A B P tmp tmp2) s).1 := m4.mono ZM_sub
  refine ⟨env_step hs hacc ?_ ?_ ?_, hz, m3.mono ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne
    apply m3 k
    intro h; rcases h with h | h | h
    · exact hne h
    · subst h; exact scr_not_trk _ ht1 hk
    · subst h; exact scr_not_trk _ ht2 hk
  · rw [m2, eA, eB, eP]
  · intro a ha; rcases ha with h | h | h
    · subst h; exact trk_range _ hacc
    · subst h; exact scr_range _ ht1
    · subst h; exact scr_range _ ht2

theorem env_dblMod (acc P tmp tmp2 : ℕ) (h1 : acc ≠ P) (h2 : acc ≠ tmp) (h3 : acc ≠ tmp2) (h4 : P ≠ tmp) (h5 : P ≠ tmp2)
    (h6 : tmp ≠ tmp2) (hacc : acc ∈ trk) (hP : P ∈ trk) (ht1 : tmp ∈ scr) (ht2 : tmp2 ∈ scr) (s : St) (W : ℕ)
    (v : ℕ → ℕ) (hs : Env s W v) (hlt : v acc < v P) (h2P : 2 * v P ≤ 2 ^ W) :
    Env (Cmd.run (dblMod acc P tmp tmp2) s).1 W (Function.update v acc ((2 * v acc) % v P)) ∧
    ScKeep ZAll s (Cmd.run (dblMod acc P tmp tmp2) s).1 ∧ ArK AR s (Cmd.run (dblMod acc P tmp tmp2) s).1 ∧ (Cmd.run (dblMod acc P tmp tmp2) s).2 ≤ 100 * W + 50 := by
  have eA := hs.2 acc hacc
  have eP := hs.2 P hP
  obtain ⟨m1, m2, m3, m4, m5⟩ := dblMod_run acc P tmp tmp2 h1 h2 h3 h4 h5 h6 s W hs.1 (by rw [eA, eP]; exact hlt) (by rw [eP]; exact h2P)
  have hz : ScKeep ZAll s (Cmd.run (dblMod acc P tmp tmp2) s).1 := m4.mono (fun y h => ZB_sub y h)
  refine ⟨env_step hs hacc ?_ ?_ ?_, hz, m3.mono ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne
    apply m3 k
    intro h; rcases h with h | h | h
    · exact hne h
    · subst h; exact scr_not_trk _ ht1 hk
    · subst h; exact scr_not_trk _ ht2 hk
  · rw [m2, eA, eP]
  · intro a ha; rcases ha with h | h | h
    · subst h; exact trk_range _ hacc
    · subst h; exact scr_range _ ht1
    · subst h; exact scr_range _ ht2

theorem env_addMod (dst src P tmp : ℕ) (h1 : dst ≠ src) (h2 : dst ≠ P) (h3 : dst ≠ tmp) (h4 : src ≠ P) (h5 : P ≠ tmp)
    (h6 : src ≠ tmp) (hd : dst ∈ trk) (hsrc : src ∈ trk) (hP : P ∈ trk) (ht : tmp ∈ scr) (s : St) (W : ℕ) (v : ℕ → ℕ)
    (hs : Env s W v) (hA : v dst < v P) (hB : v src < v P) (h2P : 2 * v P ≤ 2 ^ W) :
    Env (Cmd.run (addMod dst src P tmp) s).1 W (Function.update v dst ((v dst + v src) % v P)) ∧
    ScKeep ZAll s (Cmd.run (addMod dst src P tmp) s).1 ∧ ArK AR s (Cmd.run (addMod dst src P tmp) s).1 ∧ (Cmd.run (addMod dst src P tmp) s).2 ≤ 90 * W + 40 := by
  have eA := hs.2 dst hd
  have eS := hs.2 src hsrc
  have eP := hs.2 P hP
  obtain ⟨m1, m2, m3, m4, m5⟩ := addMod_run dst src P tmp h1 h2 h3 h4 h5 h6 s W hs.1 (by rw [eA, eP]; exact hA)
    (by rw [eS, eP]; exact hB) (by rw [eP]; exact h2P)
  have hz : ScKeep ZAll s (Cmd.run (addMod dst src P tmp) s).1 := m4.mono ZB_sub
  refine ⟨env_step hs hd ?_ ?_ ?_, hz, m3.mono ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne
    apply m3 k
    intro h; rcases h with h | h
    · exact hne h
    · subst h; exact scr_not_trk _ ht hk
  · rw [m2, eA, eS, eP]
  · intro a ha; rcases ha with h | h
    · subst h; exact trk_range _ hd
    · subst h; exact scr_range _ ht

theorem env_copy (dst src : ℕ) (hds : dst ≠ src) (hsrc : src ∈ trk) (s : St) (W : ℕ) (v : ℕ → ℕ)
    (hs : Env s W v) (hdt : dst ∈ trk) :
    Env (Cmd.run (copyA dst src) s).1 W (Function.update v dst (v src)) ∧ ScKeep ZAll s (Cmd.run (copyA dst src) s).1 ∧
    ArK AR s (Cmd.run (copyA dst src) s).1 ∧
    (Cmd.run (copyA dst src) s).2 ≤ 7 * W + 1 := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := copyA_run dst src hds s W hs.1
  have hz : ScKeep ZAll s (Cmd.run (copyA dst src) s).1 := m5.mono ZC_sub
  refine ⟨env_step hs hdt ?_ ?_ ?_, hz, ArK.mono (D := fun a => a = dst) m4 ?_, m6⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne; exact m4 k hne
  · rw [m3, hs.2 src hsrc]
  · intro a ha; subst ha; exact trk_range _ hdt

theorem env_oneA (arr : ℕ) (harr : arr ∈ trk) (s : St) (W : ℕ) (v : ℕ → ℕ) (hs : Env s W v) (hW : 1 ≤ W) :
    Env (Cmd.run (oneA arr) s).1 W (Function.update v arr 1) ∧ ScKeep ZAll s (Cmd.run (oneA arr) s).1 ∧ ArK AR s (Cmd.run (oneA arr) s).1 ∧
    (Cmd.run (oneA arr) s).2 ≤ 5 * W + 10 := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := oneA_run arr s W hs.1 hW
  have hz : ScKeep ZAll s (Cmd.run (oneA arr) s).1 := m4.mono (fun y h => by
    rcases h with h | h | h; exact ZC_sub y h; all_goals (subst h; unfold ZAll; omega))
  refine ⟨env_step hs harr ?_ ?_ m2, hz, ArK.mono (D := fun a => a = arr) m3 ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne; exact m3 k hne
  · intro a ha; subst ha; exact trk_range _ harr

theorem env_powA (arr : ℕ) (harr : arr ∈ trk) (s : St) (W : ℕ) (v : ℕ → ℕ) (hs : Env s W v) (hW : 1 ≤ W) :
    Env (Cmd.run (powA arr) s).1 W (Function.update v arr (2 ^ (W - 1))) ∧ ScKeep ZAll s (Cmd.run (powA arr) s).1 ∧ ArK AR s (Cmd.run (powA arr) s).1 ∧
    (Cmd.run (powA arr) s).2 ≤ 5 * W + 10 := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := powA_run arr s W hs.1 hW
  have hz : ScKeep ZAll s (Cmd.run (powA arr) s).1 := m4.mono (fun y h => by
    rcases h with h | h | h; exact ZC_sub y h; all_goals (subst h; unfold ZAll; omega))
  refine ⟨env_step hs harr ?_ ?_ m2, hz, ArK.mono (D := fun a => a = arr) m3 ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne; exact m3 k hne
  · intro a ha; subst ha; exact trk_range _ harr

theorem env_constA (arr : ℕ) (l : List ℕ) (harr : arr ∈ trk) (hnd : l.Nodup) (s : St) (W : ℕ) (v : ℕ → ℕ) (hs : Env s W v)
    (hb : ∀ i ∈ l, 1 ≤ i ∧ i ≤ W) :
    Env (Cmd.run (constA arr l) s).1 W (Function.update v arr (l.map (fun i => 2 ^ (i - 1))).sum) ∧
    ScKeep ZAll s (Cmd.run (constA arr l) s).1 ∧ ArK AR s (Cmd.run (constA arr l) s).1 ∧ (Cmd.run (constA arr l) s).2 ≤ 5 * W + 4 * l.length + 10 := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := constA_run arr l hnd s W hs.1 hb
  have hz : ScKeep ZAll s (Cmd.run (constA arr l) s).1 := m4.mono (fun y h => by
    rcases h with h | h | h; exact ZC_sub y h; all_goals (subst h; unfold ZAll; omega))
  refine ⟨env_step hs harr m2 ?_ m1, hz, ArK.mono (D := fun a => a = arr) m3 ?_, m5⟩
  · intro k hk hne; exact m3 k hne
  · intro a ha; subst ha; exact trk_range _ harr

/-- the flag `[V B ≤ V A]` (tmp clobbered, untracked) -/
theorem env_geC (tmp A B : ℕ) (h1 : tmp ≠ A) (h2 : tmp ≠ B) (ht : tmp ∈ scr) (hA : A ∈ trk) (hB : B ∈ trk) (s : St) (W : ℕ)
    (v : ℕ → ℕ) (hs : Env s W v) :
    Env (Cmd.run (geC tmp A B) s).1 W v ∧ (Cmd.run (geC tmp A B) s).1.sc 722 = (if v B ≤ v A then 1 else 0) ∧
    ScKeep ZAll s (Cmd.run (geC tmp A B) s).1 ∧ ArK AR s (Cmd.run (geC tmp A B) s).1 ∧ (Cmd.run (geC tmp A B) s).2 ≤ 40 * W + 20 := by
  obtain ⟨m1, m2, m3, m4⟩ := geC_run tmp A B h1 h2 s W hs.1
  have hz : ScKeep ZAll s (Cmd.run (geC tmp A B) s).1 := m3.mono ZB_sub
  refine ⟨env_keep hs ?_ ?_, ?_, hz, m2.mono ?_, m4⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk; apply m2 k; intro h; subst h; exact scr_not_trk _ ht hk
  · rw [m1, hs.2 A hA, hs.2 B hB]
  · intro a ha; subst ha; exact scr_range _ ht

theorem env_rootC (m C T1 T2 Pn p tA tB nb : ℕ) (hnd : List.Nodup [C, T1, T2, Pn, p, tA, tB]) (hC : C ∈ trk) (hPn : Pn ∈ trk)
    (hp : p ∈ trk) (h1 : T1 ∈ scr) (h2 : T2 ∈ scr) (h3 : tA ∈ scr) (h4 : tB ∈ scr) (s : St) (W : ℕ) (v : ℕ → ℕ)
    (hs : Env s W v) (h752 : s.sc 752 = nb) (hm : 1 ≤ m) (hpv : 0 < v p) (hb : v p ≤ (2 ^ nb) ^ m) (hnb : nb ≤ W)
    (hP : (2 ^ nb) ^ m ≤ v Pn) (h2P : 2 * v Pn ≤ 2 ^ W) :
    Env (Cmd.run (rootC m C T1 T2 Pn p tA tB) s).1 W (Function.update v C (sInf {B | v p ≤ B ^ m} - 1)) ∧
    ScKeep ZAll s (Cmd.run (rootC m C T1 T2 Pn p tA tB) s).1 ∧ ArK AR s (Cmd.run (rootC m C T1 T2 Pn p tA tB) s).1 ∧
    (Cmd.run (rootC m C T1 T2 Pn p tA tB) s).2 ≤ W * (400 * m * W * W + 400 * m * W + 100 * m + 101) + 5 * W + 20 := by
  have eP := hs.2 p hp
  have eN := hs.2 Pn hPn
  obtain ⟨m1, m2, m3, m4, m5⟩ := rootC_run m C T1 T2 Pn p tA tB hnd s W nb hm (by rw [eP]; exact hpv) (by rw [eP]; exact hb) hnb
    (by rw [eN]; exact hP) (by rw [eN]; exact h2P) hs.1 h752
  rw [eP] at m2
  have hz : ScKeep ZAll s (Cmd.run (rootC m C T1 T2 Pn p tA tB) s).1 := m4.mono (fun y h => ZR_sub y h)
  refine ⟨env_step hs hC ?_ ?_ ?_, hz, m3.mono ?_, m5⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne
    apply m3 k
    intro h; rcases h with h | h | h | h | h
    · exact hne h
    · subst h; exact scr_not_trk _ h1 hk
    · subst h; exact scr_not_trk _ h2 hk
    · subst h; exact scr_not_trk _ h3 hk
    · subst h; exact scr_not_trk _ h4 hk
  · omega
  · intro a ha; rcases ha with h | h | h | h | h
    · subst h; exact trk_range _ hC
    · subst h; exact scr_range _ h1
    · subst h; exact scr_range _ h2
    · subst h; exact scr_range _ h3
    · subst h; exact scr_range _ h4

theorem env_add (dst src : ℕ) (hds : dst ≠ src) (hd : dst ∈ trk) (hsrc : src ∈ trk) (s : St) (W : ℕ) (v : ℕ → ℕ) (hs : Env s W v)
    (hlt : v dst + v src < 2 ^ W) :
    Env (Cmd.run (addC false dst src) s).1 W (Function.update v dst (v dst + v src)) ∧
    ScKeep ZAll s (Cmd.run (addC false dst src) s).1 ∧ ArK AR s (Cmd.run (addC false dst src) s).1 ∧ (Cmd.run (addC false dst src) s).2 ≤ 25 * W + 10 := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := add_run dst src hds s W hs.1
  rw [hs.2 dst hd, hs.2 src hsrc] at m2
  have hz : ScKeep ZAll s (Cmd.run (addC false dst src) s).1 := m5.mono ZA_sub
  have hc : (Cmd.run (addC false dst src) s).1.sc 722 = 0 := by
    by_contra hne
    have : (Cmd.run (addC false dst src) s).1.sc 722 = 1 := by omega
    rw [this] at m2; omega
  rw [hc] at m2
  refine ⟨env_step hs hd ?_ ?_ ?_, hz, ArK.mono (D := fun a => a = dst) m4 ?_, m6⟩
  · rw [hz 710 not_ZAll_710]; exact hs.1
  · intro k hk hne; exact m4 k hne
  · simpa using m2
  · intro a ha; subst ha; exact trk_range _ hd

end ECDLP.L76
