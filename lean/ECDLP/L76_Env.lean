import ECDLP.L76_Const
import ECDLP.L76_Parse

/-!
# L76 / Env: bookkeeping of the values of the named work arrays
`Env s W v`: scalar 710 is `W` and the tracked arrays `trk` hold the numbers `v k` (width `W`).  Each library routine gets an `env_*` lemma:
the new environment is `Function.update v dst value`.  Scratch arrays (`45 46 48 49`) are not tracked.  All scratch scalars lie in `ZAll = 711..769` (the flags live in 770..775).
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- the tracked arrays: raw numbers 30-34, reduced numbers 21-24, constants 40, 41, root 47, work 50-59, copy 60, constants 61, 62 -/
def trk : List ℕ := [21, 22, 23, 24, 30, 31, 32, 33, 34, 40, 41, 47, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]

/-- the scratch arrays -/
def scr : List ℕ := [45, 46, 48, 49]

theorem scr_not_trk : ∀ k ∈ scr, k ∉ trk := by decide
theorem trk_range : ∀ k ∈ trk, 20 ≤ k ∧ k ≤ 62 := by decide
theorem scr_range : ∀ k ∈ scr, 20 ≤ k ∧ k ≤ 62 := by decide

/-- arrays `20..62` -/
def AR (a : ℕ) : Prop := 20 ≤ a ∧ a ≤ 62

def Env (s : St) (W : ℕ) (v : ℕ → ℕ) : Prop := s.sc 710 = W ∧ ∀ k ∈ trk, V (s.ar k) W = v k

def ZAll (y : ℕ) : Prop := 711 ≤ y ∧ y ≤ 769

theorem ZA_sub : ∀ y, ZA y → ZAll y := fun y h => by unfold ZA at h; unfold ZAll; omega
theorem ZC_sub : ∀ y, ZC y → ZAll y := fun y h => by unfold ZC at h; unfold ZAll; omega
theorem ZB_sub : ∀ y, ZB y → ZAll y := fun y h => by
  rcases h with h | h; exact ZA_sub y h; exact ZC_sub y h
theorem ZM_sub : ∀ y, ZM y → ZAll y := fun y h => by
  rcases h with h | h; exact ZB_sub y h; unfold ZAll; omega
theorem ZP_sub : ∀ y, ZP y → ZAll y := fun y h => by
  rcases h with h | h; exact ZM_sub y h; exact ZC_sub y h
theorem ZK_sub : ∀ y, ZK y → ZAll y := fun y h => by
  rcases h with h | h | h; exact ZC_sub y h; all_goals (subst h; unfold ZAll; omega)
theorem ZR_sub : ∀ y, ZR y → ZAll y := fun y h => by
  rcases h with h | h; exact ZP_sub y h; unfold ZAll; omega
theorem ZPa_sub : ∀ y, ZPa y → ZAll y := fun y h => by
  rcases h with h | h; exact ZC_sub y h; unfold ZAll; omega

theorem not_ZAll_710 : ¬ ZAll 710 := by unfold ZAll; omega

theorem env_step {s t : St} {W : ℕ} {v : ℕ → ℕ} {k0 x : ℕ} (hs : Env s W v) (hk0 : k0 ∈ trk) (h710 : t.sc 710 = W)
    (hD : ∀ k ∈ trk, k ≠ k0 → t.ar k = s.ar k) (hV : V (t.ar k0) W = x) : Env t W (Function.update v k0 x) := by
  refine ⟨h710, fun k hk => ?_⟩
  by_cases h : k = k0
  · subst h; simpa using hV
  · rw [Function.update_of_ne h, ← hs.2 k hk, hD k hk h]

theorem env_keep {s t : St} {W : ℕ} {v : ℕ → ℕ} (hs : Env s W v) (h710 : t.sc 710 = W)
    (hD : ∀ k ∈ trk, t.ar k = s.ar k) : Env t W v :=
  ⟨h710, fun k hk => by rw [hD k hk]; exact hs.2 k hk⟩

/-- the scalars that the library never touches and that we track: driver scalars `0, 2` and the flags `770..772` -/
def trs : List ℕ := [0, 2, 770, 771, 772]

def ScEnv (s : St) (c : ℕ → ℕ) : Prop := ∀ y ∈ trs, s.sc y = c y

theorem scenv_keep {s t : St} {c : ℕ → ℕ} (h : ScEnv s c) (hz : ScKeep ZAll s t) : ScEnv t c := by
  intro y hy
  rw [hz y (by intro hZ; unfold ZAll at hZ; simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hy; omega)]
  exact h y hy

theorem env_setSc {s : St} {W : ℕ} {v : ℕ → ℕ} (hs : Env s W v) (y n : ℕ) (hy : y ≠ 710) : Env (s.setSc y n) W v :=
  ⟨by simp only [St.setSc_sc]; rw [Function.update_of_ne (Ne.symm hy)]; exact hs.1, fun k hk => hs.2 k hk⟩

theorem scenv_set {s : St} {c : ℕ → ℕ} (h : ScEnv s c) {y : ℕ} (hy : y ∈ trs) (n : ℕ) :
    ScEnv (s.setSc y n) (Function.update c y n) := by
  intro z hz
  by_cases hzy : z = y
  · subst hzy; simp
  · simp only [St.setSc_sc, Function.update_of_ne hzy]; exact h z hz

theorem scenv_setOut {s : St} {c : ℕ → ℕ} (h : ScEnv s c) {y : ℕ} (hy : y ∉ trs) (n : ℕ) : ScEnv (s.setSc y n) c := by
  intro z hz
  have hzy : z ≠ y := fun e => hy (e ▸ hz)
  simp only [St.setSc_sc, Function.update_of_ne hzy]; exact h z hz

/-- scalars the whole input layer may write: the library's `711..769`, the root's bound `752`, the flags `770..772` -/
def ZAll2 (y : ℕ) : Prop := ZAll y ∨ y = 752 ∨ y = 770 ∨ y = 771 ∨ y = 772

theorem sck_step {Z : ℕ → Prop} {s t : St} (h : ScKeep Z s t) (hZ : ∀ y, Z y → ZAll2 y) : ScKeep ZAll2 s t :=
  h.mono hZ

theorem sck_comp {s t u : St} (h1 : ScKeep ZAll2 s t) (h2 : ScKeep ZAll2 t u) : ScKeep ZAll2 s u :=
  (h1.trans h2).mono (fun y h => by rcases h with h | h <;> exact h)

theorem ark_AR_trans {s t u : St} (h1 : ArK AR s t) (h2 : ArK AR t u) : ArK AR s u :=
  (h1.trans h2).mono (fun y h => by rcases h with h | h <;> exact h)

theorem eq_of_zmod {p X Y : ℕ} (h : (X : ZMod p) = (Y : ZMod p)) : X % p = Y % p :=
  (ZMod.natCast_eq_natCast_iff' X Y p).1 h

end ECDLP.L76
