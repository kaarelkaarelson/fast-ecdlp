import ECDLP.L76_Env2

/-!
# L76 / Compute: reductions, `2p²`, the root `X`, and the curve tests, on the work arrays (composed from the library)
-/
namespace ECDLP.L76
open Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib

def computeC (m : ℕ) : Cmd :=
  (.seq (oneA 40) (.seq (powA 41) (.seq (mulMod 21 40 31 30 45 46) (.seq (mulMod 22 40 32 30 45 46) (.seq (mulMod 23 40 33 30 45 46) (.seq (mulMod 24 40 34 30 45 46) (.seq (copyA 60 30) (.seq (mulMod 56 30 60 41 45 46) (.seq (dblMod 56 41 45 46) (.seq (.copy 752 0) (.seq (rootC m 47 48 49 41 30 45 46) (.seq (addC false 47 40) (.seq (copyA 60 21) (.seq (mulMod 50 21 60 30 45 46) (.seq (mulMod 51 50 21 30 45 46) (.seq (constA 61 [3]) (.seq (mulMod 52 51 61 30 45 46) (.seq (copyA 60 22) (.seq (mulMod 53 22 60 30 45 46) (.seq (constA 62 [1, 2, 4, 5]) (.seq (mulMod 54 53 62 30 45 46) (.seq (addMod 52 54 30 45) (.seq (geC 45 52 40) (.seq (.copy 770 722) (.seq (copyA 60 24) (.seq (mulMod 55 24 60 30 45 46) (.seq (copyA 60 23) (.seq (mulMod 57 23 60 30 45 46) (.seq (mulMod 58 57 23 30 45 46) (.seq (mulMod 59 21 23 30 45 46) (.seq (addMod 58 59 30 45) (.seq (addMod 58 22 30 45) (.seq (geC 45 55 58) (.seq (.copy 771 722) (.seq (geC 45 58 55) (.copy 772 722))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem compute_run (m : ℕ) (hm : 1 ≤ m) (s : St) (W N p a b xR yR : ℕ) (c : ℕ → ℕ) (hsc : ScEnv s c) (hc0 : c 0 = N)
    (hW : s.sc 710 = W) (hW1 : 1 ≤ W) (hp2 : 2 ≤ p) (hNW : N ≤ W) (hpm : p ≤ (2 ^ N) ^ m) (hmN : (2 ^ N) ^ m ≤ 2 ^ (W - 1))
    (h2pp : 2 * (p * p) < 2 ^ (W - 1))
    (hv30 : V (s.ar 30) W = p) (hv31 : V (s.ar 31) W = a) (hv32 : V (s.ar 32) W = b) (hv33 : V (s.ar 33) W = xR)
    (hv34 : V (s.ar 34) W = yR) (hW5 : 5 ≤ W) :
    ∀ r : St × ℕ, r = Cmd.run (computeC m) s →
    V (r.1.ar 21) W = a % p ∧ V (r.1.ar 22) W = b % p ∧ V (r.1.ar 23) W = xR % p ∧ V (r.1.ar 24) W = yR % p ∧
    V (r.1.ar 47) W = sInf {B | p ≤ B ^ m} ∧ V (r.1.ar 56) W = 2 * (p * p) ∧ V (r.1.ar 30) W = p ∧
    r.1.sc 770 = (if 1 ≤ (4 * a ^ 3 + 27 * b ^ 2) % p then 1 else 0) ∧
    r.1.sc 771 = (if (xR ^ 3 + a * xR + b) % p ≤ (yR * yR) % p then 1 else 0) ∧
    r.1.sc 772 = (if (yR * yR) % p ≤ (xR ^ 3 + a * xR + b) % p then 1 else 0) ∧
    r.1.sc 710 = W ∧ r.1.sc 0 = c 0 ∧ r.1.sc 2 = c 2 ∧ ArK AR s r.1 ∧ ScKeep ZAll2 s r.1 ∧
    r.2 ≤ 400 * m * W * W * W + 12000 * m * W * W + 3000 * m * W + 2000 := by
  intro r hr
  have hp0 : 0 < p := by omega
  have hpos : 0 < 2 ^ (W - 1) := by positivity
  have hpow : 2 ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  have hpp : p ≤ p * p := Nat.le_mul_self p
  have hm0 : 1 ≤ sInf {B | p ≤ B ^ m} := by
    have hne : ({B | p ≤ B ^ m} : Set ℕ).Nonempty := ⟨p, by show p ≤ p ^ m; exact Nat.le_self_pow (by omega) p⟩
    have hmem := Nat.sInf_mem hne
    by_contra h0; have : sInf {B | p ≤ B ^ m} = 0 := by omega
    rw [this] at hmem; simp [zero_pow (by omega : m ≠ 0)] at hmem; omega
  have hmle : sInf {B | p ≤ B ^ m} ≤ p := Nat.sInf_le (show p ∈ {B | p ≤ B ^ m} from Nat.le_self_pow (by omega) p)
  obtain ⟨v0, hv0def⟩ : ∃ v0 : ℕ → ℕ, v0 = fun k => V (s.ar k) W := ⟨_, rfl⟩
  have e0 : Env s W v0 := ⟨hW, fun k _ => by rw [hv0def]⟩
  have hv0_30 : v0 30 = p := by rw [hv0def]; exact hv30
  have hv0_31 : v0 31 = a := by rw [hv0def]; exact hv31
  have hv0_32 : v0 32 = b := by rw [hv0def]; exact hv32
  have hv0_33 : v0 33 = xR := by rw [hv0def]; exact hv33
  have hv0_34 : v0 34 = yR := by rw [hv0def]; exact hv34
  have se0 : ScEnv s c := hsc
  obtain ⟨e1, z1, a1, k1⟩ := env_oneA 40 (by decide) s W v0 e0 hW1
  generalize hr1 : Cmd.run (oneA 40) s = r1 at e1 z1 a1 k1
  have se1 : ScEnv r1.1 (c) := scenv_keep se0 z1
  generalize hu1 : Function.update v0 40 1 = v1 at e1
  have hv1_30 : v1 30 = p := by rw [← hu1, Function.update_of_ne (by decide)]; exact hv0_30
  have hv1_31 : v1 31 = a := by rw [← hu1, Function.update_of_ne (by decide)]; exact hv0_31
  have hv1_32 : v1 32 = b := by rw [← hu1, Function.update_of_ne (by decide)]; exact hv0_32
  have hv1_33 : v1 33 = xR := by rw [← hu1, Function.update_of_ne (by decide)]; exact hv0_33
  have hv1_34 : v1 34 = yR := by rw [← hu1, Function.update_of_ne (by decide)]; exact hv0_34
  have hv1_40 : v1 40 = 1 := by rw [← hu1]; simp [Function.update_self]
  have zz1 : ScKeep ZAll2 s r1.1 := sck_step z1 (fun y h => Or.inl h)
  clear hv0_30 hv0_31 hv0_32 hv0_33 hv0_34 e0 se0 z1
  obtain ⟨e2, z2, a2, k2⟩ := env_powA 41 (by decide) r1.1 W v1 e1 hW1
  generalize hr2 : Cmd.run (powA 41) r1.1 = r2 at e2 z2 a2 k2
  have se2 : ScEnv r2.1 (c) := scenv_keep se1 z2
  generalize hu2 : Function.update v1 41 (2 ^ (W - 1)) = v2 at e2
  have hv2_30 : v2 30 = p := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_30
  have hv2_31 : v2 31 = a := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_31
  have hv2_32 : v2 32 = b := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_32
  have hv2_33 : v2 33 = xR := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_33
  have hv2_34 : v2 34 = yR := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_34
  have hv2_40 : v2 40 = 1 := by rw [← hu2, Function.update_of_ne (by decide)]; exact hv1_40
  have hv2_41 : v2 41 = 2 ^ (W - 1) := by rw [← hu2]; simp [Function.update_self]
  have zz2 : ScKeep ZAll2 r1.1 r2.1 := sck_step z2 (fun y h => Or.inl h)
  clear hu1 hv1_30 hv1_31 hv1_32 hv1_33 hv1_34 hv1_40 e1 se1 z2
  obtain ⟨e3, z3, a3, k3⟩ := env_mulMod 21 40 31 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r2.1 W v2 e2 (by rw [hv2_40, hv2_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv2_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr3 : Cmd.run (mulMod 21 40 31 30 45 46) r2.1 = r3 at e3 z3 a3 k3
  have se3 : ScEnv r3.1 (c) := scenv_keep se2 z3
  generalize hu3 : Function.update v2 21 ((v2 40 * v2 31) % v2 30) = v3 at e3
  have hv3_21 : v3 21 = ((1) * (a)) % (p) := by rw [← hu3]; simp [Function.update_self, hv2_40, hv2_31, hv2_30]
  have hv3_30 : v3 30 = p := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_30
  have hv3_32 : v3 32 = b := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_32
  have hv3_33 : v3 33 = xR := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_33
  have hv3_34 : v3 34 = yR := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_34
  have hv3_40 : v3 40 = 1 := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_40
  have hv3_41 : v3 41 = 2 ^ (W - 1) := by rw [← hu3, Function.update_of_ne (by decide)]; exact hv2_41
  have zz3 : ScKeep ZAll2 r2.1 r3.1 := sck_step z3 (fun y h => Or.inl h)
  clear hu2 hv2_30 hv2_31 hv2_32 hv2_33 hv2_34 hv2_40 hv2_41 e2 se2 z3
  obtain ⟨e4, z4, a4, k4⟩ := env_mulMod 22 40 32 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r3.1 W v3 e3 (by rw [hv3_40, hv3_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv3_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr4 : Cmd.run (mulMod 22 40 32 30 45 46) r3.1 = r4 at e4 z4 a4 k4
  have se4 : ScEnv r4.1 (c) := scenv_keep se3 z4
  generalize hu4 : Function.update v3 22 ((v3 40 * v3 32) % v3 30) = v4 at e4
  have hv4_21 : v4 21 = ((1) * (a)) % (p) := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_21
  have hv4_22 : v4 22 = ((1) * (b)) % (p) := by rw [← hu4]; simp [Function.update_self, hv3_40, hv3_32, hv3_30]
  have hv4_30 : v4 30 = p := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_30
  have hv4_33 : v4 33 = xR := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_33
  have hv4_34 : v4 34 = yR := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_34
  have hv4_40 : v4 40 = 1 := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_40
  have hv4_41 : v4 41 = 2 ^ (W - 1) := by rw [← hu4, Function.update_of_ne (by decide)]; exact hv3_41
  have zz4 : ScKeep ZAll2 r3.1 r4.1 := sck_step z4 (fun y h => Or.inl h)
  clear hu3 hv3_21 hv3_30 hv3_32 hv3_33 hv3_34 hv3_40 hv3_41 e3 se3 z4
  obtain ⟨e5, z5, a5, k5⟩ := env_mulMod 23 40 33 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r4.1 W v4 e4 (by rw [hv4_40, hv4_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv4_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr5 : Cmd.run (mulMod 23 40 33 30 45 46) r4.1 = r5 at e5 z5 a5 k5
  have se5 : ScEnv r5.1 (c) := scenv_keep se4 z5
  generalize hu5 : Function.update v4 23 ((v4 40 * v4 33) % v4 30) = v5 at e5
  have hv5_21 : v5 21 = ((1) * (a)) % (p) := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_21
  have hv5_22 : v5 22 = ((1) * (b)) % (p) := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_22
  have hv5_23 : v5 23 = ((1) * (xR)) % (p) := by rw [← hu5]; simp [Function.update_self, hv4_40, hv4_33, hv4_30]
  have hv5_30 : v5 30 = p := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_30
  have hv5_34 : v5 34 = yR := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_34
  have hv5_40 : v5 40 = 1 := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_40
  have hv5_41 : v5 41 = 2 ^ (W - 1) := by rw [← hu5, Function.update_of_ne (by decide)]; exact hv4_41
  have zz5 : ScKeep ZAll2 r4.1 r5.1 := sck_step z5 (fun y h => Or.inl h)
  clear hu4 hv4_21 hv4_22 hv4_30 hv4_33 hv4_34 hv4_40 hv4_41 e4 se4 z5
  obtain ⟨e6, z6, a6, k6⟩ := env_mulMod 24 40 34 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r5.1 W v5 e5 (by rw [hv5_40, hv5_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv5_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr6 : Cmd.run (mulMod 24 40 34 30 45 46) r5.1 = r6 at e6 z6 a6 k6
  have se6 : ScEnv r6.1 (c) := scenv_keep se5 z6
  generalize hu6 : Function.update v5 24 ((v5 40 * v5 34) % v5 30) = v6 at e6
  have hv6_21 : v6 21 = ((1) * (a)) % (p) := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_21
  have hv6_22 : v6 22 = ((1) * (b)) % (p) := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_22
  have hv6_23 : v6 23 = ((1) * (xR)) % (p) := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_23
  have hv6_24 : v6 24 = ((1) * (yR)) % (p) := by rw [← hu6]; simp [Function.update_self, hv5_40, hv5_34, hv5_30]
  have hv6_30 : v6 30 = p := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_30
  have hv6_40 : v6 40 = 1 := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_40
  have hv6_41 : v6 41 = 2 ^ (W - 1) := by rw [← hu6, Function.update_of_ne (by decide)]; exact hv5_41
  have zz6 : ScKeep ZAll2 r5.1 r6.1 := sck_step z6 (fun y h => Or.inl h)
  clear hu5 hv5_21 hv5_22 hv5_23 hv5_30 hv5_34 hv5_40 hv5_41 e5 se5 z6
  obtain ⟨e7, z7, a7, k7⟩ := env_copy 60 30 (by decide) (by decide) r6.1 W v6 e6 (by decide)
  generalize hr7 : Cmd.run (copyA 60 30) r6.1 = r7 at e7 z7 a7 k7
  have se7 : ScEnv r7.1 (c) := scenv_keep se6 z7
  generalize hu7 : Function.update v6 60 (v6 30) = v7 at e7
  have hv7_21 : v7 21 = ((1) * (a)) % (p) := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_21
  have hv7_22 : v7 22 = ((1) * (b)) % (p) := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_22
  have hv7_23 : v7 23 = ((1) * (xR)) % (p) := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_23
  have hv7_24 : v7 24 = ((1) * (yR)) % (p) := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_24
  have hv7_30 : v7 30 = p := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_30
  have hv7_40 : v7 40 = 1 := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_40
  have hv7_41 : v7 41 = 2 ^ (W - 1) := by rw [← hu7, Function.update_of_ne (by decide)]; exact hv6_41
  have hv7_60 : v7 60 = p := by rw [← hu7]; simp [Function.update_self, hv6_30]
  have zz7 : ScKeep ZAll2 r6.1 r7.1 := sck_step z7 (fun y h => Or.inl h)
  clear hu6 hv6_21 hv6_22 hv6_23 hv6_24 hv6_30 hv6_40 hv6_41 e6 se6 z7
  obtain ⟨e8, z8, a8, k8⟩ := env_mulMod 56 30 60 41 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r7.1 W v7 e7 (by rw [hv7_30, hv7_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv7_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr8 : Cmd.run (mulMod 56 30 60 41 45 46) r7.1 = r8 at e8 z8 a8 k8
  have se8 : ScEnv r8.1 (c) := scenv_keep se7 z8
  generalize hu8 : Function.update v7 56 ((v7 30 * v7 60) % v7 41) = v8 at e8
  have hv8_21 : v8 21 = ((1) * (a)) % (p) := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_21
  have hv8_22 : v8 22 = ((1) * (b)) % (p) := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_22
  have hv8_23 : v8 23 = ((1) * (xR)) % (p) := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_23
  have hv8_24 : v8 24 = ((1) * (yR)) % (p) := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_24
  have hv8_30 : v8 30 = p := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_30
  have hv8_40 : v8 40 = 1 := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_40
  have hv8_41 : v8 41 = 2 ^ (W - 1) := by rw [← hu8, Function.update_of_ne (by decide)]; exact hv7_41
  have hv8_56 : v8 56 = ((p) * (p)) % (2 ^ (W - 1)) := by rw [← hu8]; simp [Function.update_self, hv7_30, hv7_60, hv7_41]
  have zz8 : ScKeep ZAll2 r7.1 r8.1 := sck_step z8 (fun y h => Or.inl h)
  clear hu7 hv7_21 hv7_22 hv7_23 hv7_24 hv7_30 hv7_40 hv7_41 hv7_60 e7 se7 z8
  obtain ⟨e9, z9, a9, k9⟩ := env_dblMod 56 41 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r8.1 W v8 e8 (by rw [hv8_56, hv8_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv8_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr9 : Cmd.run (dblMod 56 41 45 46) r8.1 = r9 at e9 z9 a9 k9
  have se9 : ScEnv r9.1 (c) := scenv_keep se8 z9
  generalize hu9 : Function.update v8 56 ((2 * v8 56) % v8 41) = v9 at e9
  have hv9_21 : v9 21 = ((1) * (a)) % (p) := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_21
  have hv9_22 : v9 22 = ((1) * (b)) % (p) := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_22
  have hv9_23 : v9 23 = ((1) * (xR)) % (p) := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_23
  have hv9_24 : v9 24 = ((1) * (yR)) % (p) := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_24
  have hv9_30 : v9 30 = p := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_30
  have hv9_40 : v9 40 = 1 := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_40
  have hv9_41 : v9 41 = 2 ^ (W - 1) := by rw [← hu9, Function.update_of_ne (by decide)]; exact hv8_41
  have hv9_56 : v9 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu9]; simp [Function.update_self, hv8_56, hv8_41]
  have zz9 : ScKeep ZAll2 r8.1 r9.1 := sck_step z9 (fun y h => Or.inl h)
  clear hu8 hv8_21 hv8_22 hv8_23 hv8_24 hv8_30 hv8_40 hv8_41 hv8_56 e8 se8 z9
  generalize hr10 : Cmd.run (.copy 752 0) r9.1 = r10
  have g10 : r10.1 = r9.1.setSc 752 (r9.1.sc 0) := by rw [← hr10]; rfl
  have e10 := env_setSc e9 752 (r9.1.sc 0) (by norm_num)
  rw [← g10] at e10
  have k10 : r10.2 = 1 := by rw [← hr10]; rfl
  have a10 : ArK AR r9.1 r10.1 := fun a _ => by rw [g10]; rfl
  have z10 : ScKeep (fun y => y = 752) r9.1 r10.1 := by rw [g10]; intro y hy; simp only [St.setSc_sc]; exact Function.update_of_ne hy _ _
  have h752 : r10.1.sc 752 = N := by rw [g10]; simp only [St.setSc_sc, Function.update_self]; exact (se9 0 (by decide)).trans hc0
  have se10 : ScEnv r10.1 c := by rw [g10]; exact scenv_setOut se9 (by decide) _
  obtain ⟨v10, hvv10⟩ : ∃ w, w = v9 := ⟨_, rfl⟩
  rw [← hvv10] at e10
  have hv10_21 : v10 21 = ((1) * (a)) % (p) := by rw [hvv10]; exact hv9_21
  have hv10_22 : v10 22 = ((1) * (b)) % (p) := by rw [hvv10]; exact hv9_22
  have hv10_23 : v10 23 = ((1) * (xR)) % (p) := by rw [hvv10]; exact hv9_23
  have hv10_24 : v10 24 = ((1) * (yR)) % (p) := by rw [hvv10]; exact hv9_24
  have hv10_30 : v10 30 = p := by rw [hvv10]; exact hv9_30
  have hv10_40 : v10 40 = 1 := by rw [hvv10]; exact hv9_40
  have hv10_41 : v10 41 = 2 ^ (W - 1) := by rw [hvv10]; exact hv9_41
  have hv10_56 : v10 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv10]; exact hv9_56
  have zz10 : ScKeep ZAll2 r9.1 r10.1 := sck_step z10 (by intro y h; subst h; simp [ZAll2, ZAll])
  clear hu9 hv9_21 hv9_22 hv9_23 hv9_24 hv9_30 hv9_40 hv9_41 hv9_56 e9 se9 z10
  obtain ⟨e11, z11, a11, k11⟩ := env_rootC m 47 48 49 41 30 45 46 N (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r10.1 W v10 e10 h752 hm (by rw [hv10_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv10_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) hNW (by rw [hv10_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv10_41]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr11 : Cmd.run (rootC m 47 48 49 41 30 45 46) r10.1 = r11 at e11 z11 a11 k11
  have se11 : ScEnv r11.1 (c) := scenv_keep se10 z11
  generalize hu11 : Function.update v10 47 (sInf {B | v10 30 ≤ B ^ m} - 1) = v11 at e11
  have hv11_21 : v11 21 = ((1) * (a)) % (p) := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_21
  have hv11_22 : v11 22 = ((1) * (b)) % (p) := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_22
  have hv11_23 : v11 23 = ((1) * (xR)) % (p) := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_23
  have hv11_24 : v11 24 = ((1) * (yR)) % (p) := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_24
  have hv11_30 : v11 30 = p := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_30
  have hv11_40 : v11 40 = 1 := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_40
  have hv11_47 : v11 47 = sInf {B | (p) ≤ B ^ m} - 1 := by rw [← hu11]; simp [Function.update_self, hv10_30, hv10_41]
  have hv11_56 : v11 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu11, Function.update_of_ne (by decide)]; exact hv10_56
  have zz11 : ScKeep ZAll2 r10.1 r11.1 := sck_step z11 (fun y h => Or.inl h)
  clear hvv10 hv10_21 hv10_22 hv10_23 hv10_24 hv10_30 hv10_40 hv10_41 hv10_56 e10 se10 z11
  obtain ⟨e12, z12, a12, k12⟩ := env_add 47 40 (by decide) (by decide) (by decide) r11.1 W v11 e11 (by rw [hv11_47, hv11_40]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr12 : Cmd.run (addC false 47 40) r11.1 = r12 at e12 z12 a12 k12
  have se12 : ScEnv r12.1 (c) := scenv_keep se11 z12
  generalize hu12 : Function.update v11 47 (v11 47 + v11 40) = v12 at e12
  have hv12_21 : v12 21 = ((1) * (a)) % (p) := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_21
  have hv12_22 : v12 22 = ((1) * (b)) % (p) := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_22
  have hv12_23 : v12 23 = ((1) * (xR)) % (p) := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_23
  have hv12_24 : v12 24 = ((1) * (yR)) % (p) := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_24
  have hv12_30 : v12 30 = p := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_30
  have hv12_40 : v12 40 = 1 := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_40
  have hv12_47 : v12 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu12]; simp [Function.update_self, hv11_47, hv11_40]
  have hv12_56 : v12 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu12, Function.update_of_ne (by decide)]; exact hv11_56
  have zz12 : ScKeep ZAll2 r11.1 r12.1 := sck_step z12 (fun y h => Or.inl h)
  clear hu11 hv11_21 hv11_22 hv11_23 hv11_24 hv11_30 hv11_40 hv11_47 hv11_56 e11 se11 z12
  obtain ⟨e13, z13, a13, k13⟩ := env_copy 60 21 (by decide) (by decide) r12.1 W v12 e12 (by decide)
  generalize hr13 : Cmd.run (copyA 60 21) r12.1 = r13 at e13 z13 a13 k13
  have se13 : ScEnv r13.1 (c) := scenv_keep se12 z13
  generalize hu13 : Function.update v12 60 (v12 21) = v13 at e13
  have hv13_21 : v13 21 = ((1) * (a)) % (p) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_21
  have hv13_22 : v13 22 = ((1) * (b)) % (p) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_22
  have hv13_23 : v13 23 = ((1) * (xR)) % (p) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_23
  have hv13_24 : v13 24 = ((1) * (yR)) % (p) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_24
  have hv13_30 : v13 30 = p := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_30
  have hv13_40 : v13 40 = 1 := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_40
  have hv13_47 : v13 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_47
  have hv13_56 : v13 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu13, Function.update_of_ne (by decide)]; exact hv12_56
  have hv13_60 : v13 60 = ((1) * (a)) % (p) := by rw [← hu13]; simp [Function.update_self, hv12_21]
  have zz13 : ScKeep ZAll2 r12.1 r13.1 := sck_step z13 (fun y h => Or.inl h)
  clear hu12 hv12_21 hv12_22 hv12_23 hv12_24 hv12_30 hv12_40 hv12_47 hv12_56 e12 se12 z13
  obtain ⟨e14, z14, a14, k14⟩ := env_mulMod 50 21 60 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r13.1 W v13 e13 (by rw [hv13_21, hv13_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv13_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr14 : Cmd.run (mulMod 50 21 60 30 45 46) r13.1 = r14 at e14 z14 a14 k14
  have se14 : ScEnv r14.1 (c) := scenv_keep se13 z14
  generalize hu14 : Function.update v13 50 ((v13 21 * v13 60) % v13 30) = v14 at e14
  have hv14_21 : v14 21 = ((1) * (a)) % (p) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_21
  have hv14_22 : v14 22 = ((1) * (b)) % (p) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_22
  have hv14_23 : v14 23 = ((1) * (xR)) % (p) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_23
  have hv14_24 : v14 24 = ((1) * (yR)) % (p) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_24
  have hv14_30 : v14 30 = p := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_30
  have hv14_40 : v14 40 = 1 := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_40
  have hv14_47 : v14 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_47
  have hv14_50 : v14 50 = ((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p) := by rw [← hu14]; simp [Function.update_self, hv13_21, hv13_60, hv13_30]
  have hv14_56 : v14 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu14, Function.update_of_ne (by decide)]; exact hv13_56
  have zz14 : ScKeep ZAll2 r13.1 r14.1 := sck_step z14 (fun y h => Or.inl h)
  clear hu13 hv13_21 hv13_22 hv13_23 hv13_24 hv13_30 hv13_40 hv13_47 hv13_56 hv13_60 e13 se13 z14
  obtain ⟨e15, z15, a15, k15⟩ := env_mulMod 51 50 21 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r14.1 W v14 e14 (by rw [hv14_50, hv14_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv14_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr15 : Cmd.run (mulMod 51 50 21 30 45 46) r14.1 = r15 at e15 z15 a15 k15
  have se15 : ScEnv r15.1 (c) := scenv_keep se14 z15
  generalize hu15 : Function.update v14 51 ((v14 50 * v14 21) % v14 30) = v15 at e15
  have hv15_21 : v15 21 = ((1) * (a)) % (p) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_21
  have hv15_22 : v15 22 = ((1) * (b)) % (p) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_22
  have hv15_23 : v15 23 = ((1) * (xR)) % (p) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_23
  have hv15_24 : v15 24 = ((1) * (yR)) % (p) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_24
  have hv15_30 : v15 30 = p := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_30
  have hv15_40 : v15 40 = 1 := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_40
  have hv15_47 : v15 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_47
  have hv15_51 : v15 51 = ((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p) := by rw [← hu15]; simp [Function.update_self, hv14_50, hv14_21, hv14_30]
  have hv15_56 : v15 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu15, Function.update_of_ne (by decide)]; exact hv14_56
  have zz15 : ScKeep ZAll2 r14.1 r15.1 := sck_step z15 (fun y h => Or.inl h)
  clear hu14 hv14_21 hv14_22 hv14_23 hv14_24 hv14_30 hv14_40 hv14_47 hv14_50 hv14_56 e14 se14 z15
  obtain ⟨e16, z16, a16, k16⟩ := env_constA 61 [3] (by decide) (by decide) r15.1 W v15 e15 (by intro i hi; simp at hi; omega)
  generalize hr16 : Cmd.run (constA 61 [3]) r15.1 = r16 at e16 z16 a16 k16
  have se16 : ScEnv r16.1 (c) := scenv_keep se15 z16
  generalize hu16 : Function.update v15 61 ([3].map (fun i => 2 ^ (i - 1))).sum = v16 at e16
  have hv16_21 : v16 21 = ((1) * (a)) % (p) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_21
  have hv16_22 : v16 22 = ((1) * (b)) % (p) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_22
  have hv16_23 : v16 23 = ((1) * (xR)) % (p) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_23
  have hv16_24 : v16 24 = ((1) * (yR)) % (p) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_24
  have hv16_30 : v16 30 = p := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_30
  have hv16_40 : v16 40 = 1 := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_40
  have hv16_47 : v16 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_47
  have hv16_51 : v16 51 = ((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_51
  have hv16_56 : v16 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu16, Function.update_of_ne (by decide)]; exact hv15_56
  have hv16_61 : v16 61 = 4 := by rw [← hu16]; simp [Function.update_self]
  have zz16 : ScKeep ZAll2 r15.1 r16.1 := sck_step z16 (fun y h => Or.inl h)
  clear hu15 hv15_21 hv15_22 hv15_23 hv15_24 hv15_30 hv15_40 hv15_47 hv15_51 hv15_56 e15 se15 z16
  obtain ⟨e17, z17, a17, k17⟩ := env_mulMod 52 51 61 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r16.1 W v16 e16 (by rw [hv16_51, hv16_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv16_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr17 : Cmd.run (mulMod 52 51 61 30 45 46) r16.1 = r17 at e17 z17 a17 k17
  have se17 : ScEnv r17.1 (c) := scenv_keep se16 z17
  generalize hu17 : Function.update v16 52 ((v16 51 * v16 61) % v16 30) = v17 at e17
  have hv17_21 : v17 21 = ((1) * (a)) % (p) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_21
  have hv17_22 : v17 22 = ((1) * (b)) % (p) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_22
  have hv17_23 : v17 23 = ((1) * (xR)) % (p) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_23
  have hv17_24 : v17 24 = ((1) * (yR)) % (p) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_24
  have hv17_30 : v17 30 = p := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_30
  have hv17_40 : v17 40 = 1 := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_40
  have hv17_47 : v17 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_47
  have hv17_52 : v17 52 = ((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p) := by rw [← hu17]; simp [Function.update_self, hv16_51, hv16_61, hv16_30]
  have hv17_56 : v17 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu17, Function.update_of_ne (by decide)]; exact hv16_56
  have zz17 : ScKeep ZAll2 r16.1 r17.1 := sck_step z17 (fun y h => Or.inl h)
  clear hu16 hv16_21 hv16_22 hv16_23 hv16_24 hv16_30 hv16_40 hv16_47 hv16_51 hv16_56 hv16_61 e16 se16 z17
  obtain ⟨e18, z18, a18, k18⟩ := env_copy 60 22 (by decide) (by decide) r17.1 W v17 e17 (by decide)
  generalize hr18 : Cmd.run (copyA 60 22) r17.1 = r18 at e18 z18 a18 k18
  have se18 : ScEnv r18.1 (c) := scenv_keep se17 z18
  generalize hu18 : Function.update v17 60 (v17 22) = v18 at e18
  have hv18_21 : v18 21 = ((1) * (a)) % (p) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_21
  have hv18_22 : v18 22 = ((1) * (b)) % (p) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_22
  have hv18_23 : v18 23 = ((1) * (xR)) % (p) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_23
  have hv18_24 : v18 24 = ((1) * (yR)) % (p) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_24
  have hv18_30 : v18 30 = p := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_30
  have hv18_40 : v18 40 = 1 := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_40
  have hv18_47 : v18 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_47
  have hv18_52 : v18 52 = ((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_52
  have hv18_56 : v18 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu18, Function.update_of_ne (by decide)]; exact hv17_56
  have hv18_60 : v18 60 = ((1) * (b)) % (p) := by rw [← hu18]; simp [Function.update_self, hv17_22]
  have zz18 : ScKeep ZAll2 r17.1 r18.1 := sck_step z18 (fun y h => Or.inl h)
  clear hu17 hv17_21 hv17_22 hv17_23 hv17_24 hv17_30 hv17_40 hv17_47 hv17_52 hv17_56 e17 se17 z18
  obtain ⟨e19, z19, a19, k19⟩ := env_mulMod 53 22 60 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r18.1 W v18 e18 (by rw [hv18_22, hv18_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv18_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr19 : Cmd.run (mulMod 53 22 60 30 45 46) r18.1 = r19 at e19 z19 a19 k19
  have se19 : ScEnv r19.1 (c) := scenv_keep se18 z19
  generalize hu19 : Function.update v18 53 ((v18 22 * v18 60) % v18 30) = v19 at e19
  have hv19_21 : v19 21 = ((1) * (a)) % (p) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_21
  have hv19_22 : v19 22 = ((1) * (b)) % (p) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_22
  have hv19_23 : v19 23 = ((1) * (xR)) % (p) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_23
  have hv19_24 : v19 24 = ((1) * (yR)) % (p) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_24
  have hv19_30 : v19 30 = p := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_30
  have hv19_40 : v19 40 = 1 := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_40
  have hv19_47 : v19 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_47
  have hv19_52 : v19 52 = ((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_52
  have hv19_53 : v19 53 = ((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p) := by rw [← hu19]; simp [Function.update_self, hv18_22, hv18_60, hv18_30]
  have hv19_56 : v19 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu19, Function.update_of_ne (by decide)]; exact hv18_56
  have zz19 : ScKeep ZAll2 r18.1 r19.1 := sck_step z19 (fun y h => Or.inl h)
  clear hu18 hv18_21 hv18_22 hv18_23 hv18_24 hv18_30 hv18_40 hv18_47 hv18_52 hv18_56 hv18_60 e18 se18 z19
  obtain ⟨e20, z20, a20, k20⟩ := env_constA 62 [1, 2, 4, 5] (by decide) (by decide) r19.1 W v19 e19 (by intro i hi; simp at hi; omega)
  generalize hr20 : Cmd.run (constA 62 [1, 2, 4, 5]) r19.1 = r20 at e20 z20 a20 k20
  have se20 : ScEnv r20.1 (c) := scenv_keep se19 z20
  generalize hu20 : Function.update v19 62 ([1, 2, 4, 5].map (fun i => 2 ^ (i - 1))).sum = v20 at e20
  have hv20_21 : v20 21 = ((1) * (a)) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_21
  have hv20_22 : v20 22 = ((1) * (b)) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_22
  have hv20_23 : v20 23 = ((1) * (xR)) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_23
  have hv20_24 : v20 24 = ((1) * (yR)) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_24
  have hv20_30 : v20 30 = p := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_30
  have hv20_40 : v20 40 = 1 := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_40
  have hv20_47 : v20 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_47
  have hv20_52 : v20 52 = ((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_52
  have hv20_53 : v20 53 = ((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_53
  have hv20_56 : v20 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu20, Function.update_of_ne (by decide)]; exact hv19_56
  have hv20_62 : v20 62 = 27 := by rw [← hu20]; simp [Function.update_self]
  have zz20 : ScKeep ZAll2 r19.1 r20.1 := sck_step z20 (fun y h => Or.inl h)
  clear hu19 hv19_21 hv19_22 hv19_23 hv19_24 hv19_30 hv19_40 hv19_47 hv19_52 hv19_53 hv19_56 e19 se19 z20
  obtain ⟨e21, z21, a21, k21⟩ := env_mulMod 54 53 62 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r20.1 W v20 e20 (by rw [hv20_53, hv20_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv20_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr21 : Cmd.run (mulMod 54 53 62 30 45 46) r20.1 = r21 at e21 z21 a21 k21
  have se21 : ScEnv r21.1 (c) := scenv_keep se20 z21
  generalize hu21 : Function.update v20 54 ((v20 53 * v20 62) % v20 30) = v21 at e21
  have hv21_21 : v21 21 = ((1) * (a)) % (p) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_21
  have hv21_22 : v21 22 = ((1) * (b)) % (p) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_22
  have hv21_23 : v21 23 = ((1) * (xR)) % (p) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_23
  have hv21_24 : v21 24 = ((1) * (yR)) % (p) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_24
  have hv21_30 : v21 30 = p := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_30
  have hv21_40 : v21 40 = 1 := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_40
  have hv21_47 : v21 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_47
  have hv21_52 : v21 52 = ((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_52
  have hv21_54 : v21 54 = ((((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p)) * (27)) % (p) := by rw [← hu21]; simp [Function.update_self, hv20_53, hv20_62, hv20_30]
  have hv21_56 : v21 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu21, Function.update_of_ne (by decide)]; exact hv20_56
  have zz21 : ScKeep ZAll2 r20.1 r21.1 := sck_step z21 (fun y h => Or.inl h)
  clear hu20 hv20_21 hv20_22 hv20_23 hv20_24 hv20_30 hv20_40 hv20_47 hv20_52 hv20_53 hv20_56 hv20_62 e20 se20 z21
  obtain ⟨e22, z22, a22, k22⟩ := env_addMod 52 54 30 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r21.1 W v21 e21 (by rw [hv21_52, hv21_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv21_54, hv21_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv21_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr22 : Cmd.run (addMod 52 54 30 45) r21.1 = r22 at e22 z22 a22 k22
  have se22 : ScEnv r22.1 (c) := scenv_keep se21 z22
  generalize hu22 : Function.update v21 52 ((v21 52 + v21 54) % v21 30) = v22 at e22
  have hv22_21 : v22 21 = ((1) * (a)) % (p) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_21
  have hv22_22 : v22 22 = ((1) * (b)) % (p) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_22
  have hv22_23 : v22 23 = ((1) * (xR)) % (p) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_23
  have hv22_24 : v22 24 = ((1) * (yR)) % (p) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_24
  have hv22_30 : v22 30 = p := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_30
  have hv22_40 : v22 40 = 1 := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_40
  have hv22_47 : v22 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_47
  have hv22_52 : v22 52 = ((((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p)) + (((((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p)) * (27)) % (p))) % (p) := by rw [← hu22]; simp [Function.update_self, hv21_52, hv21_54, hv21_30]
  have hv22_56 : v22 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu22, Function.update_of_ne (by decide)]; exact hv21_56
  have zz22 : ScKeep ZAll2 r21.1 r22.1 := sck_step z22 (fun y h => Or.inl h)
  clear hu21 hv21_21 hv21_22 hv21_23 hv21_24 hv21_30 hv21_40 hv21_47 hv21_52 hv21_54 hv21_56 e21 se21 z22
  obtain ⟨e23, f23, z23, a23, k23⟩ := env_geC 45 52 40 (by decide) (by decide) (by decide) (by decide) (by decide) r22.1 W v22 e22
  generalize hr23 : Cmd.run (geC 45 52 40) r22.1 = r23 at e23 f23 z23 a23 k23
  have se23 : ScEnv r23.1 (c) := scenv_keep se22 z23
  rw [hv22_52, hv22_40] at f23
  obtain ⟨v23, hvv23⟩ : ∃ w, w = v22 := ⟨_, rfl⟩
  rw [← hvv23] at e23
  have hv23_21 : v23 21 = ((1) * (a)) % (p) := by rw [hvv23]; exact hv22_21
  have hv23_22 : v23 22 = ((1) * (b)) % (p) := by rw [hvv23]; exact hv22_22
  have hv23_23 : v23 23 = ((1) * (xR)) % (p) := by rw [hvv23]; exact hv22_23
  have hv23_24 : v23 24 = ((1) * (yR)) % (p) := by rw [hvv23]; exact hv22_24
  have hv23_30 : v23 30 = p := by rw [hvv23]; exact hv22_30
  have hv23_47 : v23 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv23]; exact hv22_47
  have hv23_56 : v23 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv23]; exact hv22_56
  have zz23 : ScKeep ZAll2 r22.1 r23.1 := sck_step z23 (fun y h => Or.inl h)
  clear hu22 hv22_21 hv22_22 hv22_23 hv22_24 hv22_30 hv22_40 hv22_47 hv22_52 hv22_56 e22 se22 z23
  generalize hr24 : Cmd.run (.copy 770 722) r23.1 = r24
  have g24 : r24.1 = r23.1.setSc 770 (r23.1.sc 722) := by rw [← hr24]; rfl
  have e24 := env_setSc e23 770 (r23.1.sc 722) (by norm_num)
  rw [← g24] at e24
  have k24 : r24.2 = 1 := by rw [← hr24]; rfl
  have a24 : ArK AR r23.1 r24.1 := fun a _ => by rw [g24]; rfl
  have z24 : ScKeep (fun y => y = 770) r23.1 r24.1 := by rw [g24]; intro y hy; simp only [St.setSc_sc]; exact Function.update_of_ne hy _ _
  have se24 : ScEnv r24.1 (Function.update (c) 770 (r23.1.sc 722)) := by rw [g24]; exact scenv_set se23 (by decide) _
  obtain ⟨v24, hvv24⟩ : ∃ w, w = v23 := ⟨_, rfl⟩
  rw [← hvv24] at e24
  have hv24_21 : v24 21 = ((1) * (a)) % (p) := by rw [hvv24]; exact hv23_21
  have hv24_22 : v24 22 = ((1) * (b)) % (p) := by rw [hvv24]; exact hv23_22
  have hv24_23 : v24 23 = ((1) * (xR)) % (p) := by rw [hvv24]; exact hv23_23
  have hv24_24 : v24 24 = ((1) * (yR)) % (p) := by rw [hvv24]; exact hv23_24
  have hv24_30 : v24 30 = p := by rw [hvv24]; exact hv23_30
  have hv24_47 : v24 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv24]; exact hv23_47
  have hv24_56 : v24 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv24]; exact hv23_56
  have zz24 : ScKeep ZAll2 r23.1 r24.1 := sck_step z24 (by intro y h; subst h; simp [ZAll2, ZAll])
  clear hvv23 hv23_21 hv23_22 hv23_23 hv23_24 hv23_30 hv23_47 hv23_56 e23 se23 z24
  obtain ⟨e25, z25, a25, k25⟩ := env_copy 60 24 (by decide) (by decide) r24.1 W v24 e24 (by decide)
  generalize hr25 : Cmd.run (copyA 60 24) r24.1 = r25 at e25 z25 a25 k25
  have se25 : ScEnv r25.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se24 z25
  generalize hu25 : Function.update v24 60 (v24 24) = v25 at e25
  have hv25_21 : v25 21 = ((1) * (a)) % (p) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_21
  have hv25_22 : v25 22 = ((1) * (b)) % (p) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_22
  have hv25_23 : v25 23 = ((1) * (xR)) % (p) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_23
  have hv25_24 : v25 24 = ((1) * (yR)) % (p) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_24
  have hv25_30 : v25 30 = p := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_30
  have hv25_47 : v25 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_47
  have hv25_56 : v25 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu25, Function.update_of_ne (by decide)]; exact hv24_56
  have hv25_60 : v25 60 = ((1) * (yR)) % (p) := by rw [← hu25]; simp [Function.update_self, hv24_24]
  have zz25 : ScKeep ZAll2 r24.1 r25.1 := sck_step z25 (fun y h => Or.inl h)
  clear hvv24 hv24_21 hv24_22 hv24_23 hv24_24 hv24_30 hv24_47 hv24_56 e24 se24 z25
  obtain ⟨e26, z26, a26, k26⟩ := env_mulMod 55 24 60 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r25.1 W v25 e25 (by rw [hv25_24, hv25_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv25_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr26 : Cmd.run (mulMod 55 24 60 30 45 46) r25.1 = r26 at e26 z26 a26 k26
  have se26 : ScEnv r26.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se25 z26
  generalize hu26 : Function.update v25 55 ((v25 24 * v25 60) % v25 30) = v26 at e26
  have hv26_21 : v26 21 = ((1) * (a)) % (p) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_21
  have hv26_22 : v26 22 = ((1) * (b)) % (p) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_22
  have hv26_23 : v26 23 = ((1) * (xR)) % (p) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_23
  have hv26_24 : v26 24 = ((1) * (yR)) % (p) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_24
  have hv26_30 : v26 30 = p := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_30
  have hv26_47 : v26 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_47
  have hv26_55 : v26 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu26]; simp [Function.update_self, hv25_24, hv25_60, hv25_30]
  have hv26_56 : v26 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu26, Function.update_of_ne (by decide)]; exact hv25_56
  have zz26 : ScKeep ZAll2 r25.1 r26.1 := sck_step z26 (fun y h => Or.inl h)
  clear hu25 hv25_21 hv25_22 hv25_23 hv25_24 hv25_30 hv25_47 hv25_56 hv25_60 e25 se25 z26
  obtain ⟨e27, z27, a27, k27⟩ := env_copy 60 23 (by decide) (by decide) r26.1 W v26 e26 (by decide)
  generalize hr27 : Cmd.run (copyA 60 23) r26.1 = r27 at e27 z27 a27 k27
  have se27 : ScEnv r27.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se26 z27
  generalize hu27 : Function.update v26 60 (v26 23) = v27 at e27
  have hv27_21 : v27 21 = ((1) * (a)) % (p) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_21
  have hv27_22 : v27 22 = ((1) * (b)) % (p) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_22
  have hv27_23 : v27 23 = ((1) * (xR)) % (p) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_23
  have hv27_24 : v27 24 = ((1) * (yR)) % (p) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_24
  have hv27_30 : v27 30 = p := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_30
  have hv27_47 : v27 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_47
  have hv27_55 : v27 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_55
  have hv27_56 : v27 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu27, Function.update_of_ne (by decide)]; exact hv26_56
  have hv27_60 : v27 60 = ((1) * (xR)) % (p) := by rw [← hu27]; simp [Function.update_self, hv26_23]
  have zz27 : ScKeep ZAll2 r26.1 r27.1 := sck_step z27 (fun y h => Or.inl h)
  clear hu26 hv26_21 hv26_22 hv26_23 hv26_24 hv26_30 hv26_47 hv26_55 hv26_56 e26 se26 z27
  obtain ⟨e28, z28, a28, k28⟩ := env_mulMod 57 23 60 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r27.1 W v27 e27 (by rw [hv27_23, hv27_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv27_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr28 : Cmd.run (mulMod 57 23 60 30 45 46) r27.1 = r28 at e28 z28 a28 k28
  have se28 : ScEnv r28.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se27 z28
  generalize hu28 : Function.update v27 57 ((v27 23 * v27 60) % v27 30) = v28 at e28
  have hv28_21 : v28 21 = ((1) * (a)) % (p) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_21
  have hv28_22 : v28 22 = ((1) * (b)) % (p) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_22
  have hv28_23 : v28 23 = ((1) * (xR)) % (p) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_23
  have hv28_24 : v28 24 = ((1) * (yR)) % (p) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_24
  have hv28_30 : v28 30 = p := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_30
  have hv28_47 : v28 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_47
  have hv28_55 : v28 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_55
  have hv28_56 : v28 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu28, Function.update_of_ne (by decide)]; exact hv27_56
  have hv28_57 : v28 57 = ((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p) := by rw [← hu28]; simp [Function.update_self, hv27_23, hv27_60, hv27_30]
  have zz28 : ScKeep ZAll2 r27.1 r28.1 := sck_step z28 (fun y h => Or.inl h)
  clear hu27 hv27_21 hv27_22 hv27_23 hv27_24 hv27_30 hv27_47 hv27_55 hv27_56 hv27_60 e27 se27 z28
  obtain ⟨e29, z29, a29, k29⟩ := env_mulMod 58 57 23 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r28.1 W v28 e28 (by rw [hv28_57, hv28_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv28_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr29 : Cmd.run (mulMod 58 57 23 30 45 46) r28.1 = r29 at e29 z29 a29 k29
  have se29 : ScEnv r29.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se28 z29
  generalize hu29 : Function.update v28 58 ((v28 57 * v28 23) % v28 30) = v29 at e29
  have hv29_21 : v29 21 = ((1) * (a)) % (p) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_21
  have hv29_22 : v29 22 = ((1) * (b)) % (p) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_22
  have hv29_23 : v29 23 = ((1) * (xR)) % (p) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_23
  have hv29_24 : v29 24 = ((1) * (yR)) % (p) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_24
  have hv29_30 : v29 30 = p := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_30
  have hv29_47 : v29 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_47
  have hv29_55 : v29 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_55
  have hv29_56 : v29 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu29, Function.update_of_ne (by decide)]; exact hv28_56
  have hv29_58 : v29 58 = ((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p) := by rw [← hu29]; simp [Function.update_self, hv28_57, hv28_23, hv28_30]
  have zz29 : ScKeep ZAll2 r28.1 r29.1 := sck_step z29 (fun y h => Or.inl h)
  clear hu28 hv28_21 hv28_22 hv28_23 hv28_24 hv28_30 hv28_47 hv28_55 hv28_56 hv28_57 e28 se28 z29
  obtain ⟨e30, z30, a30, k30⟩ := env_mulMod 59 21 23 30 45 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r29.1 W v29 e29 (by rw [hv29_21, hv29_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv29_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr30 : Cmd.run (mulMod 59 21 23 30 45 46) r29.1 = r30 at e30 z30 a30 k30
  have se30 : ScEnv r30.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se29 z30
  generalize hu30 : Function.update v29 59 ((v29 21 * v29 23) % v29 30) = v30 at e30
  have hv30_21 : v30 21 = ((1) * (a)) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_21
  have hv30_22 : v30 22 = ((1) * (b)) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_22
  have hv30_23 : v30 23 = ((1) * (xR)) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_23
  have hv30_24 : v30 24 = ((1) * (yR)) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_24
  have hv30_30 : v30 30 = p := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_30
  have hv30_47 : v30 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_47
  have hv30_55 : v30 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_55
  have hv30_56 : v30 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_56
  have hv30_58 : v30 58 = ((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p) := by rw [← hu30, Function.update_of_ne (by decide)]; exact hv29_58
  have hv30_59 : v30 59 = ((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p) := by rw [← hu30]; simp [Function.update_self, hv29_21, hv29_23, hv29_30]
  have zz30 : ScKeep ZAll2 r29.1 r30.1 := sck_step z30 (fun y h => Or.inl h)
  clear hu29 hv29_21 hv29_22 hv29_23 hv29_24 hv29_30 hv29_47 hv29_55 hv29_56 hv29_58 e29 se29 z30
  obtain ⟨e31, z31, a31, k31⟩ := env_addMod 58 59 30 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r30.1 W v30 e30 (by rw [hv30_58, hv30_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv30_59, hv30_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv30_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr31 : Cmd.run (addMod 58 59 30 45) r30.1 = r31 at e31 z31 a31 k31
  have se31 : ScEnv r31.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se30 z31
  generalize hu31 : Function.update v30 58 ((v30 58 + v30 59) % v30 30) = v31 at e31
  have hv31_21 : v31 21 = ((1) * (a)) % (p) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_21
  have hv31_22 : v31 22 = ((1) * (b)) % (p) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_22
  have hv31_23 : v31 23 = ((1) * (xR)) % (p) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_23
  have hv31_24 : v31 24 = ((1) * (yR)) % (p) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_24
  have hv31_30 : v31 30 = p := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_30
  have hv31_47 : v31 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_47
  have hv31_55 : v31 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_55
  have hv31_56 : v31 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu31, Function.update_of_ne (by decide)]; exact hv30_56
  have hv31_58 : v31 58 = ((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p) := by rw [← hu31]; simp [Function.update_self, hv30_58, hv30_59, hv30_30]
  have zz31 : ScKeep ZAll2 r30.1 r31.1 := sck_step z31 (fun y h => Or.inl h)
  clear hu30 hv30_21 hv30_22 hv30_23 hv30_24 hv30_30 hv30_47 hv30_55 hv30_56 hv30_58 hv30_59 e30 se30 z31
  obtain ⟨e32, z32, a32, k32⟩ := env_addMod 58 22 30 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r31.1 W v31 e31 (by rw [hv31_58, hv31_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv31_22, hv31_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption) (by rw [hv31_30]; first | omega | exact Nat.mod_lt _ hp0 | exact Nat.mod_lt _ hpos | assumption)
  generalize hr32 : Cmd.run (addMod 58 22 30 45) r31.1 = r32 at e32 z32 a32 k32
  have se32 : ScEnv r32.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se31 z32
  generalize hu32 : Function.update v31 58 ((v31 58 + v31 22) % v31 30) = v32 at e32
  have hv32_21 : v32 21 = ((1) * (a)) % (p) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_21
  have hv32_22 : v32 22 = ((1) * (b)) % (p) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_22
  have hv32_23 : v32 23 = ((1) * (xR)) % (p) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_23
  have hv32_24 : v32 24 = ((1) * (yR)) % (p) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_24
  have hv32_30 : v32 30 = p := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_30
  have hv32_47 : v32 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_47
  have hv32_55 : v32 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_55
  have hv32_56 : v32 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [← hu32, Function.update_of_ne (by decide)]; exact hv31_56
  have hv32_58 : v32 58 = ((((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p)) + (((1) * (b)) % (p))) % (p) := by rw [← hu32]; simp [Function.update_self, hv31_58, hv31_22, hv31_30]
  have zz32 : ScKeep ZAll2 r31.1 r32.1 := sck_step z32 (fun y h => Or.inl h)
  clear hu31 hv31_21 hv31_22 hv31_23 hv31_24 hv31_30 hv31_47 hv31_55 hv31_56 hv31_58 e31 se31 z32
  obtain ⟨e33, f33, z33, a33, k33⟩ := env_geC 45 55 58 (by decide) (by decide) (by decide) (by decide) (by decide) r32.1 W v32 e32
  generalize hr33 : Cmd.run (geC 45 55 58) r32.1 = r33 at e33 f33 z33 a33 k33
  have se33 : ScEnv r33.1 (Function.update (c) 770 (r23.1.sc 722)) := scenv_keep se32 z33
  rw [hv32_55, hv32_58] at f33
  obtain ⟨v33, hvv33⟩ : ∃ w, w = v32 := ⟨_, rfl⟩
  rw [← hvv33] at e33
  have hv33_21 : v33 21 = ((1) * (a)) % (p) := by rw [hvv33]; exact hv32_21
  have hv33_22 : v33 22 = ((1) * (b)) % (p) := by rw [hvv33]; exact hv32_22
  have hv33_23 : v33 23 = ((1) * (xR)) % (p) := by rw [hvv33]; exact hv32_23
  have hv33_24 : v33 24 = ((1) * (yR)) % (p) := by rw [hvv33]; exact hv32_24
  have hv33_30 : v33 30 = p := by rw [hvv33]; exact hv32_30
  have hv33_47 : v33 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv33]; exact hv32_47
  have hv33_55 : v33 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [hvv33]; exact hv32_55
  have hv33_56 : v33 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv33]; exact hv32_56
  have hv33_58 : v33 58 = ((((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p)) + (((1) * (b)) % (p))) % (p) := by rw [hvv33]; exact hv32_58
  have zz33 : ScKeep ZAll2 r32.1 r33.1 := sck_step z33 (fun y h => Or.inl h)
  clear hu32 hv32_21 hv32_22 hv32_23 hv32_24 hv32_30 hv32_47 hv32_55 hv32_56 hv32_58 e32 se32 z33
  generalize hr34 : Cmd.run (.copy 771 722) r33.1 = r34
  have g34 : r34.1 = r33.1.setSc 771 (r33.1.sc 722) := by rw [← hr34]; rfl
  have e34 := env_setSc e33 771 (r33.1.sc 722) (by norm_num)
  rw [← g34] at e34
  have k34 : r34.2 = 1 := by rw [← hr34]; rfl
  have a34 : ArK AR r33.1 r34.1 := fun a _ => by rw [g34]; rfl
  have z34 : ScKeep (fun y => y = 771) r33.1 r34.1 := by rw [g34]; intro y hy; simp only [St.setSc_sc]; exact Function.update_of_ne hy _ _
  have se34 : ScEnv r34.1 (Function.update (Function.update (c) 770 (r23.1.sc 722)) 771 (r33.1.sc 722)) := by rw [g34]; exact scenv_set se33 (by decide) _
  obtain ⟨v34, hvv34⟩ : ∃ w, w = v33 := ⟨_, rfl⟩
  rw [← hvv34] at e34
  have hv34_21 : v34 21 = ((1) * (a)) % (p) := by rw [hvv34]; exact hv33_21
  have hv34_22 : v34 22 = ((1) * (b)) % (p) := by rw [hvv34]; exact hv33_22
  have hv34_23 : v34 23 = ((1) * (xR)) % (p) := by rw [hvv34]; exact hv33_23
  have hv34_24 : v34 24 = ((1) * (yR)) % (p) := by rw [hvv34]; exact hv33_24
  have hv34_30 : v34 30 = p := by rw [hvv34]; exact hv33_30
  have hv34_47 : v34 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv34]; exact hv33_47
  have hv34_55 : v34 55 = ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p) := by rw [hvv34]; exact hv33_55
  have hv34_56 : v34 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv34]; exact hv33_56
  have hv34_58 : v34 58 = ((((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p)) + (((1) * (b)) % (p))) % (p) := by rw [hvv34]; exact hv33_58
  have zz34 : ScKeep ZAll2 r33.1 r34.1 := sck_step z34 (by intro y h; subst h; simp [ZAll2, ZAll])
  clear hvv33 hv33_21 hv33_22 hv33_23 hv33_24 hv33_30 hv33_47 hv33_55 hv33_56 hv33_58 e33 se33 z34
  obtain ⟨e35, f35, z35, a35, k35⟩ := env_geC 45 58 55 (by decide) (by decide) (by decide) (by decide) (by decide) r34.1 W v34 e34
  generalize hr35 : Cmd.run (geC 45 58 55) r34.1 = r35 at e35 f35 z35 a35 k35
  have se35 : ScEnv r35.1 (Function.update (Function.update (c) 770 (r23.1.sc 722)) 771 (r33.1.sc 722)) := scenv_keep se34 z35
  rw [hv34_58, hv34_55] at f35
  obtain ⟨v35, hvv35⟩ : ∃ w, w = v34 := ⟨_, rfl⟩
  rw [← hvv35] at e35
  have hv35_21 : v35 21 = ((1) * (a)) % (p) := by rw [hvv35]; exact hv34_21
  have hv35_22 : v35 22 = ((1) * (b)) % (p) := by rw [hvv35]; exact hv34_22
  have hv35_23 : v35 23 = ((1) * (xR)) % (p) := by rw [hvv35]; exact hv34_23
  have hv35_24 : v35 24 = ((1) * (yR)) % (p) := by rw [hvv35]; exact hv34_24
  have hv35_30 : v35 30 = p := by rw [hvv35]; exact hv34_30
  have hv35_47 : v35 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv35]; exact hv34_47
  have hv35_56 : v35 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv35]; exact hv34_56
  have zz35 : ScKeep ZAll2 r34.1 r35.1 := sck_step z35 (fun y h => Or.inl h)
  clear hvv34 hv34_21 hv34_22 hv34_23 hv34_24 hv34_30 hv34_47 hv34_55 hv34_56 hv34_58 e34 se34 z35
  generalize hr36 : Cmd.run (.copy 772 722) r35.1 = r36
  have g36 : r36.1 = r35.1.setSc 772 (r35.1.sc 722) := by rw [← hr36]; rfl
  have e36 := env_setSc e35 772 (r35.1.sc 722) (by norm_num)
  rw [← g36] at e36
  have k36 : r36.2 = 1 := by rw [← hr36]; rfl
  have a36 : ArK AR r35.1 r36.1 := fun a _ => by rw [g36]; rfl
  have z36 : ScKeep (fun y => y = 772) r35.1 r36.1 := by rw [g36]; intro y hy; simp only [St.setSc_sc]; exact Function.update_of_ne hy _ _
  have se36 : ScEnv r36.1 (Function.update (Function.update (Function.update (c) 770 (r23.1.sc 722)) 771 (r33.1.sc 722)) 772 (r35.1.sc 722)) := by rw [g36]; exact scenv_set se35 (by decide) _
  obtain ⟨v36, hvv36⟩ : ∃ w, w = v35 := ⟨_, rfl⟩
  rw [← hvv36] at e36
  have hv36_21 : v36 21 = ((1) * (a)) % (p) := by rw [hvv36]; exact hv35_21
  have hv36_22 : v36 22 = ((1) * (b)) % (p) := by rw [hvv36]; exact hv35_22
  have hv36_23 : v36 23 = ((1) * (xR)) % (p) := by rw [hvv36]; exact hv35_23
  have hv36_24 : v36 24 = ((1) * (yR)) % (p) := by rw [hvv36]; exact hv35_24
  have hv36_30 : v36 30 = p := by rw [hvv36]; exact hv35_30
  have hv36_47 : v36 47 = (sInf {B | (p) ≤ B ^ m} - 1) + (1) := by rw [hvv36]; exact hv35_47
  have hv36_56 : v36 56 = (2 * (((p) * (p)) % (2 ^ (W - 1)))) % (2 ^ (W - 1)) := by rw [hvv36]; exact hv35_56
  have zz36 : ScKeep ZAll2 r35.1 r36.1 := sck_step z36 (by intro y h; subst h; simp [ZAll2, ZAll])
  clear hvv35 hv35_21 hv35_22 hv35_23 hv35_24 hv35_30 hv35_47 hv35_56 e35 se35 z36
  have harr : ArK AR s r36.1 := ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (ark_AR_trans (a1) a2) a3) a4) a5) a6) a7) a8) a9) a10) a11) a12) a13) a14) a15) a16) a17) a18) a19) a20) a21) a22) a23) a24) a25) a26) a27) a28) a29) a30) a31) a32) a33) a34) a35) a36
  have hzz : ScKeep ZAll2 s r36.1 := sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (sck_comp (zz1) zz2) zz3) zz4) zz5) zz6) zz7) zz8) zz9) zz10) zz11) zz12) zz13) zz14) zz15) zz16) zz17) zz18) zz19) zz20) zz21) zz22) zz23) zz24) zz25) zz26) zz27) zz28) zz29) zz30) zz31) zz32) zz33) zz34) zz35) zz36
  have h1 : r.1 = r36.1 := by rw [hr]; simp only [computeC, Cmd.run_seq, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30, hr31, hr32, hr33, hr34, hr35, hr36]
  have hcost : r.2 ≤ 400 * m * W * W * W + 12000 * m * W * W + 3000 * m * W + 2000 := by
    rw [hr]; simp only [computeC, Cmd.run_seq, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30, hr31, hr32, hr33, hr34, hr35, hr36]
    simp only [List.length_cons, List.length_nil] at k16 k20
    have hWW : W ≤ W * W := Nat.le_mul_self W
    have hmW : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
    have hmWW : W * W ≤ m * W * W := Nat.mul_le_mul_right W hmW
    have hmWWW : m * W * W ≤ m * W * W * W := Nat.le_mul_of_pos_right _ (by omega)
    linarith [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36]
  have hD : (((((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p)) + (((((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p)) * (27)) % (p))) % (p)) = (4 * a ^ 3 + 27 * b ^ 2) % p := by
    have := eq_of_zmod (p := p) (X := ((((((((((1) * (a)) % (p)) * (((1) * (a)) % (p))) % (p)) * (((1) * (a)) % (p))) % (p)) * (4)) % (p)) + (((((((1) * (b)) % (p)) * (((1) * (b)) % (p))) % (p)) * (27)) % (p))) % (p)) (Y := (4 * a ^ 3 + 27 * b ^ 2) % p) (by simp [ZMod.natCast_mod]; ring)
    simpa [Nat.mod_mod] using this
  have hL : (((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p)) = (yR * yR) % p := by
    have := eq_of_zmod (p := p) (X := ((((1) * (yR)) % (p)) * (((1) * (yR)) % (p))) % (p)) (Y := (yR * yR) % p) (by simp [ZMod.natCast_mod])
    simpa [Nat.mod_mod] using this
  have hR : (((((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p)) + (((1) * (b)) % (p))) % (p)) = (xR ^ 3 + a * xR + b) % p := by
    have := eq_of_zmod (p := p) (X := ((((((((((1) * (xR)) % (p)) * (((1) * (xR)) % (p))) % (p)) * (((1) * (xR)) % (p))) % (p)) + (((((1) * (a)) % (p)) * (((1) * (xR)) % (p))) % (p))) % (p)) + (((1) * (b)) % (p))) % (p)) (Y := (xR ^ 3 + a * xR + b) % p) (by simp [ZMod.natCast_mod]; ring)
    simpa [Nat.mod_mod] using this
  have s770 : r.1.sc 770 = r23.1.sc 722 := by
    rw [h1]; have := se36 770 (by decide); simp [Function.update_apply] at this; exact this
  have s771 : r.1.sc 771 = r33.1.sc 722 := by
    rw [h1]; have := se36 771 (by decide); simp [Function.update_apply] at this; exact this
  have s772 : r.1.sc 772 = r35.1.sc 722 := by
    rw [h1]; have := se36 772 (by decide); simp [Function.update_apply] at this; exact this
  have s0 : r.1.sc 0 = c 0 := by
    rw [h1]; have := se36 0 (by decide); simp [Function.update_apply] at this; exact this
  have s2 : r.1.sc 2 = c 2 := by
    rw [h1]; have := se36 2 (by decide); simp [Function.update_apply] at this; exact this
  have hE := e36
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s0, s2, ?_, ?_, hcost⟩
  · rw [h1, hE.2 21 (by decide), hv36_21]; simp
  · rw [h1, hE.2 22 (by decide), hv36_22]; simp
  · rw [h1, hE.2 23 (by decide), hv36_23]; simp
  · rw [h1, hE.2 24 (by decide), hv36_24]; simp
  · rw [h1, hE.2 47 (by decide), hv36_47]; omega
  · rw [h1, hE.2 56 (by decide), hv36_56]
    have e1 : p * p % 2 ^ (W - 1) = p * p := Nat.mod_eq_of_lt (by omega)
    have e2 : 2 * (p * p) % 2 ^ (W - 1) = 2 * (p * p) := Nat.mod_eq_of_lt h2pp
    simp [e1, e2]
  · rw [h1, hE.2 30 (by decide), hv36_30]
  · rw [s770, f23, hD]
  · rw [s771, f33, hL, hR]
  · rw [s772, f35, hL, hR]
  · rw [h1]; exact hE.1
  · rw [h1]; exact harr
  · rw [h1]; exact hzz

end ECDLP.L76
