# Verification

A clean build of `lean/` in this repository, on October 31, 2026.

## Setup

- Machine: Mac, 16 cores, macOS 26.5.2; Lean `v4.35.0` (elan), Mathlib `v4.35.0`.
- Start state: `lean/.lake/build` and `lean/vendor/rudich-factoring/.lake` deleted; Mathlib's compiled files already downloaded (`lake exe cache get` reported `Already decompressed 9031 file(s)`; a first download took about 1 min).
- No edits were needed to make the build pass beyond the ones listed under "Changes from the paper's working tree".

## Commands

```sh
cd lean
lake exe cache get
nice -n 19 lake build            # default targets: Challenge, Solution, ECDLPArtifact, Verify
lake env lean Verify.lean
lake env lean Solution.lean
lake env lean Challenge.lean
```

## Result

- `lake build`: `Build completed successfully (9597 jobs).` 0 errors. Wall-clock time 699 s (about 12 min).
- After the final comment-only edits, `lake build Verify` was re-run: `Build completed successfully (9593 jobs)`, and `Verify.lean` again printed 42 lines, each `[propext, Classical.choice, Quot.sound]`.
- The only `sorry` warning: `Challenge.lean:86:8: declaration uses 'sorry'` (the Challenge's theorem, on purpose).
- Disk: `lean/.lake` 10 GB (Mathlib and the build), `lean/vendor/rudich-factoring/.lake` 327 MB.
- Modules built from this repository: `Challenge`, `Solution`, `ECDLPArtifact`, `Verify`, 409 files in `ECDLP/` and 133 files in `vendor/rudich-factoring/FactoringAux/`.
- The `example : ∀ m : ℕ, type_of% (ECDLP.subexponentialRate m) := ECDLP.L104R.subexponentialRate_all` in `Verify.lean` type-checks.

`lake env lean Solution.lean`:

```
'ECDLP.subexponentialRate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean Challenge.lean`:

```
Challenge.lean:86:8: warning: declaration uses `sorry`
'ECDLP.lexLeast_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean Verify.lean` (5 s):

```
'ECDLP.subexponentialRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L104R.subexponentialRate_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L77.subexponentialRate_zero_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L102.subexponentialRate_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L93.edgeCount_real_eq_Zc' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L92.count_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L92.zc_lt_len' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L96.frameIn_fr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L104.engFullHF_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L104.engFullHF_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.stepC_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.chain_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.chain_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.mul_modEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.zero_iff_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L30.card_int_eq_card_generic' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L31.search_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L31.search_abstract' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L34.Par.accept_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L34.NPar.good_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L35.Forced.forced_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L56.PForced.pforced_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L38.gadget_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L38.system_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L44.okC_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L56.edge_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L56.main_count_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L56.net_eq_ncard_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L56.search_computes_lexLeast_exists_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L57.exists_cluster' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L57.ecdlp_engine_conditions' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L94.wt_htot' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L40.sq_card_le_sums_mul_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L46.las_vegas_success' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L46.coverage_oracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L49.dilEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L49.dlp_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'ECDLP.L49.corollary4_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'E1' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2' depends on axioms: [propext, Classical.choice, Quot.sound]
'E4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every theorem reports only `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`, no new axiom.

## Continuous integration

The GitHub Actions workflow `.github/workflows/lean.yml` rebuilt the project from scratch and passed (run 41243751810): `lake build` with no `sorry` outside `Challenge.lean`, the axiom check in `Verify.lean`, and [Comparator](https://github.com/leanprover/comparator) with `lean/comparator.json`, which checks that `Solution.lean` proves exactly the statement in `Challenge.lean`, using only the three standard axioms, and re-checks the proof with a second kernel (nanoda).

## Changes from the paper's development

Two changes affect what a reader audits; neither changes a statement or a proof.

1. `Challenge.lean` holds the statement with `sorry`, and `Solution.lean` proves the same declaration. In the development the statement lived in `ECDLP/L35_Challenge.lean`; there it is now the definition `SubexponentialRateStmt` with the same statement, so that `Solution.lean` can declare `ECDLP.subexponentialRate` itself. The definitions of `Challenge.lean` and `ECDLP/L35_Challenge.lean` are textually identical.
2. `vendor/rudich-factoring/lakefile.toml` builds only the vendored files (see `NOTICE`).
