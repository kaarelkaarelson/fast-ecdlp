# Version 2

Version 2 of the paper adds two things to this repository: the paper itself, and the Lean modules that are new since version 1. Everything else (`lean/`, `scripts/`, `docs/`) is version 1 and has not changed.

## Paper

**[paper.pdf](paper.pdf)**: *A Fast Algorithm for Elliptic-Curve Discrete Logarithms*, version 2, November 1, 2026. The section "Changes from version 1" in the introduction lists what changed.

## Lean modules

`lean/` holds a Lake project with 59 modules. It builds on the version 1 project in `../../lean` and uses the same Mathlib download. The files sit under the module root `ECDLPv2` (so Lake does not look for them in version 1); the declarations keep their namespaces (`ECDLP.L132`, …), and the module names (`L132_Final`, …) are the ones the paper cites. The modules prove:

| Claim (paper, Table "Formal verification status") | Theorem | Module |
|---|---|---|
| Counting in time p<sup>o(1)</sup>, every m, engine included (Theorem 2(i), x-string with sign bits) | `ECDLP.L132.countingRate_all` | `L132_Final` |
| Relation lattice, recovery, Chinese remaindering, planted diagonal (Theorem 1) | `relation_lattice`, `recover_from_span`, `crt_correct`, `planted_kernel`, `runFinal_sound`, `runFinal_complete` | `L114_*` |
| Relation rows for an adaptive oracle; Chernoff cap | `algSpec_row_rel`, `cap_bound` | `L116_Alg`, `L116_Chernoff`, `L119_WAlg` |
| Random elements generate any finite abelian group (Lemma gen) | `ECDLP.L119.gen_log_explicit` | `L119_Gen` |
| n ≤ (1 + log<sub>2</sub> n) φ(n) | `ECDLP.L118.totient_ge` | `L118_Tot` |

The counting statement to audit is `ECDLP109.countingRate` in [`lean/ECDLPv2/L109_CountChallenge.lean`](lean/ECDLPv2/L109_CountChallenge.lean). It imports only Mathlib and is left as `sorry` on purpose, like `Challenge.lean` in version 1. `Verify.lean` ties `countingRate_all` to that statement with an `example`, so the proof does not use the `sorry`.

The index-calculus theorems carry the analytic inputs as named hypotheses: the coverage bound, the group order and its factorization, and the cost of the sparse linear algebra (paper, Section "Formal verification").

## Check the proofs

First build version 1 (see the [top-level README](../README.md)). Then:

```sh
cd v2/lean
lake build                # reuses the version 1 build
lake env lean Verify.lean
```

`lake build` prints one `declaration uses 'sorry'` warning, from `L109_CountChallenge.lean`. Every line of `Verify.lean`'s output should read:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Not in this folder

The paper says which claims cannot be checked from the repository: the scripts for the networks X and V8x, genus 2, Theorem 7 and its Remarks, and the new rows of the crossover table (block clustering, schedule, c<sub>1</sub> bound).
