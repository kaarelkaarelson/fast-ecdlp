# A Fast Algorithm for Elliptic-Curve Discrete Logarithms

A Las Vegas algorithm solves the discrete logarithm problem on every elliptic curve over a prime field F<sub>p</sub>, of any group order, in expected time p<sup>2/m+o(1)</sup> for every fixed m. For m ≥ 5 this is asymptotically faster than Pollard's rho method (p<sup>1/2</sup>).

The algorithm is Semaev's index calculus with a fast decomposition step: find R = P<sub>1</sub> + … + P<sub>m</sub> with every x(P<sub>i</sub>) < ⌈p<sup>1/m</sup>⌉ in time p<sup>o(1)</sup>. That step uses the counting engine of the October 2026 refutations of the Exponential Time Hypothesis, and it is proved in Lean 4 here, engine included, with no hypotheses.

The result is asymptotic. The guarantee beats rho only once log<sub>2</sub> log<sub>2</sub> p ≳ 5·10<sup>11</sup>, so it does not affect any elliptic curve in use.

The research, proofs and formalization were produced with Claude Opus 5.5 in a custom agent loop with automated verifiers; see the paper's declaration of AI use. Research artifact; not maintained and not accepting contributions.

## Paper

**[paper.pdf](paper.pdf)**: *A Fast Algorithm for Elliptic-Curve Discrete Logarithms*, Kaarel Kaarelson, 2026. IACR Cryptology ePrint Archive, link to appear.

## Lean proof

**1. Read the statement.** [`lean/Challenge.lean`](lean/Challenge.lean) (91 lines, imports only Mathlib) states the theorem `ECDLP.subexponentialRate m`:

> For every m there is one Turing machine (Mathlib's `TM2ComputableInTime`, finite alphabets, binary input) that, given a curve y² = x³ + ax + b over F<sub>p</sub>, a point R and a bit prefix, outputs the lexicographically least string of a decomposition R = P<sub>1</sub> + … + P<sub>m</sub> with x(P<sub>i</sub>) < ⌈p<sup>1/m</sup>⌉ (x-coordinates and sign bits) extending the prefix, or `none`, within C<sub>k</sub> · 2<sup>L/k</sup> steps on inputs of length L, for every k ≥ 1.

That is time p<sup>o(1)</sup>. The file has no proofs and is short so that a reader can check it against Theorem 2 of the paper. [`lean/Solution.lean`](lean/Solution.lean) states the same declarations and proves the theorem.

**2. Check the proofs.** With [elan](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake exe cache get        # downloads compiled Mathlib
lake build                # about 12 minutes, about 10 GB of disk
lake env lean Verify.lean
```

`lake build` prints one warning, `declaration uses 'sorry'`, from `Challenge.lean`, where the statement is left unproved on purpose. [`VERIFICATION.md`](VERIFICATION.md) records a clean build: 9597 jobs, about 12 minutes. `Verify.lean` prints the axioms of the main theorem and of every theorem in the paper's Lean table. Each line should read:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. Lean and Mathlib are pinned to `v4.35.0`.

**Fuller check.** [`lean/comparator.json`](lean/comparator.json) configures [Comparator](https://github.com/leanprover/comparator): it checks that `Solution.lean` proves exactly the statement in `Challenge.lean`, using only the three axioms, and re-checks the proof with a second kernel (`nanoda`).

## What is not in Lean

These results have written proofs in the paper. They rely on classical results that Lean's library does not yet contain (the Weil bound for character sums on curves, Semaev's theorem on summation polynomials, Schoof's point counting, rigorous factoring and sparse linear algebra), and they are backed by numerical checks in `scripts/` (see [`docs/REPRODUCE.md`](docs/REPRODUCE.md)):

- the discrete-logarithm theorems: Theorem 1 (the main theorem, every curve and every m) and Theorems 4–6;
- Theorem 3: in a random isomorphic model of any curve, a constant fraction of points decompose;
- the counting form of Theorem 2, which uses the engine papers' statements.

## Layout

| Path | Contents |
|---|---|
| `paper.pdf` | The paper. |
| `lean/Challenge.lean` | The statement to audit (Mathlib only). |
| `lean/Solution.lean` | The proof of that statement. |
| `lean/Main.lean` | The main results under readable names; start here. |
| `lean/Verify.lean` | Axiom check for the main theorem and the paper's Lean table. |
| `lean/ECDLP/` | All lemmas and proofs. Module names (e.g. `L104_Final`) are the ones cited in the paper's Lean table. |
| `lean/vendor/rudich-factoring/` | The counting engine as proved by Rudich and Rousseau (Apache 2.0). |
| `lean/comparator.json`, `lean/formalization.yaml` | Comparator configuration and project metadata. |
| `scripts/` | Numerical checks for the paper-only results, one folder per topic; [`scripts/README.md`](scripts/README.md) gives each command and its expected output. |
| `docs/REPRODUCE.md` | Each claim of the paper → how to check it → expected output. |
| `docs/MODULES.md` | What each group of Lean modules contains. |
| `docs/CLAIMS.md` | Each claim → how it is established (Lean, paper proof, numerical check, citation). |

## Navigating the Lean code

Start with [`lean/Main.lean`](lean/Main.lean): it restates the main results under readable names. The modules in `lean/ECDLP/` are named after the work packages that produced them, and the paper cites these names. By topic:

| Topic | Modules |
|---|---|
| The statement and the final assembly | `L35`, `L61`, `L77`, `L78`, `L80`, `L92`, `L102`, `L104` |
| Group law as integer constraints | `L30` |
| Search from counts | `L31` |
| Multiplication gadgets and networks | `L34`, `L38`, `L44`, `L51`, `L54`, `L56`, `L93` |
| The counting engine on this network: size, cost, value | `L57`–`L60`, `L63`–`L65`, `L69`–`L72`, `L84`, `L85`, `L87`, `L88`, `L94`, `L96` |
| Gate expressions and their bounds | `L68`, `L73`–`L76`, `L79`, `L81`–`L83`, `L86`, `L89`–`L91`, `L95` |
| Coverage, with the classical inputs as hypotheses | `L40`, `L43`, `L46`, `L49` |
| Audit examples | `L105` |

[`docs/MODULES.md`](docs/MODULES.md) describes every group.

## How the proof works

1. **Group law as integer constraints.** The addition formulas for m points become a system of integer identities with bounded quotients.
2. **A network of multiplication checks.** The system is checked by a network of local multiplication gadgets that shares only O(m log p) bits in total.
3. **Counting engine.** The engine counts solutions of such a network in time 2<sup>o(bits)</sup> = p<sup>o(1)</sup>.
4. **Search from counts.** Counting with prescribed leading bits, one bit at a time, recovers the lexicographically least decomposition.
5. **Index calculus** (paper only). Decompositions give relations; averaging over the p − 1 isomorphic models of the curve guarantees enough of them; sparse linear algebra gives the logarithm.

## Citation

```bibtex
@misc{kaarelson2026fastecdlp,
  author = {Kaarelson, Kaarel},
  title  = {A Fast Algorithm for Elliptic-Curve Discrete Logarithms},
  year   = {2026},
  howpublished = {IACR Cryptology ePrint Archive},
  note   = {identifier to appear}
}
```

## License

The code, proofs and documents in this repository are licensed under the [Apache License 2.0](LICENSE), copyright 2026 Kaarel Kaarelson.

Third-party material, listed in [NOTICE](NOTICE):

| Component | Location | License |
|---|---|---|
| Lean development of Rudich and Rousseau (the counting engine) | `lean/vendor/rudich-factoring/`, a subset of the original files, unmodified apart from `lakefile.toml` | Apache 2.0, its own [LICENSE](lean/vendor/rudich-factoring/LICENSE) |
| Lean 4, Mathlib and its dependencies | downloaded at build time | Apache 2.0 (one dependency, Cli, is MIT) |

The paper (`paper.pdf`) is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
