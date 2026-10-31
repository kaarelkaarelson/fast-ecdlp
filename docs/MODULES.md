# Module map

The Lean modules in `lean/ECDLP/` are named after the work packages that produced them (`L30_…` to `L105_…`); the paper cites these names. This table says what each group contains. Start with [`lean/Main.lean`](../lean/Main.lean), which restates the main results under readable names.

| Group | Contents | Modules |
|---|---|---|
| `L30` | Group law ⇔ integer constraint system; count equality | 5 |
| `L31` | Search from counts (prefix self-reduction) | 1 |
| `L34` | Multiplication gadgets: acceptance ⇔ integer identity | 6 |
| `L35` | The statement (Challenge copy); contraction of forced networks | 2 |
| `L38` | Gadgets as networks; value of the composed system | 6 |
| `L40` | Coverage, average over curves: energy and Cauchy–Schwarz skeleton | 5 |
| `L43` | Coverage, average over curves: assembly over a finite field | 3 |
| `L44` | One network for the whole integer system; value = count | 11 |
| `L46` | Coverage, average over curves: Las Vegas step and oracle link | 8 |
| `L49` | Coverage for a fixed curve over random isomorphic models | 6 |
| `L51` | Strings and prefixes of decompositions | 5 |
| `L54` | Broadcast network (correct, but too large for the engine) | 5 |
| `L56` | The edge network: value = count, search returns lexLeast | 4 |
| `L57` | Engine size and cluster conditions for the edge network | 9 |
| `L58` | Generic top step of the engine pipeline | 2 |
| `L59` | Explicit engine parameters | 5 |
| `L60` | Generic rate bound | 5 |
| `L61` | Driver: prefix search over oracle calls; Turing-machine encoding | 10 |
| `L63` | Instance inputs read by the network | 10 |
| `L64` | Expression layer for networks (node and edge expressions) | 6 |
| `L65` | The edge-network family and its rate | 7 |
| `L68` | Carry gates | 8 |
| `L69` | Cost of the counting command | 8 |
| `L70` | Capstone interface (oracle specification) | 4 |
| `L71` | Primality guard | 6 |
| `L72` | Reduction of the engine core to gate data | 7 |
| `L73` | Gate enumeration, decoding and dispatch | 11 |
| `L74` | Forward-transform and middle gates | 9 |
| `L75` | Inverse-transform gates; held-bit bounds | 11 |
| `L76` | Big-number commands; memory layout; input checks | 18 |
| `L77` | One-time gate; recoding to the statement's encoding | 9 |
| `L78` | Per-call prefix-length test | 3 |
| `L79` | Gate value bounds; closed-form digits | 25 |
| `L80` | Frame writer and per-call oracle | 15 |
| `L81` | Source and check gates | 5 |
| `L82` | Shallower dispatch expressions | 3 |
| `L83` | Concrete instance expressions; slot enumeration | 13 |
| `L84` | Engine cost; independence from scratch memory | 6 |
| `L85` | Engine cost chain with a depth parameter | 26 |
| `L86` | Expression depth bounds for the real network | 9 |
| `L87` | Assembly of the pipeline with the engine hypotheses | 1 |
| `L88` | Value of the counting command on this network | 3 |
| `L89` | Dispatch-level value bounds; clamped messages | 8 |
| `L90` | Gate kinds without the nonemptiness assumption | 10 |
| `L91` | Syntactic conditions on all expressions | 6 |
| `L92` | Frame invariant; short inputs; every m | 13 |
| `L93` | Network value = decomposition count for the real instances | 3 |
| `L94` | Cluster weights | 7 |
| `L95` | Repaired instance expressions; carry-gate bounds | 11 |
| `L96` | Assembly of the engine core for the real network | 10 |
| `L102` | The case m = 1 | 6 |
| `L104` | Final assembly: the main Lean theorem for every m | 13 |
| `L105` | Audit examples decided in the kernel (p = 13) | 1 |
