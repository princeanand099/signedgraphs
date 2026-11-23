# Ma–Yang–Li Signature Conjecture (`signedgraphs`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24463191.svg)](https://doi.org/10.5281/zenodo.24463191)

Lean 4 (`v4.35.0` + Mathlib) formalization of Prince Anand's manuscript [*"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"*](https://doi.org/10.5281/zenodo.24463191) (`Ma Yang Li Signature.pdf`, `ma_yang_li_signature.tex`). The main result proves that every real symmetric zero-diagonal matrix $A$ whose underlying signed graph is negative-odd-cycle (NOC) satisfies $s(A) \le 0$ (Theorem 1.2), and deduces the 2013 Ma–Yang–Li Signature Conjecture (Corollary 1.3): for every finite simple graph $G$,
$$-c_3(G) \le s(G) \le c_5(G),$$
where $s(G) = n_+(G) - n_-(G)$ is the signature of the adjacency matrix of $G$, $c_3(G)$ is the number of simple cycles of length $\equiv 3 \pmod 4$, and $c_5(G)$ is the number of simple cycles of length $\equiv 1 \pmod 4$.

## Scope & Verification Status

- **Proved**: All manuscript results (Theorem 1.2, Corollary 1.3, Lemmas 2.1–2.2, Theorem 3.1, Lemmas 3.2–3.4, Proposition 4.1, Lemmas 5.1–5.2, and the SPQR two-leaf theorem), public challenge statements using only core Lean and Mathlib types in their signatures (`SignedGraphs/Challenge.lean`), and non-vacuity/small-case witnesses for $n = 0, 1, 2, 3$ including non-bipartite $K_3$ (`SignedGraphs/SanityChecks.lean`).
- **Build, Hygiene & Comparator Audit**: Verified green end-to-end in CI log [`ad922d15`](https://github.com/princeanand099/signedgraphs/commit/ad922d159f8479e54a50e9156efd214a95e0d4d0) on commit [`b63325c8`](https://github.com/princeanand099/signedgraphs/commit/b63325c8ab10b3ff035ccfbec732b5e2f47e8759):
  - `lake build SignedGraphs Solution`: `9070/9070` jobs succeeded (all proof/check modules `✔`, `SignedGraphs.AuditAxioms` `ℹ`, plus Lake v4.35's standard informational `module`-system notice on `Basic.lean` and `ChallengeDefs.lean`).
  - Static anti-cheat hygiene check: `0` forbidden constructs (`sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `unsafeCast`, `implemented_by`, `extern`, `partial`, `skipKernelTC`, `local instance`).
  - `SignedGraphs/AuditAxioms.lean`: all four headline theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
  - Sandboxed `lake comparator` (`bwrap`, `comparator.json` with `definition_names: []`): `Lean default kernel accepts the solution` / `Your solution is okay!`.
- **Comparator Audit Layout**: To trust the main results without reading the 18 proof modules, inspect `comparator/ChallengeDefs.lean` (40 lines, imports only `Mathlib`), `comparator/Challenge.lean` (35 lines, intentional `sorry` statements), `comparator.json` (13 lines), and the CI comparator log. For multi-kernel replay on a local Linux machine with sufficient RAM, run `bash scripts/verify.sh --paranoid`.

## Theorem-to-Lean Mapping

| Paper Result | Mathematical Statement | Lean Declaration | Module | Status |
|---|---|---|---|---|
| **Theorem 1.2** | Real symmetric zero-diagonal NOC matrix $A \implies s(A) \le 0$ | `SignedGraphs.theorem_1_2` | `SignedGraphs/MainTheorem.lean` | Proved |
| **Theorem 1.2 (public)** | Mathlib-only signature of Theorem 1.2 | `SignedGraphs.Challenge.main_theorem_noc` | `SignedGraphs/Challenge.lean`, `comparator/Solution.lean` | Proved |
| **Corollary 1.3** | Every finite simple graph $G$ satisfies $-c_3(G) \le s(G) \le c_5(G)$ | `SignedGraphs.corollary_1_3` | `SignedGraphs/MainTheorem.lean` | Proved |
| **Corollary 1.3 (public)** | Mathlib-only signature of Corollary 1.3 | `SignedGraphs.Challenge.ma_yang_li_conjecture` | `SignedGraphs/Challenge.lean`, `comparator/Solution.lean` | Proved |
| **Lemma 2.1** | Cut-vertex reduction for NOC signature | `SignedGraphs.cut_vertex_reduction` | `SignedGraphs/LocalReductions.lean` | Proved |
| **Lemma 2.2** | Degree-2 vertex reduction for NOC signature | `SignedGraphs.degree_two_reduction` | `SignedGraphs/LocalReductions.lean` | Proved |
| **Theorem 3.1** | 3-connected non-bipartite NOC $\implies$ switching-equiv. to $(K_4, +1)$ or $(\text{Petersen}, -1)$ | `SignedGraphs.three_connected_non_bipartite_noc_classification` | `SignedGraphs/Classification.lean` | Proved |
| **Lemma 3.2** | Maximal even-cycle lemma in 3-connected graphs | `SignedGraphs.maximal_even_cycle_lemma` | `SignedGraphs/MaximalEvenCycle.lean` | Proved |
| **Eq. (3.1) & Lemma 3.3** | Even-cycle arc weight difference and even–odd cycle linkage | `SignedGraphs.even_cycle_arc_weight_diff`, `SignedGraphs.even_odd_cycle_linkage` | `SignedGraphs/ParityCore.lean` | Proved |
| **Lemma 3.4(1)–(2)** | No disjoint or 1-vertex-sharing even–odd cycle pair in 3-connected NOC graphs | `SignedGraphs.cycle_pair_obstructions_disjoint_even_odd`, `SignedGraphs.cycle_pair_obstructions_one_vertex_even_odd` | `SignedGraphs/ParityAndCycles.lean` | Proved |
| **Lemma 3.4(3)** | Two disjoint odd cycles in a 3-connected NOC graph force $(\text{Petersen}, -1)$ | `SignedGraphs.cycle_pair_obstructions_two_disjoint_odd_impl` | `SignedGraphs/TwoOddCycles.lean` | Proved |
| **Proposition 4.1** | Bipartite R-leaf has two $(x,y)$-paths differing by $2 \pmod 4$ | `SignedGraphs.bipartite_r_leaf_path_diversity` | `SignedGraphs/BipartiteLeaves.lean` | Proved |
| **SPQR Two-Leaf** | 2-connected $\delta \ge 3$ non-3-connected graph has two R-leaves | `SignedGraphs.two_r_leaves_of_two_connected_min_deg_three` | `SignedGraphs/SPQR.lean` | Proved |
| **Lemma 5.1** | Positive-weighted $(K_4, +1)$ signature $\le 0$ and $(K_4 - xy, +1)$ leaf reduction | `SignedGraphs.k4_signature_nonpos`, `SignedGraphs.k4_leaf_reduction` | `SignedGraphs/SchurReductions.lean` | Proved |
| **Lemma 5.2** | Negative-weighted $(\text{Petersen}, -1)$ signature $\le 0$ and $(\text{Petersen} - xy, -1)$ leaf reduction | `SignedGraphs.petersen_signature_nonpos`, `SignedGraphs.petersen_leaf_reduction` | `SignedGraphs/SchurReductions.lean` | Proved |
| **Non-Vacuity Checks** | Explicit NOC witnesses ($n = 0, 1, 2, 3$ incl. non-bipartite $K_3$) and small cases | `SignedGraphs.SanityChecks.*` | `SignedGraphs/SanityChecks.lean` | Proved |

## Check It Yourself

Run the full verification script (do **not** run `lake update`, which breaks pinned reproducibility):

```bash
# Build, static hygiene check, axiom audit, and lake comparator (Linux with bubblewrap)
bash scripts/verify.sh

# Multi-kernel paranoid replay (requires >16 GB RAM on Linux with bubblewrap)
bash scripts/verify.sh --paranoid

# Without comparator (e.g., on macOS without bubblewrap)
bash scripts/verify.sh --no-comparator
```

Expected `#print axioms` output (`SignedGraphs/AuditAxioms.lean`):
```
'SignedGraphs.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.corollary_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.main_theorem_noc' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.ma_yang_li_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Repository Layout

- `SignedGraphs.lean` — Root aggregator importing all 19 modules.
- `SignedGraphs/Challenge.lean` — Public theorem statements (`main_theorem_noc`, `ma_yang_li_conjecture`) using only core Lean and Mathlib types in their signatures.
- `SignedGraphs/SanityChecks.lean` — Non-vacuity witnesses and concrete small-case corollaries ($n = 0, 1, 2, 3$).
- `SignedGraphs/AuditAxioms.lean` — `#print axioms` verification for all four headline theorems.
- `SignedGraphs/*.lean` — Modular proof development (see `PROOF-PATH.md` and `PROGRESS.md`).
- `comparator/` & `comparator.json` — Standalone `ChallengeDefs.lean`, `Challenge.lean`, `Solution.lean`, and configuration for `lake comparator`.
- `scripts/verify.sh` — End-to-end verification script (`lake build`, static hygiene check, `#print axioms`, `lake comparator`).
- `CITATION.cff` — Machine-readable citation metadata (with manuscript DOI [`10.5281/zenodo.24463191`](https://doi.org/10.5281/zenodo.24463191)).
- `EXTERNAL-AXIOMS.md` — External/custom axiom audit (none used).
- `ATTRIBUTION.md` — Authorship, manuscript reference, and dependency attribution.
- `Ma Yang Li Signature.pdf`, `ma_yang_li_signature.tex` — Source manuscript.
