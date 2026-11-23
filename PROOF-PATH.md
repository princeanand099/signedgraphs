# Proof Path — Ma–Yang–Li Signature Conjecture (`signedgraphs`)

Complete, zero-`sorry`, zero-custom-axiom Lean 4 (v4.35.0 + Mathlib) formalization of Prince Anand's proof of the Ma–Yang–Li Signature Conjecture (*"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"*).

## Verified Build & Axiom Audit
- **Verified Lean 4 Build**: `lake build` — **9066/9066 jobs succeeded** (CI log [`09bd34f3`](https://github.com/princeanand099/signedgraphs/commit/09bd34f328d1fb54bac9174807776152499d7070) for commit [`9a14ee0a`](https://github.com/princeanand099/signedgraphs/commit/9a14ee0ab530aba67452d9610a6884e8e73bfdbf)).
- **Axiom Audit (`SignedGraphs/AuditAxioms.lean`)**:
  - `SignedGraphs.theorem_1_2` — `[propext, Classical.choice, Quot.sound]`
  - `SignedGraphs.corollary_1_3` — `[propext, Classical.choice, Quot.sound]`
  - `SignedGraphs.Challenge.main_theorem_noc` — `[propext, Classical.choice, Quot.sound]`
  - `SignedGraphs.Challenge.ma_yang_li_conjecture` — `[propext, Classical.choice, Quot.sound]`

## Module Dependency DAG (18 Modules — All Complete)
1. `SignedGraphs/Basic.lean` — Signed graphs, switching equivalence, `IsNOC`, `modFourWeight`, `IsNOCModFour`, inertia/signature definitions, `K₄` and Petersen graph definitions.
2. `SignedGraphs/LinearAlgebra.lean` & `SignedGraphs/LinearAlgebraExtra.lean` — Sylvester's Law of Inertia, congruence invariance, block-diagonal additivity, Cauchy interlacing (`|s(A) - s(A - v)| ≤ 1`), Schur complement inertia (`s(A) = s(B) + s(A / B)`).
3. `SignedGraphs/GraphTools.lean` — 2-connectivity, Menger-style 2-disjoint paths (`two_disjoint_paths_between_sets`), cycle arc splitting, walk/path utilities.
4. `SignedGraphs/LocalReductions.lean` — **Lemma 2.1** (cut-vertex reduction) and **Lemma 2.2** (degree-2 vertex reduction).
5. `SignedGraphs/ParityCore.lean`, `SignedGraphs/MaximalEvenCycle.lean`, `SignedGraphs/ParityAndCycles.lean` — **Lemmas 3.2 & 3.3** (even-cycle parity, maximal even cycles, 3-connected NOC cycle structure).
6. `SignedGraphs/PetersenAlgebra.lean` & `SignedGraphs/PetersenSwitching.lean` — Algebraic and switching-equivalence characterizations of the all-negative Petersen signed graph.
7. `SignedGraphs/TwoOddCycles.lean` — **Lemma 3.4** (two odd cycles in 3-connected NOC graphs).
8. `SignedGraphs/Classification.lean` — **Theorem 3.1** (3-connected non-bipartite NOC signed graphs are switching-equivalent to all-negative `K₄` or all-negative Petersen).
9. `SignedGraphs/BipartiteLeaves.lean` — **Proposition 4.1** (bipartite R-leaf path diversity: two `(x, y)`-paths differing by `2 mod 4`).
10. `SignedGraphs/SPQR.lean` — **SPQR two-leaf theorem** (`two_r_leaves_of_two_connected_min_deg_three`).
11. `SignedGraphs/SchurReductions.lean` — **Lemma 5.1** (`K₄` signature & leaf reduction) and **Lemma 5.2** (Petersen signature & leaf reduction via explicit Schur complements).
12. `SignedGraphs/MainTheorem.lean` — **Theorem 1.2** (`theorem_1_2`: every real symmetric zero-diagonal NOC matrix satisfies `s(A) ≤ 0`) and **Corollary 1.3** (`corollary_1_3`: `-c₃(G) ≤ s(G) ≤ c₅(G)`).
13. `SignedGraphs/Challenge.lean` — Locked, self-contained public statements (`main_theorem_noc`, `ma_yang_li_conjecture`) using only core Lean and Mathlib definitions.
14. `SignedGraphs/AuditAxioms.lean` — `#print axioms` verification for all four headline theorems.
