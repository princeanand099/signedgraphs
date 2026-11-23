# Proof Path — Ma–Yang–Li Signature Conjecture (`signedgraphs`)

Zero-`sorry`, zero-custom-axiom Lean 4 (v4.35.0 + Mathlib) formalization of Prince Anand's proof of the Ma–Yang–Li Signature Conjecture (*"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"*).

## Module Dependency DAG (19 Modules)
1. `SignedGraphs/Basic.lean` — Signed graphs, switching equivalence, `IsNOC`, `modFourWeight`, `IsNOCModFour`, inertia/signature definitions, `K₄` and Petersen graph definitions.
2. `SignedGraphs/LinearAlgebra.lean` & `SignedGraphs/LinearAlgebraExtra.lean` — Sylvester's Law of Inertia, congruence invariance, block-diagonal additivity, Cauchy interlacing (`|s(A) - s(A - v)| ≤ 1`), Schur complement inertia (`s(A) = s(B) + s(A / B)`).
3. `SignedGraphs/GraphTools.lean` — 2-connectivity, Menger-style 2-disjoint paths (`two_disjoint_paths_between_sets`), cycle arc splitting, walk/path utilities.
4. `SignedGraphs/LocalReductions.lean` — **Lemma 2.1** (`cut_vertex_reduction`) and **Lemma 2.2** (`degree_two_reduction`).
5. `SignedGraphs/ParityCore.lean`, `SignedGraphs/MaximalEvenCycle.lean`, `SignedGraphs/ParityAndCycles.lean` — **Lemmas 3.2 & 3.3** (even-cycle parity, maximal even cycles, 3-connected NOC cycle structure).
6. `SignedGraphs/PetersenAlgebra.lean` & `SignedGraphs/PetersenSwitching.lean` — Algebraic and switching-equivalence characterizations of the all-negative Petersen signed graph.
7. `SignedGraphs/TwoOddCycles.lean` — **Lemma 3.4** (two odd cycles in 3-connected NOC graphs).
8. `SignedGraphs/Classification.lean` — **Theorem 3.1** (`three_connected_non_bipartite_noc_classification`).
9. `SignedGraphs/BipartiteLeaves.lean` — **Proposition 4.1** (`bipartite_r_leaf_path_diversity`).
10. `SignedGraphs/SPQR.lean` — **SPQR two-leaf theorem** (`two_r_leaves_of_two_connected_min_deg_three`).
11. `SignedGraphs/SchurReductions.lean` — **Lemma 5.1** (`k4_signature_nonpos`, `k4_leaf_reduction`) and **Lemma 5.2** (`petersen_signature_nonpos`, `petersen_leaf_reduction`).
12. `SignedGraphs/MainTheorem.lean` — **Theorem 1.2** (`theorem_1_2`) and **Corollary 1.3** (`corollary_1_3`).
13. `SignedGraphs/Challenge.lean` — Locked, self-contained public statements (`main_theorem_noc`, `ma_yang_li_conjecture`) using only core Lean and Mathlib definitions.
14. `SignedGraphs/SanityChecks.lean` — Non-vacuity witnesses (`n = 0, 1, 2, 3`, including non-bipartite `K₃`) and concrete small-case corollaries.
15. `SignedGraphs/AuditAxioms.lean` — `#print axioms` verification for all four headline theorems.
