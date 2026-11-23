# Proof Path — Ma–Yang–Li Signature Conjecture (`signedgraphs`)

Zero-`sorry`, zero-custom-axiom Lean 4 (`v4.35.0` + Mathlib) formalization of Prince Anand's proof of the Ma–Yang–Li Signature Conjecture (*"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"*).

## Module Dependency DAG (19 Modules)
1. `SignedGraphs/Basic.lean` — Signed graphs, switching equivalence, `IsNOC`, `modFourWeight`, `IsNOCModFour`, inertia/signature definitions, `(K₄, +1)` (`k4SignedGraph`) and `(Petersen, -1)` (`petersenSignedGraph`) definitions.
2. `SignedGraphs/LinearAlgebra.lean` & `SignedGraphs/LinearAlgebraExtra.lean` — Sylvester's Law of Inertia, congruence invariance, block-diagonal additivity, Cauchy interlacing (`|s(A) - s(A - v)| ≤ 1`), Weyl monotonicity, and Schur complement inertia (`s(A) = s(B) + s(A / B)`).
3. `SignedGraphs/GraphTools.lean` — 2-connectivity, Menger-style 2-disjoint paths (`two_disjoint_paths_between_sets`), cycle arc splitting, walk/path utilities.
4. `SignedGraphs/LocalReductions.lean` — **Lemma 2.1** (`cut_vertex_reduction`) and **Lemma 2.2** (`degree_two_reduction`).
5. `SignedGraphs/ParityCore.lean` — **Eq. (3.1)** (`even_cycle_arc_weight_diff`) and **Lemma 3.3** (`even_odd_cycle_linkage`).
6. `SignedGraphs/MaximalEvenCycle.lean` — **Lemma 3.2** (`maximal_even_cycle_lemma`).
7. `SignedGraphs/ParityAndCycles.lean` — **Lemma 3.4(1)–(2)** (`cycle_pair_obstructions_disjoint_even_odd`, `cycle_pair_obstructions_one_vertex_even_odd`).
8. `SignedGraphs/PetersenAlgebra.lean` & `SignedGraphs/PetersenSwitching.lean` — Algebraic and switching-equivalence characterizations of `(Petersen, -1)`.
9. `SignedGraphs/TwoOddCycles.lean` — **Lemma 3.4(3)** (`cycle_pair_obstructions_two_disjoint_odd_impl`).
10. `SignedGraphs/Classification.lean` — **Theorem 3.1** (`three_connected_non_bipartite_noc_classification`: 3-connected non-bipartite NOC implies switching-equivalent to `(K₄, +1)` or `(Petersen, -1)`).
11. `SignedGraphs/BipartiteLeaves.lean` — **Proposition 4.1** (`bipartite_r_leaf_path_diversity`).
12. `SignedGraphs/SPQR.lean` — **SPQR two-leaf theorem** (`two_r_leaves_of_two_connected_min_deg_three`).
13. `SignedGraphs/SchurReductions.lean` — **Lemma 5.1** (`k4_signature_nonpos`, `k4_leaf_reduction`) and **Lemma 5.2** (`petersen_signature_nonpos`, `petersen_leaf_reduction`).
14. `SignedGraphs/MainTheorem.lean` — **Theorem 1.2** (`theorem_1_2`) and **Corollary 1.3** (`corollary_1_3`).
15. `SignedGraphs/Challenge.lean` — Public theorem statements (`main_theorem_noc`, `ma_yang_li_conjecture`) using only core Lean and Mathlib types in their signatures.
16. `SignedGraphs/SanityChecks.lean` — Non-vacuity witnesses (`n = 0, 1, 2, 3`, including non-bipartite `K₃`) and concrete small-case corollaries.
17. `SignedGraphs/AuditAxioms.lean` — `#print axioms` verification for all four headline theorems.
