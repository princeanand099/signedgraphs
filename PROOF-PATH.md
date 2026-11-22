# Proof Path & Manuscript Correspondence

| Paper Result | Location | Lean Module | Lean Declaration | Fidelity | Proof Status |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Def. 1.1 (`ϵ(C)`, `w_σ`, NOC) | Sec. 1, p. 2 | `SignedGraphs/Basic.lean` | `signedCycleType`, `modFourWeight`, `IsNOC` | Exact | Implemented |
| Inertia & Signature `s(A)` | Sec. 1, p. 1 | `SignedGraphs/Basic.lean` | `posInertia`, `negInertia`, `signature` | Exact | `inertia_sum` proved |
| Switching & Congruence | Sec. 2.1, p. 3 | `SignedGraphs/LinearAlgebra.lean` | `walkSignProd_switch`, `signature_congr`, `signature_eq_zero_of_bipartite` | Exact | In progress (`sorry`) |
| Weyl & Cauchy Interlacing | Sec. 2.1, p. 3 | `SignedGraphs/LinearAlgebra.lean` | `signature_mono_of_posSemidef`, `signature_interlacing_delete_vertex` | Exact | In progress (`sorry`) |
| Lemma 2.1 (Cut-vertex) | Sec. 2.2, pp. 3–4 | `SignedGraphs/LocalReductions.lean` | `cut_vertex_reduction` | Exact | In progress (`sorry`) |
| Lemma 2.2 (Degree-2) | Sec. 2.2, pp. 4–5 | `SignedGraphs/LocalReductions.lean` | `degree_two_reduction` | Exact | In progress (`sorry`) |
| Eq. (3.1) & Lemma 3.3 | Sec. 3, pp. 6–7 | `SignedGraphs/ParityAndCycles.lean` | `even_cycle_arc_weight_diff`, `even_odd_cycle_linkage` | Exact | In progress (`sorry`) |
| Lemma 3.4 (Cycle pairs) | Sec. 3, pp. 7–9 | `SignedGraphs/ParityAndCycles.lean` | `cycle_pair_obstructions_*` | Exact | In progress (`sorry`) |
| Theorem 3.1 (Classification) | Sec. 3, pp. 9–10 | `SignedGraphs/Classification.lean` | `three_connected_non_bipartite_noc_classification` | Exact | In progress (`sorry`) |
| Proposition 4.1 (Bipartite R-leaf) | Sec. 4, pp. 10–11 | `SignedGraphs/BipartiteLeaves.lean` | `bipartite_r_leaf_path_diversity` | Exact | In progress (`sorry`) |
| Lemma 5.1 (`K₄` & diamond) | Sec. 5, pp. 11–12 | `SignedGraphs/SchurReductions.lean` | `k4_signature_nonpos`, `k4_leaf_reduction` | Exact | In progress (`sorry`) |
| Lemma 5.2 (`Petersen` & leaf) | Sec. 5, pp. 12–15 | `SignedGraphs/SchurReductions.lean` | `petersen_signature_nonpos`, `petersen_leaf_reduction` | Exact | In progress (`sorry`) |
| SPQR Two-Leaf Theorem | Sec. 2.3 & 6, pp. 6, 15 | `SignedGraphs/SPQR.lean` | `two_r_leaves_of_two_connected_min_deg_three` | Exact | In progress (`sorry`) |
| Theorem 1.2 (Main Theorem) | Sec. 1 & 6, pp. 2, 15–16 | `SignedGraphs/MainTheorem.lean` & `Challenge.lean` | `theorem_1_2`, `Challenge.main_theorem_noc` | Exact | In progress (`sorry`) |
| Corollary 1.3 (Ma–Yang–Li) | Sec. 1 & 6, pp. 2, 16 | `SignedGraphs/MainTheorem.lean` & `Challenge.lean` | `corollary_1_3`, `Challenge.ma_yang_li_conjecture` | Exact | In progress (`sorry`) |
