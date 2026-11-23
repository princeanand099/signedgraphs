# Ma–Yang–Li Signature Conjecture (`signedgraphs`)

Lean 4 (v4.35.0 + Mathlib) formalization of Prince Anand's manuscript *"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"* (`Ma_Yang_Li_Signature.pdf`). The main result proves that every real symmetric zero-diagonal matrix $A$ whose underlying signed graph is negative-odd-cycle (NOC) satisfies $s(A) \le 0$ (Theorem 1.2), and deduces the 2013 Ma–Yang–Li Signature Conjecture (Corollary 1.3): for every finite simple graph $G$,
$$-c_3(G) \le s(G) \le c_5(G),$$
where $s(G) = n_+(G) - n_-(G)$ is the signature of the adjacency matrix of $G$, $c_3(G)$ is the number of simple cycles of length $\equiv 3 \pmod 4$, and $c_5(G)$ is the number of simple cycles of length $\equiv 1 \pmod 4$.

## Scope & Verification Status

- **Proved**: All manuscript results (Theorem 1.2, Corollary 1.3, Lemmas 2.1–2.2, Theorem 3.1, Lemmas 3.2–3.4, Proposition 4.1, Lemmas 5.1–5.2, SPQR two-leaf theorem), locked public challenge statements (`SignedGraphs/Challenge.lean`), and non-vacuity/small-case witnesses for $n = 0, 1, 2, 3$ including non-bipartite $K_3$ (`SignedGraphs/SanityChecks.lean`).
- **Axioms**: Zero custom axioms, zero `sorry`/`admit`, zero `native_decide`. Verified via `SignedGraphs/AuditAxioms.lean` in CI log [`09bd34f3`](https://github.com/princeanand099/signedgraphs/commit/09bd34f328d1fb54bac9174807776152499d7070) (commit [`9a14ee0a`](https://github.com/princeanand099/signedgraphs/commit/9a14ee0ab530aba67452d9610a6884e8e73bfdbf)): all four headline theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
- **Not run in CI**: Standalone `lean4checker --fresh` and `lake comparator --paranoid` are not currently configured as separate CI steps (instructions for running them locally are included below).

## Theorem-to-Lean Mapping

| Paper Result | Mathematical Statement | Lean Declaration | Module | Status |
|---|---|---|---|---|
| **Theorem 1.2** | Real symmetric zero-diagonal NOC matrix $A \implies s(A) \le 0$ | `SignedGraphs.theorem_1_2` | `SignedGraphs/MainTheorem.lean` | Proved |
| **Theorem 1.2 (locked)** | Self-contained Mathlib-only statement of Theorem 1.2 | `SignedGraphs.Challenge.main_theorem_noc` | `SignedGraphs/Challenge.lean` | Proved |
| **Corollary 1.3** | Every finite simple graph $G$ satisfies $-c_3(G) \le s(G) \le c_5(G)$ | `SignedGraphs.corollary_1_3` | `SignedGraphs/MainTheorem.lean` | Proved |
| **Corollary 1.3 (locked)** | Self-contained Mathlib-only statement of Corollary 1.3 | `SignedGraphs.Challenge.ma_yang_li_conjecture` | `SignedGraphs/Challenge.lean` | Proved |
| **Lemma 2.1** | Cut-vertex reduction for NOC signature | `SignedGraphs.cut_vertex_reduction` | `SignedGraphs/LocalReductions.lean` | Proved |
| **Lemma 2.2** | Degree-2 vertex reduction for NOC signature | `SignedGraphs.degree_two_reduction` | `SignedGraphs/LocalReductions.lean` | Proved |
| **Theorem 3.1** | 3-connected non-bipartite NOC $\iff$ switching-equiv. to $-K_4$ or $-\text{Petersen}$ | `SignedGraphs.three_connected_non_bipartite_noc_classification` | `SignedGraphs/Classification.lean` | Proved |
| **Lemmas 3.2–3.3** | Even-cycle parity and maximal even cycle structure | `SignedGraphs.ParityAndCycles` | `SignedGraphs/ParityAndCycles.lean` | Proved |
| **Lemma 3.4** | Two odd cycles in 3-connected NOC signed graphs | `SignedGraphs.TwoOddCycles` | `SignedGraphs/TwoOddCycles.lean` | Proved |
| **Proposition 4.1** | Bipartite R-leaf has two $(x,y)$-paths differing by $2 \pmod 4$ | `SignedGraphs.bipartite_r_leaf_path_diversity` | `SignedGraphs/BipartiteLeaves.lean` | Proved |
| **SPQR Two-Leaf** | 2-connected $\delta \ge 3$ non-3-connected graph has two R-leaves | `SignedGraphs.two_r_leaves_of_two_connected_min_deg_three` | `SignedGraphs/SPQR.lean` | Proved |
| **Lemma 5.1** | $K_4$ signature $\le 0$ and $K_4$ R-leaf Schur reduction | `SignedGraphs.k4_signature_nonpos`, `SignedGraphs.k4_leaf_reduction` | `SignedGraphs/SchurReductions.lean` | Proved |
| **Lemma 5.2** | Petersen signature $\le 0$ and Petersen R-leaf Schur reduction | `SignedGraphs.petersen_signature_nonpos`, `SignedGraphs.petersen_leaf_reduction` | `SignedGraphs/SchurReductions.lean` | Proved |
| **Non-Vacuity Checks** | Explicit NOC witnesses ($n = 0, 1, 2, 3$ incl. non-bipartite $K_3$) and small cases | `SignedGraphs.SanityChecks.*` | `SignedGraphs/SanityChecks.lean` | Proved |

## Check It Yourself

```bash
# 1. Fetch precompiled Mathlib oleans (do NOT run `lake update`, which breaks pinned reproducibility)
lake exe cache get

# 2. Build all modules (including Challenge, SanityChecks, and AuditAxioms)
lake build

# 3. Verify static absence of sorry / custom axioms / native_decide / unsafe constructs
grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC)\b' SignedGraphs/ SignedGraphs.lean

# 4. Inspect axiom audit output directly
lake env lean SignedGraphs/AuditAxioms.lean
```

Expected `#print axioms` output:
```
'SignedGraphs.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.corollary_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.main_theorem_noc' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.ma_yang_li_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To replay `.olean` files independently through `lean4checker` (if installed):
```bash
lake exe lean4checker --fresh SignedGraphs
```

## Repository Layout

- `SignedGraphs.lean` — Root aggregator importing all 19 modules.
- `SignedGraphs/Challenge.lean` — Locked, self-contained public theorem statements (`main_theorem_noc`, `ma_yang_li_conjecture`).
- `SignedGraphs/SanityChecks.lean` — Non-vacuity witnesses and concrete small-case corollaries ($n = 0, 1, 2, 3$).
- `SignedGraphs/AuditAxioms.lean` — `#print axioms` verification for all four headline theorems.
- `SignedGraphs/*.lean` — Modular proof development (see `PROOF-PATH.md` and `PROGRESS.md`).
- `EXTERNAL-AXIOMS.md` — External/custom axiom audit (none used).
- `ATTRIBUTION.md` — Authorship, manuscript reference, and dependency attribution.
- `Ma_Yang_Li_Signature.pdf`, `ma_yang_li_signature.tex` — Source manuscript.
