# Ma–Yang–Li Signature Conjecture — Complete Lean 4 Formalization

Complete, zero-`sorry`, zero-custom-axiom Lean 4 (v4.35.0 + Mathlib) formalization of Prince Anand's proof of the **Ma–Yang–Li Signature Conjecture** (*"A Proof of the Ma–Yang–Li Signature Conjecture via Weighted Signed Graphs"*).

## Headline Theorems (Locked in `SignedGraphs/Challenge.lean`)
- **`SignedGraphs.Challenge.main_theorem_noc` (Theorem 1.2)**: Every real symmetric zero-diagonal matrix $A$ whose underlying signed graph is negative-odd-cycle (NOC) satisfies $s(A) \le 0$.
- **`SignedGraphs.Challenge.ma_yang_li_conjecture` (Corollary 1.3 — Ma–Yang–Li Conjecture)**: Every finite simple graph $G$ satisfies
  $$-c_3(G) \le s(G) \le c_5(G),$$
  where $s(G) = n_+(G) - n_-(G)$ is the signature of the adjacency matrix of $G$, $c_3(G)$ is the number of simple cycles of length $\equiv 3 \pmod 4$, and $c_5(G)$ is the number of simple cycles of length $\equiv 1 \pmod 4$.

## Verification
- **CI Build**: 100% green (`9066/9066` jobs) — see CI log [`09bd34f3`](https://github.com/princeanand099/signedgraphs/commit/09bd34f328d1fb54bac9174807776152499d7070) for commit [`9a14ee0a`](https://github.com/princeanand099/signedgraphs/commit/9a14ee0ab530aba67452d9610a6884e8e73bfdbf).
- **Axiom Audit (`SignedGraphs/AuditAxioms.lean`)**: All four headline theorems (`theorem_1_2`, `corollary_1_3`, `Challenge.main_theorem_noc`, `Challenge.ma_yang_li_conjecture`) depend strictly on the standard Lean axioms `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero custom `axiom`, and zero `native_decide`.
- See `PROOF-PATH.md`, `PROGRESS.md`, and `EXTERNAL-AXIOMS.md` for full module architecture and audit details.
