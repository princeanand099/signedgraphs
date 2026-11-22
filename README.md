# SignedGraphs: Lean 4 Formalization of the Ma–Yang–Li Signature Conjecture

Formalization in Lean 4 (`v4.35.0` + Mathlib) of Prince Anand's proof of the Ma–Yang–Li signature conjecture via weighted signed graphs (`ma_yang_li_signature.tex`):

> Every finite simple graph $G$ satisfies $-c_3(G) \le s(G) \le c_5(G)$, deduced from the general NOC theorem: every real symmetric zero-diagonal matrix $A$ whose underlying signed graph $(G, \sigma)$ satisfies $\epsilon(C) = (-1)^k \prod_{e \in C} \sigma(e) = -1$ on every odd cycle $C$ of length $2k+1$ has signature $s(A) \le 0$.

## Scope & Verification Status
- **Current state**: First-pass complete statement translation (Stage 3) in progress; proofs are currently being formalized bottom-up.
- **Zero-cheat policy**: No custom axioms, no `native_decide`, no `unsafe`, no `partial def`. Only `[propext, Classical.choice, Quot.sound]` will be permitted in `SignedGraphs/AuditAxioms.lean`.

## Check It Yourself
```bash
lake exe cache get
lake build
```
*(Do not run `lake update`; versions are pinned in `lean-toolchain` and `lake-manifest.json`.)*

## Repository Layout
- `SignedGraphs/Basic.lean` — Signed graphs, NOC condition, mod-4 weights, matrix inertia & signature
- `SignedGraphs/LinearAlgebra.lean` — Switching invariance, Sylvester congruence, Weyl monotonicity, Cauchy interlacing
- `SignedGraphs/LocalReductions.lean` — Cut-vertex and degree-2 reductions (Lemmas 2.1–2.2)
- `SignedGraphs/ParityAndCycles.lean` — Parity mechanism & cycle-pair obstructions (Lemmas 3.2–3.4)
- `SignedGraphs/Classification.lean` — 3-connected non-bipartite NOC classification (Theorem 3.1)
- `SignedGraphs/BipartiteLeaves.lean` — Mod-4 path diversity in bipartite R-leaves (Proposition 4.1)
- `SignedGraphs/SchurReductions.lean` — Weighted `K₄` and `Petersen` Schur-complement reductions (Lemmas 5.1–5.2)
- `SignedGraphs/SPQR.lean` — SPQR two-leaf decomposition
- `SignedGraphs/MainTheorem.lean` — Proofs of Theorem 1.2 and Corollary 1.3
- `SignedGraphs/Challenge.lean` — Standalone pure-Mathlib statement of Theorem 1.2 and Corollary 1.3
- `SignedGraphs/AuditAxioms.lean` — `#print axioms` audit
- `PROOF-PATH.md` / `EXTERNAL-AXIOMS.md` / `PROGRESS.md` — Correspondence, axiom, and progress records
