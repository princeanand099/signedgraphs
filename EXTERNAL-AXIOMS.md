# External Axioms Audit — `signedgraphs`

**Custom / external axioms used: NONE (0).**

Every theorem in this repository is proved unconditionally from standard Lean 4 and Mathlib4 foundations. Verified by `SignedGraphs/AuditAxioms.lean` in CI log [`c21bc128`](https://github.com/princeanand099/signedgraphs/commit/c21bc1287900f4ed3a7dec02e47ec059e9652082) (commit [`78557719`](https://github.com/princeanand099/signedgraphs/commit/7855771937371ad718a0dab064092640f2490f1e)):

```
'SignedGraphs.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.corollary_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.main_theorem_noc' depends on axioms: [propext, Classical.choice, Quot.sound]
'SignedGraphs.Challenge.ma_yang_li_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```
