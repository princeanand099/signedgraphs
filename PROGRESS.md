# Formalization Progress (`SignedGraphs`)

- **Current Stage**: Stage 3 (Complete First-Pass Translation & Statement Verification)
- **Toolchain**: `leanprover/lean4:v4.35.0` / Mathlib `v4.35.0`
- **Proved Declarations**:
  - `SignedGraphs.inertia_sum` (`SignedGraphs/Basic.lean`)
- **Remaining `sorry`s**:
  - Stage 3 first-pass translation skeletons in `Basic.lean` (1), `LinearAlgebra.lean` (6), `LocalReductions.lean` (2), `ParityAndCycles.lean` (5), `Classification.lean` (1), `BipartiteLeaves.lean` (1), `SchurReductions.lean` (5), `SPQR.lean` (1), `MainTheorem.lean` (2), `Challenge.lean` (2).
- **Next Concrete Steps**:
  1. Inspect `ci-logs` to confirm Stage 3 first-pass translation compiles cleanly with zero type/syntax errors.
  2. Eliminate `sorry`s in dependency order: Batch 1 (`Basic.lean`, `LinearAlgebra.lean`), Batch 2 (`LocalReductions.lean`), Batch 3 (`ParityAndCycles.lean`, `Classification.lean`), Batch 4 (`BipartiteLeaves.lean`, `SchurReductions.lean`), Batch 5 (`SPQR.lean`, `MainTheorem.lean`, `Challenge.lean`).
