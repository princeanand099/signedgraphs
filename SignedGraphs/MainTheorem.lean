import SignedGraphs.LocalReductions
import SignedGraphs.SchurReductions
import SignedGraphs.SPQR
import SignedGraphs.Challenge

/-!
# Proofs of Theorem 1.2 and Corollary 1.3 (Section 6)

Combines Sections 2–5 via the SPQR-tree decomposition to prove `theorem_1_2`
and `corollary_1_3`.
-/

open Matrix SimpleGraph

namespace SignedGraphs

/-- **Theorem 1.2**: Every real symmetric zero-diagonal NOC matrix `A` satisfies `s(A) ≤ 0`. -/
theorem theorem_1_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0) (hnoc : MatrixIsNOC A hA.isSymm) :
    signature A hA ≤ 0 := by
  sorry

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem corollary_1_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    -(Challenge.cycleCountMod4 G 3 : ℤ) ≤
      Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
    Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤
      (Challenge.cycleCountMod4 G 1 : ℤ) := by
  sorry

end SignedGraphs
