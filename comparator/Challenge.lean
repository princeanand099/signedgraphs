import ChallengeDefs

/-!
# Comparator Challenge Statements: Ma–Yang–Li Signature Conjecture

Pure-Mathlib statement file for `lake comparator`. The `sorry` proofs below are
intentional: `lake comparator` verifies that `Solution` proves these exact types
over the identical definitions from `ChallengeDefs` using only
`[propext, Quot.sound, Classical.choice]`.
-/

open Matrix SimpleGraph

namespace SignedGraphs.Challenge

/-- **Theorem 1.2 (Main Theorem)**: Every real symmetric zero-diagonal matrix `A` whose
underlying signed graph is NOC satisfies `s(A) ≤ 0`. -/
theorem main_theorem_noc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0)
    (hnoc : ∀ (v : Fin n) (c : (adjGraph A hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) :
    matSig A hA ≤ 0 := by
  sorry

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem ma_yang_li_conjecture {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    -(cycleCountMod4 G 3 : ℤ) ≤
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
    matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤
      (cycleCountMod4 G 1 : ℤ) := by
  sorry

end SignedGraphs.Challenge
