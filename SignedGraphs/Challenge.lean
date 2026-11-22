import Mathlib

/-!
# Challenge Statements: Ma–Yang–Li Signature Conjecture

Immutable public theorem statements using only core Lean and Mathlib definitions.
- `main_theorem_noc`: Theorem 1.2 (for every real symmetric zero-diagonal NOC matrix `A`, `s(A) ≤ 0`).
- `ma_yang_li_conjecture`: Corollary 1.3 (for every finite simple graph `G`, `-c₃(G) ≤ s(G) ≤ c₅(G)`).
-/

open Matrix SimpleGraph

namespace SignedGraphs.Challenge

/-- For a real symmetric matrix `A` over `Fin n`, its signature is `n₊(A) - n₋(A)`. -/
noncomputable def matSig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) : ℤ :=
  ((Finset.univ.filter fun i : Fin n => 0 < hA.eigenvalues i).card : ℤ) -
  ((Finset.univ.filter fun i : Fin n => hA.eigenvalues i < 0).card : ℤ)

/-- Underlying graph of a real symmetric matrix `A` on `Fin n`: `i ~ j` iff `i ≠ j ∧ A i j ≠ 0`. -/
def adjGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A i j ≠ 0
  symm i j h := ⟨h.1.symm, by simpa [congrFun (congrFun hA j) i] using h.2⟩
  loopless i h := h.1 rfl

/-- Sign product along a walk in `Fin n`. -/
def walkEntrySignProd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {G : SimpleGraph (Fin n)} :
    ∀ {u v : Fin n}, G.Walk u v → ℤ
  | _, _, .nil => 1
  | u, _, .cons (v := w) _ p => (if 0 < A u w then 1 else -1) * walkEntrySignProd A p

/-- **Theorem 1.2 (Main Theorem)**: Every real symmetric zero-diagonal matrix `A` whose
underlying signed graph is NOC satisfies `s(A) ≤ 0`. -/
theorem main_theorem_noc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0)
    (hnoc : ∀ (v : Fin n) (c : (adjGraph A hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) :
    matSig A hA ≤ 0 := by
  sorry

/-- Number of simple cycle edge-sets in `G` of length congruent to `r` modulo `4`. -/
noncomputable def cycleCountMod4 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
    ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r).card

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem ma_yang_li_conjecture {n : ℕ} (G : SimpleGraph (Fin n)) :
    -(cycleCountMod4 G 3 : ℤ) ≤
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G ℝ) ∧
    matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G ℝ) ≤
      (cycleCountMod4 G 1 : ℤ) := by
  sorry

end SignedGraphs.Challenge
