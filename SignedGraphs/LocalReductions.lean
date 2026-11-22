import SignedGraphs.LinearAlgebra

/-!
# Local Algebraic Reductions (Section 2.2)

Formalization of:
- `cut_vertex_reduction` (Lemma 2.1): Cut-vertex decomposition via Schur complement / decoupling.
- `degree_two_reduction` (Lemma 2.2): Degree-2 vertex elimination via hyperbolic 2×2 block & Weyl.
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 2.1 (Cut-vertex reduction)**: If `v` is a cut-vertex decomposing `G` into two
induced subgraphs `G₁, G₂` on `V₁, V₂` with `V₁ ∩ V₂ = {v}`, `|V₁| < |V|`, `|V₂| < |V|`,
and Theorem 1.2 holds for all NOC matrices of order strictly less than `|V|`, then `s(A) ≤ 0`. -/
theorem cut_vertex_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (v : V) (V₁ V₂ : Finset V)
    (hunion : V₁ ∪ V₂ = Finset.univ)
    (hinter : V₁ ∩ V₂ = {v})
    (hcard₁ : V₁.card < Fintype.card V)
    (hcard₂ : V₂.card < Fintype.card V)
    (hno_cross : ∀ u ∈ V₁, ∀ w ∈ V₂, u ≠ v → w ≠ v → A u w = 0)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W < Fintype.card V →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ x, B x x = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  sorry

/-- **Lemma 2.2 (Degree-2 vertex reduction)**: If `v` has degree 2 in `G(A)` (with `|V| ≥ 3`)
and Theorem 1.2 holds for all NOC matrices of order `|V| - 2`, then `s(A) ≤ 0`. -/
theorem degree_two_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (hn : 3 ≤ Fintype.card V)
    (v x y : V) (hxy : x ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (hN : ∀ w : V, (matrixGraph A hA.isSymm).Adj v w ↔ w = x ∨ w = y)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W = Fintype.card V - 2 →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ z, B z z = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  sorry

end SignedGraphs
