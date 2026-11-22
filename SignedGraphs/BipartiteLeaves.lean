import SignedGraphs.Classification

/-!
# Bipartite R-Node Leaves and Signed Path Weights (Section 4)

Formalization of **Proposition 4.1**: If `T = H + xy` is a 3-connected simple graph with
`H = T - xy` bipartite, then for every signing `σ` of `H`, there exist two `(x, y)`-paths
`P₁, P₂` in `H` whose mod-4 weights differ by `2` in `ZMod 4`.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Proposition 4.1 (Mod-4 path-weight diversity in bipartite R-leaves)**:
Let `T` be a 3-connected simple graph on `V` with `xy ∈ E(T)` such that `H = T - xy`
is bipartite, and let `σ` be any signing of `H`. Then `H` contains two simple `(x, y)`-paths
`P₁, P₂` such that `w_σ(P₁) - w_σ(P₂) = 2` in `ZMod 4`. -/
theorem bipartite_r_leaf_path_diversity (T : SimpleGraph V)
    (hcard : 4 ≤ Fintype.card V)
    (hconn : T.Preconnected)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (T.induce (Aᶜ : Set V)).Preconnected)
    (x y : V) (hxy : T.Adj x y)
    (H : SimpleGraph V) (hH : H = T.deleteEdges {s(x, y)})
    (hbip : H.IsBipartite)
    (σ : Sym2 V → ℤ) (hσ : ∀ e ∈ H.edgeSet, σ e = 1 ∨ σ e = -1) :
    ∃ (p₁ p₂ : H.Walk x y), p₁.IsPath ∧ p₂.IsPath ∧
      walkModFourWeight σ p₁ - walkModFourWeight σ p₂ = 2 := by
  sorry

end SignedGraphs
