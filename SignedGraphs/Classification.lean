import SignedGraphs.ParityAndCycles

/-!
# Classification of 3-Connected Non-Bipartite NOC Signed Graphs (Section 3)

Formalization of **Theorem 3.1**: Every 3-connected non-bipartite NOC signed graph is
switching-isomorphic to either `(K₄, +1)` or `(Petersen, -1)`.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 3.1**: Every 3-connected non-bipartite NOC signed graph `(G, σ)` is
switching-isomorphic to either `(K₄, +1)` or `(Petersen, -1)`. -/
theorem three_connected_non_bipartite_noc_classification (S : SignedGraph V)
    (hcard : 4 ≤ Fintype.card V)
    (hconn : S.graph.Preconnected)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnonbip : ¬ S.graph.IsBipartite)
    (hnoc : IsNOC S) :
    SwitchingIso S k4SignedGraph ∨ SwitchingIso S petersenSignedGraph := by
  sorry

end SignedGraphs
