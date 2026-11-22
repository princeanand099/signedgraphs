import SignedGraphs.BipartiteLeaves

/-!
# SPQR-Tree Leaf Decomposition for 2-Connected Graphs (Section 2.3 & Section 6)

Formalizes the structural consequence of Tutte's SPQR decomposition used in Section 6:
any 2-connected simple graph `G` with `δ(G) ≥ 3` that is not 3-connected admits two
disjoint R-node leaves `(H, x, y)` and `(H', x', y')` whose torsos `H + xy` and `H' + x'y'`
are 3-connected simple graphs.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An R-node leaf decomposition `G = H ∪ G₂` across a 2-cut `{x, y}` where `T = H + xy`
is a 3-connected simple graph with `|V(H)| ≥ 4` and `xy ∉ E(H)`. -/
structure RLeafDecomp (G : SimpleGraph V) where
  VH : Finset V
  VG₂ : Finset V
  x : V
  y : V
  hxy : x ≠ y
  hunion : VH ∪ VG₂ = Finset.univ
  hinter : VH ∩ VG₂ = {x, y}
  hcardH : 4 ≤ VH.card
  hcardG₂ : 3 ≤ VG₂.card
  hno_cross : ∀ u ∈ VH, ∀ w ∈ VG₂, u ≠ x → u ≠ y → w ≠ x → w ≠ y → ¬ G.Adj u w
  hT_3conn : ∀ A : Finset VH, A.card ≤ 2 →
    (((G.induce (VH : Set V)) ⊔ SimpleGraph.fromRel (fun a b : VH =>
      (a.1 = x ∧ b.1 = y) ∨ (a.1 = y ∧ b.1 = x))).induce (Aᶜ : Set VH)).Preconnected

/-- **SPQR Two-Leaf Theorem (Section 6)**: If `G` is 2-connected with `δ(G) ≥ 3` and is not
3-connected, then `G` has two R-node leaves `μ, μ'` whose interiors are disjoint (`H' ⊆ G₂`). -/
theorem two_r_leaves_of_two_connected_min_deg_three (G : SimpleGraph V)
    (hcard : 4 ≤ Fintype.card V)
    (hconn : G.Preconnected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hnot3 : ¬ ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected) :
    ∃ d₁ d₂ : RLeafDecomp G, d₁.VH ⊆ d₂.VG₂ ∧ d₂.VH ⊆ d₁.VG₂ := by
  sorry

end SignedGraphs
