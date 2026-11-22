import SignedGraphs.Basic

/-!
# Parity Mechanism, Maximal Even Cycles, and Cycle-Pair Obstructions (Section 3)

Formalization of:
- Equation (3.1): Mod-4 arc-weight difference along an even cycle.
- Lemma 3.2: Gao–Li–Ma–Xie maximal even-cycle lemma.
- Lemma 3.3: Even-odd cycle linkage obstruction.
- Lemma 3.4: Cycle-pair obstructions (1), (2), and (3) forcing `(Petersen, -1)`.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Canonical 4-vertex complete graph `(K₄, +1)`. -/
def k4SignedGraph : SignedGraph (Fin 4) where
  graph := ⊤
  sign _ := 1
  sign_pm_one _ _ := Or.inl rfl

/-- Canonical Petersen graph on `Fin 10` with all-negative signing `(Petersen, -1)`:
outer 5-cycle `0-1-2-3-4-0`, inner 5-cycle `5-7-9-6-8-5`, spokes `i-(i+5)`. -/
def petersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun i j =>
    (i.val < 5 ∧ j.val < 5 ∧ (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val ∧
      ((j.val - 5) = ((i.val - 5) + 2) % 5 ∨ (i.val - 5) = ((j.val - 5) + 2) % 5)) ∨
    (i.val < 5 ∧ j.val = i.val + 5) ∨
    (j.val < 5 ∧ i.val = j.val + 5)

/-- The all-negative Petersen signed graph `(Petersen, -1)`. -/
def petersenSignedGraph : SignedGraph (Fin 10) where
  graph := petersenGraph
  sign _ := -1
  sign_pm_one _ _ := Or.inr rfl

/-- Two signed graphs `(G₁, σ₁)` and `(G₂, σ₂)` are switching-isomorphic if there is a
graph isomorphism `e : G₁ ≃g G₂` and a vertex set `T` such that switching `σ₁` at `T`
matches `σ₂` along `e`. -/
def SwitchingIso {V W : Type*} (S₁ : SignedGraph V) (S₂ : SignedGraph W) : Prop :=
  ∃ (e : S₁.graph ≃g S₂.graph) (T : Set V),
    ∀ u v, S₁.graph.Adj u v →
      (if u ∈ T then -1 else 1) * (if v ∈ T then -1 else 1) * S₁.sign s(u, v) =
        S₂.sign s(e u, e v)

/-- **Equation (3.1)**: For any even cycle `C₁` partitioned at `u, v` into two `(u, v)`-arcs
`p₁, p₂`, `w(p₁) - w(p₂) = w(C₁) + 2 * (p₂.length : ZMod 4)` in `ZMod 4`. -/
theorem even_cycle_arc_weight_diff {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v : V} (p₁ p₂ : G.Walk u v) (heven : Even (p₁.length + p₂.length)) :
    walkModFourWeight σ p₁ - walkModFourWeight σ p₂ =
      (walkModFourWeight σ p₁ + walkModFourWeight σ p₂) + 2 * (p₂.length : ZMod 4) := by
  sorry

/-- **Lemma 3.3 (Even-odd cycle linkage)**: If an even cycle `C₁` and an odd cycle `C₂`
are linked by two disjoint paths (or one path when sharing a single vertex `u₁`) with
`w(C₁) + 2 * d(u₁, u₂) = 2` in `ZMod 4`, then `(G, σ)` is not NOC. -/
theorem even_odd_cycle_linkage (S : SignedGraph V)
    {u₁ u₂ : V} (p₁ p₂ : S.graph.Walk u₁ u₂)
    (heven : Even (p₁.length + p₂.length))
    (q : S.graph.Walk u₁ u₂) (hdisj : ∀ x ∈ q.support, x ≠ u₁ → x ≠ u₂ →
      x ∉ p₁.support ∧ x ∉ p₂.support)
    (hq_parity : Odd (q.length + p₂.length))
    (hw : (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) +
      2 * (p₂.length : ZMod 4) = 2) :
    ¬ IsNOC S := by
  sorry

/-- **Lemma 3.4 (Cycle-pair obstructions)** in a 3-connected NOC signed graph `(G, σ)`:
(1) no disjoint even and odd cycles;
(2) no even and odd cycles meeting in exactly one vertex;
(3) two vertex-disjoint odd cycles force `(G, σ)` to be switching-isomorphic to `(Petersen, -1)`. -/
theorem cycle_pair_obstructions_disjoint_even_odd (S : SignedGraph V)
    (hconn : S.graph.Preconnected) (h3 : ∀ A : Finset V, A.card ≤ 2 →
      (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {v₁ v₂ : V} (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hdisj : Disjoint c₁.support.toFinset c₂.support.toFinset) :
    False := by
  sorry

theorem cycle_pair_obstructions_one_vertex_even_odd (S : SignedGraph V)
    (hconn : S.graph.Preconnected) (h3 : ∀ A : Finset V, A.card ≤ 2 →
      (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {u v₁ v₂ : V} (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hinter : c₁.support.toFinset ∩ c₂.support.toFinset = {u}) :
    False := by
  sorry

theorem cycle_pair_obstructions_two_disjoint_odd (S : SignedGraph V)
    (hconn : S.graph.Preconnected) (h3 : ∀ A : Finset V, A.card ≤ 2 →
      (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {v₁ v₂ : V} (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (hodd₁ : Odd c₁.length) (hodd₂ : Odd c₂.length)
    (hdisj : Disjoint c₁.support.toFinset c₂.support.toFinset) :
    SwitchingIso S petersenSignedGraph := by
  sorry

end SignedGraphs
