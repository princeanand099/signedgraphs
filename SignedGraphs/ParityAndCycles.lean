import SignedGraphs.Basic

/-!
# Parity Mechanism, Maximal Even Cycles, and Cycle-Pair Obstructions (Section 3)

Formalization of:
- Equation (3.1): Mod-4 arc-weight difference along an even cycle.
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
def SwitchingIso {V W : Type*} [Fintype V] [DecidableEq V]
    (S₁ : SignedGraph V) (S₂ : SignedGraph W) : Prop :=
  ∃ (e : S₁.graph ≃g S₂.graph) (T : Finset V),
    ∀ u v, S₁.graph.Adj u v →
      (if u ∈ T then -1 else 1) * (if v ∈ T then -1 else 1) * S₁.sign s(u, v) =
        S₂.sign s(e u, e v)

omit [Fintype V] [DecidableEq V] in
private lemma two_mul_modFourWeight (σ : Sym2 V → ℤ) (e : Sym2 V) :
    2 * modFourWeight σ e = 2 := by
  unfold modFourWeight
  split_ifs <;> decide

omit [Fintype V] [DecidableEq V] in
private lemma two_mul_walkModFourWeight {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v : V} (p : G.Walk u v) :
    2 * walkModFourWeight σ p = 2 * (p.length : ZMod 4) := by
  unfold walkModFourWeight
  rw [← SimpleGraph.Walk.length_edges p]
  induction p.edges with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [mul_add, mul_add, two_mul_modFourWeight, ih]
    ring

omit [Fintype V] [DecidableEq V] in
/-- Mod-4 weight is additive under walk concatenation. -/
lemma walkModFourWeight_append {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkModFourWeight σ (p.append q) = walkModFourWeight σ p + walkModFourWeight σ q := by
  simp [walkModFourWeight, SimpleGraph.Walk.edges_append]

omit [Fintype V] [DecidableEq V] in
/-- Mod-4 weight is invariant under walk reversal. -/
lemma walkModFourWeight_reverse {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v : V} (p : G.Walk u v) :
    walkModFourWeight σ p.reverse = walkModFourWeight σ p := by
  simp [walkModFourWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]

omit [Fintype V] [DecidableEq V] in
/-- **Equation (3.1)**: For any two `(u, v)`-walks `p₁, p₂`,
`w(p₁) - w(p₂) = (w(p₁) + w(p₂)) + 2 * (p₂.length : ZMod 4)` in `ZMod 4`. -/
theorem even_cycle_arc_weight_diff {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v : V} (p₁ p₂ : G.Walk u v) :
    walkModFourWeight σ p₁ - walkModFourWeight σ p₂ =
      (walkModFourWeight σ p₁ + walkModFourWeight σ p₂) + 2 * (p₂.length : ZMod 4) := by
  have h2 : 2 * walkModFourWeight σ p₂ = 2 * (p₂.length : ZMod 4) :=
    two_mul_walkModFourWeight σ p₂
  have h4 : (4 : ZMod 4) = 0 := rfl
  calc
    walkModFourWeight σ p₁ - walkModFourWeight σ p₂
      = (walkModFourWeight σ p₁ + walkModFourWeight σ p₂) - 2 * walkModFourWeight σ p₂ := by ring
    _ = (walkModFourWeight σ p₁ + walkModFourWeight σ p₂) - 2 * (p₂.length : ZMod 4) := by rw [h2]
    _ = (walkModFourWeight σ p₁ + walkModFourWeight σ p₂) + 2 * (p₂.length : ZMod 4) := by
      have hneg : -(2 * (p₂.length : ZMod 4)) = 2 * (p₂.length : ZMod 4) := by
        have : (4 : ZMod 4) * (p₂.length : ZMod 4) = 0 := by rw [h4, zero_mul]
        linear_combination -this
      rw [sub_eq_add_neg, hneg]

omit [Fintype V] [DecidableEq V] in
private lemma path_length_eq_one_of_edge_endpoints {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (he : s(u, v) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at he
  | @cons _ w _ hadj q =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with heq | hq
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨huv, _⟩
      · cases q with
        | nil => rfl
        | cons hadj' q' =>
          have hnd := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
          have hv_mem : v ∈ (SimpleGraph.Walk.cons hadj' q').support :=
            SimpleGraph.Walk.end_mem_support _
          exact absurd (by simp [hv_mem]) hnd.2.1
      · exact absurd huv (G.ne_of_adj hadj)
    · have hu_mem : u ∈ q.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges q hq
      have hnd := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact absurd hu_mem hnd.1

omit [Fintype V] [DecidableEq V] in
/-- Two internally vertex-disjoint simple `(u₁, u₂)`-paths whose lengths sum to at least `3`
form a simple cycle `q.append p.reverse`. -/
lemma isCycle_append_reverse_of_disjoint {G : SimpleGraph V} {u₁ u₂ : V}
    (p q : G.Walk u₁ u₂) (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x ∈ q.support, x ≠ u₁ → x ≠ u₂ → x ∉ p.support)
    (hlen : 3 ≤ q.length + p.length) :
    (q.append p.reverse).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_append, List.nodup_append]
    refine ⟨hq.isTrail.edges_nodup, hp.reverse.isTrail.edges_nodup, ?_⟩
    intro e heq e' hep hne
    subst hne
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hep
    rcases e with ⟨a, b⟩
    have ha_q : a ∈ q.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges q heq
    have hb_q : b ∈ q.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges q heq
    have ha_p : a ∈ p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges p hep
    have hb_p : b ∈ p.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges p hep
    have hab : a ≠ b := G.ne_of_adj (SimpleGraph.Walk.adj_of_mem_edges q heq)
    have ha_end : a = u₁ ∨ a = u₂ := by
      by_contra h
      push Not at h
      exact hdisj a ha_q h.1 h.2 ha_p
    have hb_end : b = u₁ ∨ b = u₂ := by
      by_contra h
      push Not at h
      exact hdisj b hb_q h.1 h.2 hb_p
    have he_eq : s(a, b) = s(u₁, u₂) := by
      rcases ha_end with rfl | rfl <;> rcases hb_end with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hab
    rw [he_eq] at heq hep
    have hq1 := path_length_eq_one_of_edge_endpoints q hq heq
    have hp1 := path_length_eq_one_of_edge_endpoints p hp hep
    omega
  · intro hnil
    have h0 : (q.append p.reverse).length = 0 := by rw [hnil]; rfl
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at h0
    omega
  · rw [SimpleGraph.Walk.support_append]
    have hq_cons : q.support = u₁ :: q.support.tail := by
      cases q <;> simp
    have hp_cons : p.reverse.support = u₂ :: p.reverse.support.tail := by
      cases hr : p.reverse <;> simp
    have htail : (q.support ++ p.reverse.support.tail).tail =
        q.support.tail ++ p.reverse.support.tail := by
      rw [hq_cons]; rfl
    rw [htail, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have hnd := hq.support_nodup
      rw [hq_cons, List.nodup_cons] at hnd
      exact hnd.2
    · have hnd := hp.reverse.support_nodup
      rw [hp_cons, List.nodup_cons] at hnd
      exact hnd.2
    · intro x hxq y hxp hxy
      subst hxy
      have hndq := hq.support_nodup
      rw [hq_cons, List.nodup_cons] at hndq
      have hxu₁ : x ≠ u₁ := fun h => hndq.1 (h ▸ hxq)
      have hndp := hp.reverse.support_nodup
      rw [hp_cons, List.nodup_cons] at hndp
      have hxu₂ : x ≠ u₂ := fun h => hndp.1 (h ▸ hxp)
      have hxq' : x ∈ q.support := by rw [hq_cons]; exact List.mem_cons_of_mem _ hxq
      have hxp' : x ∈ p.support := by
        have : x ∈ p.reverse.support := by rw [hp_cons]; exact List.mem_cons_of_mem _ hxp
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
      exact hdisj x hxq' hxu₁ hxu₂ hxp'

omit [Fintype V] [DecidableEq V] in
/-- **Lemma 3.3 (Even-odd cycle linkage)**: If an even cycle `C₁` partitioned at `u₁ ≠ u₂`
into two simple paths `p₁, p₂` is linked by an internally vertex-disjoint simple path `q`
with `q.length + p₂.length` odd and `w(C₁) + 2 * p₂.length = 2` in `ZMod 4`, then `(G, σ)` is
not NOC. -/
theorem even_odd_cycle_linkage (S : SignedGraph V)
    {u₁ u₂ : V} (hu : u₁ ≠ u₂)
    (p₁ p₂ : S.graph.Walk u₁ u₂) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (heven : Even (p₁.length + p₂.length))
    (q : S.graph.Walk u₁ u₂) (hq : q.IsPath)
    (hdisj : ∀ x ∈ q.support, x ≠ u₁ → x ≠ u₂ → x ∉ p₁.support ∧ x ∉ p₂.support)
    (hq_parity : Odd (q.length + p₂.length))
    (hw : (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) +
      2 * (p₂.length : ZMod 4) = 2) :
    ¬ IsNOC S := by
  intro hnoc
  have hmod4 : IsNOCModFour S := (isNOC_iff_isNOCModFour S).mp hnoc
  have hp₁_pos : 1 ≤ p₁.length := by
    cases p₁ with
    | nil => exact absurd rfl hu
    | cons _ _ => simp
  have hp₂_pos : 1 ≤ p₂.length := by
    cases p₂ with
    | nil => exact absurd rfl hu
    | cons _ _ => simp
  have hq_pos : 1 ≤ q.length := by
    cases q with
    | nil => exact absurd rfl hu
    | cons _ _ => simp
  have hodd₁ : Odd (q.length + p₁.length) := by
    rcases heven with ⟨a, ha⟩
    rcases hq_parity with ⟨b, hb⟩
    refine ⟨b + a - p₂.length, ?_⟩
    omega
  have hlen₁ : 3 ≤ q.length + p₁.length := by
    rcases hodd₁ with ⟨k, hk⟩; omega
  have hlen₂ : 3 ≤ q.length + p₂.length := by
    rcases hq_parity with ⟨k, hk⟩; omega
  have hc₁ : (q.append p₁.reverse).IsCycle :=
    isCycle_append_reverse_of_disjoint p₁ q hp₁ hq (fun x hx h1 h2 => (hdisj x hx h1 h2).1) hlen₁
  have hc₂ : (q.append p₂.reverse).IsCycle :=
    isCycle_append_reverse_of_disjoint p₂ q hp₂ hq (fun x hx h1 h2 => (hdisj x hx h1 h2).2) hlen₂
  have hw₁ : walkModFourWeight S.sign (q.append p₁.reverse) = 3 :=
    hmod4 u₁ (q.append p₁.reverse) hc₁ (by simpa [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse] using hodd₁)
  have hw₂ : walkModFourWeight S.sign (q.append p₂.reverse) = 3 :=
    hmod4 u₁ (q.append p₂.reverse) hc₂ (by simpa [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse] using hq_parity)
  rw [walkModFourWeight_append, walkModFourWeight_reverse] at hw₁ hw₂
  have hdiff : walkModFourWeight S.sign p₁ - walkModFourWeight S.sign p₂ = 0 := by
    linear_combination hw₁ - hw₂
  have heq := even_cycle_arc_weight_diff S.sign p₁ p₂
  rw [hdiff, hw] at heq
  exact absurd heq (by decide)

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
