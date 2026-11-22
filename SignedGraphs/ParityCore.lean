import SignedGraphs.Basic
import SignedGraphs.GraphTools

/-!
# Parity Mechanism Core (Section 3)

Formalization of:
- Canonical `k4SignedGraph`, `petersenGraph`, `petersenSignedGraph`, `SwitchingIso`.
- Equation (3.1): Mod-4 arc-weight difference along an even cycle.
- Lemma 3.3: Even-odd cycle linkage obstructions (`even_odd_cycle_linkage`, disjoint & 1-vertex).
- Even-cycle bipartition, arc splitting, `K₄` pair-path weights, and cycle helpers.
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
lemma two_mul_modFourWeight (σ : Sym2 V → ℤ) (e : Sym2 V) :
    2 * modFourWeight σ e = 2 := by
  unfold modFourWeight
  split_ifs <;> decide

omit [Fintype V] [DecidableEq V] in
lemma two_mul_walkModFourWeight {G : SimpleGraph V} (σ : Sym2 V → ℤ)
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
    have heq' : s(u₁, u₂) ∈ q.edges := he_eq ▸ heq
    have hep' : s(u₁, u₂) ∈ p.edges := he_eq ▸ hep
    have hq1 := path_length_eq_one_of_edge_endpoints q hq heq'
    have hp1 := path_length_eq_one_of_edge_endpoints p hp hep'
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

omit [Fintype V] [DecidableEq V] in
lemma isPath_append_of_disjoint_pc {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x ∈ p.support, x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  refine SimpleGraph.Walk.IsPath.mk' ?_
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  have hq_cons : q.support = b :: q.support.tail := by cases q <;> simp
  have hq_nd := hq.support_nodup
  rw [hq_cons, List.nodup_cons] at hq_nd
  refine ⟨hp.support_nodup, hq_nd.2, ?_⟩
  intro x hxp y hyq hxy
  subst hxy
  have hxb : x = b := hdisj x hxp (by rw [hq_cons]; exact List.mem_cons_of_mem _ hyq)
  subst hxb
  exact hq_nd.1 hyq

omit [Fintype V] in
lemma cycle_support_card {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have htail_eq : c.support.toFinset = c.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons _ w _ hadj p =>
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.mem_cons]
      constructor
      · rintro (rfl | hp)
        · exact SimpleGraph.Walk.end_mem_support p
        · exact hp
      · exact Or.inr
  rw [htail_eq, List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
    SimpleGraph.Walk.length_support]
  omega

omit [Fintype V] [DecidableEq V] in
lemma even_cycle_length_ge_four {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (heven : Even c.length) : 4 ≤ c.length := by
  have h3 := hc.three_le_length
  rcases heven with ⟨k, hk⟩
  omega

lemma card_ge_four_of_even_cycle {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (heven : Even c.length) : 4 ≤ Fintype.card V := by
  have h4 := even_cycle_length_ge_four c hc heven
  have hc_le : c.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  rw [cycle_support_card c hc] at hc_le
  omega

lemma min_deg_three_of_three_conn {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected)
    (v : V) : 3 ≤ G.degree v := by
  by_contra hlt
  have hle : (G.neighborFinset v).card ≤ 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  have hsub_lt : (insert v (G.neighborFinset v)).card < Fintype.card V := by
    have h1 : (insert v (G.neighborFinset v)).card ≤ (G.neighborFinset v).card + 1 :=
      Finset.card_insert_le _ _
    omega
  have hex : ∃ w : V, w ∉ insert v (G.neighborFinset v) := by
    by_contra hall
    push Not at hall
    have heq : insert v (G.neighborFinset v) = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [heq, Finset.card_univ] at hsub_lt
    omega
  rcases hex with ⟨w, hw⟩
  simp only [Finset.mem_insert, not_or] at hw
  have hv_mem : v ∈ ((G.neighborFinset v : Set V)ᶜ) := by
    simp [SimpleGraph.mem_neighborFinset]
  have hw_mem : w ∈ ((G.neighborFinset v : Set V)ᶜ) := hw.2
  obtain ⟨p⟩ := h3 (G.neighborFinset v) hle ⟨v, hv_mem⟩ ⟨w, hw_mem⟩
  cases p with
  | nil => exact hw.1 rfl
  | @cons _ u _ hadj _ =>
    have hu_nbr : u.1 ∈ G.neighborFinset v := (G.mem_neighborFinset v u.1).mpr hadj
    exact u.2 hu_nbr

omit [Fintype V] in
lemma walk_exits_finset_pc {G : SimpleGraph V} (S : Finset V) {a b : V}
    (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y ∧ x ∈ p.support ∧ y ∈ p.support := by
  induction p with
  | nil => exact absurd ha hb
  | @cons x y z hxy q ih =>
    by_cases hy : y ∈ S
    · obtain ⟨u, hu, v, hv, huv, hux, huy⟩ := ih hy hb
      exact ⟨u, hu, v, hv, huv, List.mem_cons_of_mem _ hux, List.mem_cons_of_mem _ huy⟩
    · exact ⟨x, ha, y, hy, hxy, List.mem_cons_self ..,
        List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q)⟩

lemma sep_card_ge_three_of_three_conn {G : SimpleGraph V}
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected)
    (K A : Finset V) (u w : V) (hu : u ∈ K) (hwK : w ∉ K) (hwA : w ∉ A)
    (hdisj : Disjoint K A)
    (hclosed : ∀ x ∈ K, ∀ y : V, G.Adj x y → y ∈ K ∪ A) :
    3 ≤ A.card := by
  by_contra hlt
  have hle : A.card ≤ 2 := by omega
  have huA : u ∈ ((A : Set V)ᶜ) := Finset.disjoint_left.mp hdisj hu
  have hwA' : w ∈ ((A : Set V)ᶜ) := hwA
  obtain ⟨p⟩ := h3 A hle ⟨u, huA⟩ ⟨w, hwA'⟩
  let f : (G.induce ((A : Set V)ᶜ)) →g G := (SimpleGraph.Embedding.induce ((A : Set V)ᶜ)).toHom
  obtain ⟨x, hxK, y, hyK, hxy, _, hyp⟩ := walk_exits_finset_pc K (p.map f) hu hwK
  have hmem := hclosed x hxK y hxy
  rw [Finset.mem_union] at hmem
  rcases hmem with h1 | h2
  · exact hyK h1
  · rw [SimpleGraph.Walk.support_map, List.mem_map] at hyp
    rcases hyp with ⟨y', _, hy'eq⟩
    exact y'.2 (hy'eq.symm ▸ h2)

omit [Fintype V] in
private lemma path_takeUntil_adj_length {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), p.IsPath →
      ∀ {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support), s(x, y) ∈ p.edges →
        (p.takeUntil x hx).length + 1 = (p.takeUntil y hy).length ∨
        (p.takeUntil y hy).length + 1 = (p.takeUntil x hx).length
  | _, _, .nil, _, _, _, _, _, he => by simp at he
  | a, _, .cons (v := b) hadj q, hp, x, y, hx, hy, he => by
    have hnd := hp.support_nodup
    rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
    have hq_path : q.IsPath := SimpleGraph.Walk.IsPath.mk' hnd.2
    have ha_nq : a ∉ q.support := hnd.1
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with heq | hq_e
    · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        have hba : b ≠ a := (G.ne_of_adj hadj).symm
        simp [SimpleGraph.Walk.takeUntil_cons, hba]
      · right
        have hba : b ≠ a := (G.ne_of_adj hadj).symm
        simp [SimpleGraph.Walk.takeUntil_cons, hba]
    · have hxq : x ∈ q.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges q hq_e
      have hyq : y ∈ q.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges q hq_e
      have hxa : x ≠ a := fun h => ha_nq (h ▸ hxq)
      have hya : y ≠ a := fun h => ha_nq (h ▸ hyq)
      have ih := path_takeUntil_adj_length q hq_path hxq hyq hq_e
      have hxlen : ((SimpleGraph.Walk.cons hadj q).takeUntil x hx).length =
          (q.takeUntil x hxq).length + 1 := by
        simp [SimpleGraph.Walk.takeUntil_cons, hxa.symm]
      have hylen : ((SimpleGraph.Walk.cons hadj q).takeUntil y hy).length =
          (q.takeUntil y hyq).length + 1 := by
        simp [SimpleGraph.Walk.takeUntil_cons, hya.symm]
      rw [hxlen, hylen]
      omega

omit [Fintype V] in
/-- An even cycle `c` admits a 2-coloring `col : V → ℕ` (taking values in `{0, 1}`) of its edges
such that any walk `q` using only edges of `c` satisfies `(col b + col a + q.length) % 2 = 0`. -/
lemma even_cycle_bipartition {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (heven : Even c.length) :
    ∃ col : V → ℕ,
      (∀ u, col u < 2) ∧
      (∀ x y, s(x, y) ∈ c.edges → col x ≠ col y) ∧
      (∀ {a b : V} (q : G.Walk a b), (∀ e ∈ q.edges, e ∈ c.edges) →
        (col b + col a + q.length) % 2 = 0) := by
  classical
  cases c with
  | nil => exact False.elim (hc.ne_nil rfl)
  | @cons _ w _ hadj p =>
    have hp_nd : p.support.Nodup := by simpa [SimpleGraph.Walk.support_cons] using hc.support_nodup
    have hp : p.IsPath := SimpleGraph.Walk.IsPath.mk' hp_nd
    let col : V → ℕ := fun u =>
      if hu : u ∈ p.support then (p.takeUntil u hu).length % 2 else 0
    have hlt2 : ∀ u, col u < 2 := fun u => by
      dsimp only [col]; split_ifs
      · exact Nat.mod_lt _ (by decide)
      · decide
    have hvalid : ∀ x y, s(x, y) ∈ (SimpleGraph.Walk.cons hadj p).edges → col x ≠ col y := by
      intro x y he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with heq | hp_e
      · have hw_p : w ∈ p.support := SimpleGraph.Walk.start_mem_support p
        have hv_p : v ∈ p.support := SimpleGraph.Walk.end_mem_support p
        have hlen_w : (p.takeUntil w hw_p).length = 0 := by simp
        have hlen_v : (p.takeUntil v hv_p).length = p.length := by
          have hspec := SimpleGraph.Walk.take_spec p hv_p
          have hdrop : p.dropUntil v hv_p = .nil := by
            cases hd : p.dropUntil v hv_p with
            | nil => rfl
            | cons h' r' =>
              exfalso
              have hnd' := hp.support_nodup
              rw [← hspec, hd, SimpleGraph.Walk.support_append, List.nodup_append] at hnd'
              have hv_r' : v ∈ r'.support := SimpleGraph.Walk.end_mem_support r'
              exact hnd'.2.2 v (SimpleGraph.Walk.end_mem_support _) v (by simp [hv_r']) rfl
          rw [hdrop, SimpleGraph.Walk.append_nil] at hspec
          exact congrArg SimpleGraph.Walk.length hspec
        have hodd_p : p.length % 2 = 1 := by
          simp only [SimpleGraph.Walk.length_cons] at heven
          rcases heven with ⟨k, hk⟩; omega
        have hcol_w : col w = 0 := by simp [col, hw_p, hlen_w]
        have hcol_v : col v = 1 := by simp [col, hv_p, hlen_v, hodd_p]
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hcol_v, hcol_w]; decide
        · rw [hcol_w, hcol_v]; decide
      · have hxp : x ∈ p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges p hp_e
        have hyp : y ∈ p.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges p hp_e
        have hdiff := path_takeUntil_adj_length p hp hxp hyp hp_e
        simp only [col, hxp, hyp, dif_pos]
        omega
    refine ⟨col, hlt2, hvalid, ?_⟩
    intro a b q hq
    induction q with
    | nil => simp; omega
    | @cons x y z hxy r ih =>
      have he : s(x, y) ∈ (SimpleGraph.Walk.cons hadj p).edges := hq _ (by simp)
      have hne : col x ≠ col y := hvalid x y he
      have hx2 := hlt2 x
      have hy2 := hlt2 y
      have hr : ∀ e ∈ r.edges, e ∈ (SimpleGraph.Walk.cons hadj p).edges :=
        fun e he' => hq e (by simp [he'])
      have ih' := ih hr
      simp only [SimpleGraph.Walk.length_cons]
      omega

omit [Fintype V] in
/-- Every edge of either arc from `cycle_arcs_of_mem` belongs to `c.edges`. -/
lemma cycle_arcs_edges_subset {G : SimpleGraph V} {v u₁ u₂ : V}
    (c : G.Walk v v) (hc : c.IsCycle)
    (hu₁ : u₁ ∈ c.support) (hu₂ : u₂ ∈ c.support) (hne : u₁ ≠ u₂) :
    ∃ (p₁ p₂ : G.Walk u₁ u₂), p₁.IsPath ∧ p₂.IsPath ∧
      p₁.length + p₂.length = c.length ∧
      (∀ x, x ∈ p₁.support ∨ x ∈ p₂.support ↔ x ∈ c.support) ∧
      (∀ x ∈ p₁.support, x ≠ u₁ → x ≠ u₂ → x ∉ p₂.support) ∧
      (∀ e ∈ p₁.edges, e ∈ c.edges) ∧
      (∀ e ∈ p₂.edges, e ∈ c.edges) ∧
      (∀ σ : Sym2 V → ℤ, walkModFourWeight σ p₁ + walkModFourWeight σ p₂ =
        walkModFourWeight σ c) := by
  let c' : G.Walk u₁ u₁ := c.rotate u₁ hu₁
  have hc' : c'.IsCycle := hc.rotate hu₁
  have hperm : c'.edges.Perm c.edges := by
    have h1 : c = (c.takeUntil u₁ hu₁).append (c.dropUntil u₁ hu₁) := (SimpleGraph.Walk.take_spec c hu₁).symm
    have h2 : c' = (c.dropUntil u₁ hu₁).append (c.takeUntil u₁ hu₁) := rfl
    rw [h2, SimpleGraph.Walk.edges_append]
    conv_rhs => rw [h1, SimpleGraph.Walk.edges_append]
    exact List.perm_append_comm
  have hsupp_eq : ∀ x, x ∈ c'.support ↔ x ∈ c.support := by
    intro x
    have h1 : c' = (c.dropUntil u₁ hu₁).append (c.takeUntil u₁ hu₁) := rfl
    have h2 : c = (c.takeUntil u₁ hu₁).append (c.dropUntil u₁ hu₁) := (SimpleGraph.Walk.take_spec c hu₁).symm
    rw [h1, SimpleGraph.Walk.mem_support_append_iff]
    conv_rhs => rw [h2, SimpleGraph.Walk.mem_support_append_iff]
    exact or_comm
  have hu₂' : u₂ ∈ c'.support := (hsupp_eq u₂).mpr hu₂
  let p₁ : G.Walk u₁ u₂ := c'.takeUntil u₂ hu₂'
  let q₂ : G.Walk u₂ u₁ := c'.dropUntil u₂ hu₂'
  let p₂ : G.Walk u₁ u₂ := q₂.reverse
  have hspec : p₁.append q₂ = c' := SimpleGraph.Walk.take_spec c' hu₂'
  have hlen : p₁.length + p₂.length = c.length := by
    have h1 : p₁.length + q₂.length = c'.length := by rw [← SimpleGraph.Walk.length_append, hspec]
    have h2 : c'.length = c.length := SimpleGraph.Walk.length_rotate c u₁ hu₁
    rw [SimpleGraph.Walk.length_reverse]; omega
  have hp₁_e : ∀ e ∈ p₁.edges, e ∈ c.edges := by
    intro e he
    apply hperm.subset
    rw [← hspec, SimpleGraph.Walk.edges_append, List.mem_append]
    exact Or.inl he
  have hp₂_e : ∀ e ∈ p₂.edges, e ∈ c.edges := by
    intro e he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    apply hperm.subset
    rw [← hspec, SimpleGraph.Walk.edges_append, List.mem_append]
    exact Or.inr he
  have htail_nodup : c'.support.tail.Nodup := hc'.support_nodup
  have hsupp_tail : c'.support.tail = p₁.support.tail ++ q₂.support.tail := by
    conv_lhs => rw [← hspec]
    rw [SimpleGraph.Walk.support_append]
    cases hp₁_eq : p₁ with
    | nil => exact absurd rfl hne
    | cons hadj r => simp [List.cons_append]
  have hp₁_tail_nd : p₁.support.tail.Nodup := (List.nodup_append.mp (hsupp_tail ▸ htail_nodup)).1
  have hq₂_tail_nd : q₂.support.tail.Nodup := (List.nodup_append.mp (hsupp_tail ▸ htail_nodup)).2.1
  have hdisj_tails : ∀ x ∈ p₁.support.tail, ∀ y ∈ q₂.support.tail, x ≠ y :=
    (List.nodup_append.mp (hsupp_tail ▸ htail_nodup)).2.2
  have hu₁_in_q₂_tail : u₁ ∈ q₂.support.tail := by
    cases hq₂_eq : q₂ with
    | nil => exact absurd rfl hne.symm
    | cons hadj r => exact SimpleGraph.Walk.end_mem_support r
  have hp₁_path : p₁.IsPath := by
    refine SimpleGraph.Walk.IsPath.mk' ?_
    have hp₁_cons : p₁.support = u₁ :: p₁.support.tail := by cases p₁ <;> simp
    rw [hp₁_cons, List.nodup_cons]
    exact ⟨fun hm => hdisj_tails u₁ hm u₁ hu₁_in_q₂_tail rfl, hp₁_tail_nd⟩
  have hu₂_in_p₁_tail : u₂ ∈ p₁.support.tail := by
    cases hp₁_eq : p₁ with
    | nil => exact absurd rfl hne
    | cons hadj r => exact SimpleGraph.Walk.end_mem_support r
  have hq₂_path : q₂.IsPath := by
    refine SimpleGraph.Walk.IsPath.mk' ?_
    have hq₂_cons : q₂.support = u₂ :: q₂.support.tail := by cases q₂ <;> simp
    rw [hq₂_cons, List.nodup_cons]
    exact ⟨fun hm => hdisj_tails u₂ hu₂_in_p₁_tail u₂ hm rfl, hq₂_tail_nd⟩
  refine ⟨p₁, p₂, hp₁_path, hq₂_path.reverse, hlen, ?_, ?_, hp₁_e, hp₂_e, ?_⟩
  · intro x
    rw [← hsupp_eq x, ← hspec, SimpleGraph.Walk.mem_support_append_iff]
    simp [p₂, SimpleGraph.Walk.support_reverse]
  · intro x hxp₁ hx1 hx2 hxp₂
    have hxp₁_tail : x ∈ p₁.support.tail := by
      have hp₁_cons : p₁.support = u₁ :: p₁.support.tail := by cases p₁ <;> simp
      rw [hp₁_cons, List.mem_cons] at hxp₁; exact hxp₁.resolve_left hx1
    have hxq₂ : x ∈ q₂.support := by simpa [p₂, SimpleGraph.Walk.support_reverse] using hxp₂
    have hxq₂_tail : x ∈ q₂.support.tail := by
      have hq₂_cons : q₂.support = u₂ :: q₂.support.tail := by cases q₂ <;> simp
      rw [hq₂_cons, List.mem_cons] at hxq₂; exact hxq₂.resolve_left hx2
    exact hdisj_tails x hxp₁_tail x hxq₂_tail rfl
  · intro σ
    have hadd : walkModFourWeight σ (p₁.append q₂) = walkModFourWeight σ p₁ + walkModFourWeight σ q₂ :=
      walkModFourWeight_append σ p₁ q₂
    have hrev : walkModFourWeight σ p₂ = walkModFourWeight σ q₂ := walkModFourWeight_reverse σ q₂
    rw [hrev, ← hadd, hspec]
    exact walkModFourWeight_rotate σ c hu₁

omit [Fintype V] in
/-- **Lemma 3.3(a)**: Disjoint even cycle `c₁` and odd cycle `c₂` linked by two vertex-disjoint
paths `P₁ : u₁ → w₁`, `P₂ : u₂ → w₂` (internally disjoint from `c₁ ∪ c₂`) with
`w(c₁) + 2 * d(u₁, u₂) = 2 (mod 4)` cannot occur in an NOC signed graph. -/
lemma even_odd_cycle_linkage_disjoint (S : SignedGraph V)
    {v₁ v₂ u₁ u₂ w₁ w₂ : V}
    (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hdisjC : ∀ x ∈ c₁.support, x ∉ c₂.support)
    (hu₁ : u₁ ∈ c₁.support) (hu₂ : u₂ ∈ c₁.support) (hu : u₁ ≠ u₂)
    (hw₁ : w₁ ∈ c₂.support) (hw₂ : w₂ ∈ c₂.support) (hw : w₁ ≠ w₂)
    (P₁ : S.graph.Walk u₁ w₁) (P₂ : S.graph.Walk u₂ w₂)
    (hP₁ : P₁.IsPath) (hP₂ : P₂.IsPath)
    (hP_disj : ∀ x ∈ P₁.support, x ∉ P₂.support)
    (hP₁_int : ∀ x ∈ P₁.support, x ≠ u₁ → x ≠ w₁ → x ∉ c₁.support ∧ x ∉ c₂.support)
    (hP₂_int : ∀ x ∈ P₂.support, x ≠ u₂ → x ≠ w₂ → x ∉ c₁.support ∧ x ∉ c₂.support)
    (p₁ p₂ : S.graph.Walk u₁ u₂) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hp_len : p₁.length + p₂.length = c₁.length)
    (hp_supp : ∀ x, x ∈ p₁.support ∨ x ∈ p₂.support ↔ x ∈ c₁.support)
    (hw_eq : (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) +
      2 * (p₂.length : ZMod 4) = 2) :
    ¬ IsNOC S := by
  obtain ⟨q₁, q₂, hq₁, hq₂, hq_len, hq_supp, _, _⟩ :=
    cycle_arcs_of_mem c₂ hc₂ hw₁ hw₂ hw
  have hbuild : ∀ (q : S.graph.Walk w₁ w₂), q.IsPath → (∀ x ∈ q.support, x ∈ c₂.support) →
      ∃ R : S.graph.Walk u₁ u₂, R.IsPath ∧ R.length = P₁.length + q.length + P₂.length ∧
        (∀ x ∈ R.support, x ≠ u₁ → x ≠ u₂ → x ∉ p₁.support ∧ x ∉ p₂.support) := by
    intro q hq hqC₂
    have h1 : (P₁.append q).IsPath := by
      apply isPath_append_of_disjoint_pc P₁ q hP₁ hq
      intro x hx1 hxq
      by_contra hxw₁
      have hxu₁ : x ≠ u₁ := fun h => hdisjC u₁ hu₁ (hqC₂ x (h ▸ hxq))
      exact (hP₁_int x hx1 hxu₁ hxw₁).2 (hqC₂ x hxq)
    have h2 : ((P₁.append q).append P₂.reverse).IsPath := by
      apply isPath_append_of_disjoint_pc (P₁.append q) P₂.reverse h1 hP₂.reverse
      intro x hx1 hx2
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx1
      rcases hx1 with hxP₁ | hxq
      · exact False.elim (hP_disj x hxP₁ hx2)
      · by_contra hxw₂
        have hxu₂ : x ≠ u₂ := fun h => hdisjC u₂ hu₂ (hqC₂ x (h ▸ hxq))
        exact (hP₂_int x hx2 hxu₂ hxw₂).2 (hqC₂ x hxq)
    refine ⟨(P₁.append q).append P₂.reverse, h2, ?_, ?_⟩
    · simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    · intro x hx hx1 hx2
      have hxC₁ : x ∉ c₁.support := by
        intro hmem
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff] at hx
        rcases hx with (hxP₁ | hxq) | hxP₂
        · have hxw₁ : x ≠ w₁ := fun h => hdisjC x hmem (h ▸ hw₁)
          exact (hP₁_int x hxP₁ hx1 hxw₁).1 hmem
        · exact hdisjC x hmem (hqC₂ x hxq)
        · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hxP₂
          have hxw₂ : x ≠ w₂ := fun h => hdisjC x hmem (h ▸ hw₂)
          exact (hP₂_int x hxP₂ hx2 hxw₂).1 hmem
      exact ⟨fun hm => hxC₁ ((hp_supp x).mp (Or.inl hm)), fun hm => hxC₁ ((hp_supp x).mp (Or.inr hm))⟩
  obtain ⟨R₁, hR₁, hR₁_len, hR₁_int⟩ := hbuild q₁ hq₁ (fun x hx => (hq_supp x).mp (Or.inl hx))
  obtain ⟨R₂, hR₂, hR₂_len, hR₂_int⟩ := hbuild q₂ hq₂ (fun x hx => (hq_supp x).mp (Or.inr hx))
  by_cases hpar : Odd (R₁.length + p₂.length)
  · exact even_odd_cycle_linkage S hu p₁ p₂ hp₁ hp₂ (hp_len.symm ▸ heven) R₁ hR₁ hR₁_int hpar hw_eq
  · have hpar₂ : Odd (R₂.length + p₂.length) := by
      rw [Nat.not_odd_iff_even] at hpar
      rcases hpar with ⟨a, ha⟩
      rcases hodd with ⟨b, hb⟩
      refine ⟨b + P₁.length + P₂.length + p₂.length - a, ?_⟩
      omega
    exact even_odd_cycle_linkage S hu p₁ p₂ hp₁ hp₂ (hp_len.symm ▸ heven) R₂ hR₂ hR₂_int hpar₂ hw_eq

omit [Fintype V] in
/-- **Lemma 3.3(b)**: Even cycle `c₁` and odd cycle `c₂` meeting only at `u`, linked by a path
`P : u₂ → w` (`u₂ ∈ c₁ \ {u}`, `w ∈ c₂ \ {u}`, internally disjoint from `c₁ ∪ c₂`), with
`w(c₁) + 2 * d(u, u₂) = 2 (mod 4)` cannot occur in an NOC signed graph. -/
lemma even_odd_cycle_linkage_one_vertex (S : SignedGraph V)
    {u v₁ v₂ u₂ w : V}
    (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hinter : ∀ x, x ∈ c₁.support → x ∈ c₂.support → x = u)
    (hu₁ : u ∈ c₁.support) (hu₂ : u₂ ∈ c₁.support) (hu : u ≠ u₂)
    (huC₂ : u ∈ c₂.support) (hwC₂ : w ∈ c₂.support) (hwu : w ≠ u)
    (P : S.graph.Walk u₂ w) (hP : P.IsPath)
    (hP_int : ∀ x ∈ P.support, x ≠ u₂ → x ≠ w → x ∉ c₁.support ∧ x ∉ c₂.support)
    (p₁ p₂ : S.graph.Walk u u₂) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hp_len : p₁.length + p₂.length = c₁.length)
    (hp_supp : ∀ x, x ∈ p₁.support ∨ x ∈ p₂.support ↔ x ∈ c₁.support)
    (hw_eq : (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) +
      2 * (p₂.length : ZMod 4) = 2) :
    ¬ IsNOC S := by
  obtain ⟨q₁, q₂, hq₁, hq₂, hq_len, hq_supp, _, _⟩ :=
    cycle_arcs_of_mem c₂ hc₂ hwC₂ huC₂ hwu
  have hbuild : ∀ (q : S.graph.Walk w u), q.IsPath → (∀ x ∈ q.support, x ∈ c₂.support) →
      ∃ R : S.graph.Walk u u₂, R.IsPath ∧ R.length = P.length + q.length ∧
        (∀ x ∈ R.support, x ≠ u → x ≠ u₂ → x ∉ p₁.support ∧ x ∉ p₂.support) := by
    intro q hq hqC₂
    have h1 : (P.append q).IsPath := by
      apply isPath_append_of_disjoint_pc P q hP hq
      intro x hxP hxq
      by_contra hxw
      have hxu₂ : x ≠ u₂ := fun h => hu (hinter u₂ hu₂ (hqC₂ x (h ▸ hxq))).symm
      exact (hP_int x hxP hxu₂ hxw).2 (hqC₂ x hxq)
    refine ⟨(P.append q).reverse, h1.reverse, by simp [SimpleGraph.Walk.length_append], ?_⟩
    intro x hx hxu hxu₂
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.mem_support_append_iff] at hx
    have hxC₁ : x ∉ c₁.support := by
      intro hmem
      rcases hx with hxP | hxq
      · have hxw : x ≠ w := fun h => hwu (h ▸ hinter x hmem (h ▸ hwC₂))
        exact (hP_int x hxP hxu₂ hxw).1 hmem
      · exact hxu (hinter x hmem (hqC₂ x hxq))
    exact ⟨fun hm => hxC₁ ((hp_supp x).mp (Or.inl hm)), fun hm => hxC₁ ((hp_supp x).mp (Or.inr hm))⟩
  obtain ⟨R₁, hR₁, hR₁_len, hR₁_int⟩ := hbuild q₁ hq₁ (fun x hx => (hq_supp x).mp (Or.inl hx))
  obtain ⟨R₂, hR₂, hR₂_len, hR₂_int⟩ := hbuild q₂ hq₂ (fun x hx => (hq_supp x).mp (Or.inr hx))
  by_cases hpar : Odd (R₁.length + p₂.length)
  · exact even_odd_cycle_linkage S hu p₁ p₂ hp₁ hp₂ (hp_len.symm ▸ heven) R₁ hR₁ hR₁_int hpar hw_eq
  · have hpar₂ : Odd (R₂.length + p₂.length) := by
      rw [Nat.not_odd_iff_even] at hpar
      rcases hpar with ⟨a, ha⟩
      rcases hodd with ⟨b, hb⟩
      refine ⟨b + P.length + p₂.length - a, ?_⟩
      omega
    exact even_odd_cycle_linkage S hu p₁ p₂ hp₁ hp₂ (hp_len.symm ▸ heven) R₂ hR₂ hR₂_int hpar₂ hw_eq

omit [Fintype V] [DecidableEq V] in
/-- In an NOC signed graph, an even cycle `c` with `walkModFourWeight S.sign c = 2` has no
chord joining two vertices at even distance along `c`. -/
lemma no_even_distance_chord_of_weight_two (S : SignedGraph V) (hnoc : IsNOC S)
    {v u₁ u₂ : V} (c : S.graph.Walk v v) (hc : c.IsCycle) (heven : Even c.length)
    (hw2 : walkModFourWeight S.sign c = 2)
    (hu₁ : u₁ ∈ c.support) (hu₂ : u₂ ∈ c.support) (hu : u₁ ≠ u₂)
    (hadj : S.graph.Adj u₁ u₂) (hchord : s(u₁, u₂) ∉ c.edges) :
    ∀ (p₁ p₂ : S.graph.Walk u₁ u₂), p₁.IsPath → p₂.IsPath →
      p₁.length + p₂.length = c.length →
      walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂ = walkModFourWeight S.sign c →
      ¬ Even p₂.length := by
  intro p₁ p₂ hp₁ hp₂ hlen hwsum hev2
  let q : S.graph.Walk u₁ u₂ := SimpleGraph.Walk.cons hadj .nil
  have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [q, hu])
  have hq_disj : ∀ x ∈ q.support, x ≠ u₁ → x ≠ u₂ → x ∉ p₁.support ∧ x ∉ p₂.support := by
    intro x hx h1 h2; simp [q] at hx; rcases hx with rfl | rfl <;> contradiction
  have hq_odd : Odd (q.length + p₂.length) := by
    rcases hev2 with ⟨k, hk⟩
    exact ⟨k, by simp [q]; omega⟩
  have h2p2 : 2 * (p₂.length : ZMod 4) = 0 := by
    rcases hev2 with ⟨k, hk⟩
    rw [hk]
    have : 2 * ((k + k : ℕ) : ZMod 4) = (4 : ZMod 4) * (k : ZMod 4) := by push_cast; ring
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [this, h4, zero_mul]
  have hwc : (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) + 2 * (p₂.length : ZMod 4) = 2 := by
    rw [hwsum, hw2, h2p2, add_zero]
  exact even_odd_cycle_linkage S hu p₁ p₂ hp₁ hp₂ (hlen.symm ▸ heven) q hq hq_disj hq_odd hwc hnoc

omit [Fintype V] [DecidableEq V] in
lemma walkModFourWeight_even_of_even_length {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {u v : V} (p : G.Walk u v) (heven : Even p.length) :
    walkModFourWeight σ p = 0 ∨ walkModFourWeight σ p = 2 := by
  have h2 := two_mul_walkModFourWeight σ p
  rcases heven with ⟨k, hk⟩
  rw [hk] at h2
  have h0 : 2 * ((k + k : ℕ) : ZMod 4) = 0 := by
    have : 2 * ((k + k : ℕ) : ZMod 4) = (4 : ZMod 4) * (k : ZMod 4) := by push_cast; ring
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [this, h4, zero_mul]
  rw [h0] at h2
  generalize hw : walkModFourWeight σ p = w
  rw [hw] at h2
  fin_cases w
  · exact Or.inl rfl
  · exact absurd h2 (by decide)
  · exact Or.inr rfl
  · exact absurd h2 (by decide)

lemma k4_pair_paths (S : SignedGraph V) (hnoc : IsNOC S)
    {v : V} (c : S.graph.Walk v v) (hc : c.IsCycle) (hclen : c.length = 4)
    (hK4 : ∀ a ∈ c.support, ∀ b ∈ c.support, a ≠ b → S.graph.Adj a b)
    {u₁ u₂ : V} (hu₁ : u₁ ∈ c.support) (hu₂ : u₂ ∈ c.support) (hu : u₁ ≠ u₂) :
    ∃ (p₁ p₂ : S.graph.Walk u₁ u₂), p₁.IsPath ∧ p₂.IsPath ∧
      p₁.length + p₂.length = 4 ∧
      (∀ x, x ∈ p₁.support ∨ x ∈ p₂.support ↔ x ∈ c.support) ∧
      (walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂) +
        2 * (p₂.length : ZMod 4) = 2 := by
  classical
  have hcard : c.support.toFinset.card = 4 := by
    rw [cycle_support_card c hc, hclen]
  let rem : Finset V := (c.support.toFinset.erase u₁).erase u₂
  have hrem_card : rem.card = 2 := by
    have hu₁' : u₁ ∈ c.support.toFinset := List.mem_toFinset.mpr hu₁
    have hu₂' : u₂ ∈ c.support.toFinset.erase u₁ :=
      Finset.mem_erase.mpr ⟨hu.symm, List.mem_toFinset.mpr hu₂⟩
    rw [Finset.card_erase_of_mem hu₂', Finset.card_erase_of_mem hu₁', hcard]
  obtain ⟨a, b, hab, hrem_eq⟩ := Finset.card_eq_two.mp hrem_card
  have ha_mem : a ∈ rem := by rw [hrem_eq]; simp
  have hb_mem : b ∈ rem := by rw [hrem_eq]; simp
  have haC : a ∈ c.support := List.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha_mem))
  have hbC : b ∈ c.support := List.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb_mem))
  have hau₁ : a ≠ u₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha_mem)).1
  have hau₂ : a ≠ u₂ := (Finset.mem_erase.mp ha_mem).1
  have hbu₁ : b ≠ u₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb_mem)).1
  have hbu₂ : b ≠ u₂ := (Finset.mem_erase.mp hb_mem).1
  have h_u1u2 : S.graph.Adj u₁ u₂ := hK4 u₁ hu₁ u₂ hu₂ hu
  have h_u1a : S.graph.Adj u₁ a := hK4 u₁ hu₁ a haC hau₁.symm
  have h_ab : S.graph.Adj a b := hK4 a haC b hbC hab
  have h_bu2 : S.graph.Adj b u₂ := hK4 b hbC u₂ hu₂ hbu₂
  have h_au2 : S.graph.Adj a u₂ := hK4 a haC u₂ hu₂ hau₂
  let p₁ : S.graph.Walk u₁ u₂ := SimpleGraph.Walk.cons h_u1u2 .nil
  let p₂ : S.graph.Walk u₁ u₂ := SimpleGraph.Walk.cons h_u1a (SimpleGraph.Walk.cons h_ab (SimpleGraph.Walk.cons h_bu2 .nil))
  have hp₁ : p₁.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [p₁, hu])
  have hp₂ : p₂.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    simp [p₂, hau₁.symm, hbu₁.symm, hu, hab, hau₂, hbu₂])
  have hmod4 := (isNOC_iff_isNOCModFour S).mp hnoc
  let t₁ : S.graph.Walk u₁ u₁ := SimpleGraph.Walk.cons h_u1a (SimpleGraph.Walk.cons h_au2 (SimpleGraph.Walk.cons h_u1u2.symm .nil))
  have ht₁_cyc : t₁.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp only [t₁, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
      · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hau₁ h1.symm
        · exact hu h2
      · rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hau₁ h2.symm
        · exact hau₂ h1.symm
      · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hau₂ h1
        · exact hu h2.symm
    · intro h; simp [t₁] at h
    · simp [t₁, hau₂, hau₁, hu.symm]
  let t₂ : S.graph.Walk a a := SimpleGraph.Walk.cons h_ab (SimpleGraph.Walk.cons h_bu2 (SimpleGraph.Walk.cons h_au2.symm .nil))
  have ht₂_cyc : t₂.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp only [t₂, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
      · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hab h1
        · exact hau₂ h2
      · rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hab h2.symm
        · exact hbu₂ h1.symm
      · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hbu₂ h1
        · exact hau₂ h2.symm
    · intro h; simp [t₂] at h
    · simp [t₂, hbu₂, hab.symm, hau₂.symm]
  have hwt₁ : walkModFourWeight S.sign t₁ = 3 := hmod4 u₁ t₁ ht₁_cyc ⟨1, rfl⟩
  have hwt₂ : walkModFourWeight S.sign t₂ = 3 := hmod4 a t₂ ht₂_cyc ⟨1, rfl⟩
  simp only [t₁, t₂, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hwt₁ hwt₂
  have h2au2 : 2 * modFourWeight S.sign s(a, u₂) = 2 := two_mul_modFourWeight S.sign s(a, u₂)
  have hswap1 : s(u₂, u₁) = s(u₁, u₂) := Sym2.eq_swap
  have hswap2 : s(u₂, a) = s(a, u₂) := Sym2.eq_swap
  rw [hswap1] at hwt₁
  rw [hswap2] at hwt₂
  have hsum : walkModFourWeight S.sign p₁ + walkModFourWeight S.sign p₂ = 0 := by
    simp only [p₁, p₂, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h4 : (4 : ZMod 4) = 0 := rfl
    linear_combination hwt₁ + hwt₂ - h2au2 - h4
  refine ⟨p₁, p₂, hp₁, hp₂, by simp [p₁, p₂], ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      rcases hx with h1 | h2
      · simp [p₁] at h1; rcases h1 with rfl | rfl <;> assumption
      · simp [p₂] at h2; rcases h2 with rfl | rfl | rfl | rfl <;> assumption
    · intro hxC
      by_cases h1 : x = u₁
      · subst h1; left; simp [p₁]
      · by_cases h2 : x = u₂
        · subst h2; left; simp [p₁]
        · have hx_rem : x ∈ rem := by
            simp only [rem, Finset.mem_erase]
            exact ⟨h2, h1, List.mem_toFinset.mpr hxC⟩
          rw [hrem_eq, Finset.mem_insert, Finset.mem_singleton] at hx_rem
          rcases hx_rem with rfl | rfl
          · right; simp [p₂]
          · right; simp [p₂]
  · rw [hsum]
    simp [p₂]
    decide

omit [Fintype V] in
lemma cycle_induce_preconnected {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    ∀ x ∈ c.support.toFinset, ∀ y ∈ c.support.toFinset,
      (G.induce (c.support.toFinset : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · obtain ⟨p₁, _, _, _, _, hsupp, _, _⟩ :=
      cycle_arcs_of_mem c hc (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy
    have hp₁_sub : ∀ z ∈ p₁.support, z ∈ c.support.toFinset := fun z hz =>
      List.mem_toFinset.mpr ((hsupp z).mp (Or.inl hz))
    have hlift : ∀ {a b : V} (q : G.Walk a b) (hq : ∀ z ∈ q.support, z ∈ c.support.toFinset),
        (G.induce (c.support.toFinset : Set V)).Reachable
          ⟨a, hq a (SimpleGraph.Walk.start_mem_support q)⟩
          ⟨b, hq b (SimpleGraph.Walk.end_mem_support q)⟩ := by
      intro a b q
      induction q with
      | nil => intro _; exact SimpleGraph.Reachable.refl _
      | @cons a₁ b₁ d hadj r ihr =>
        intro hq
        have ha₁ : a₁ ∈ c.support.toFinset := hq a₁ (List.mem_cons_self ..)
        have hqr : ∀ z ∈ r.support, z ∈ c.support.toFinset := fun z hz =>
          hq z (List.mem_cons_of_mem _ hz)
        exact (SimpleGraph.Adj.reachable (show (G.induce (c.support.toFinset : Set V)).Adj
          ⟨a₁, ha₁⟩ ⟨b₁, hqr b₁ (SimpleGraph.Walk.start_mem_support r)⟩ from hadj)).trans (ihr hqr)
    exact hlift p₁ hp₁_sub

omit [Fintype V] in
lemma cycle_erase_preconnected {G : SimpleGraph V} {v u : V}
    (c : G.Walk v v) (hc : c.IsCycle) (hu : u ∈ c.support) :
    ∀ x ∈ c.support.toFinset.erase u, ∀ y ∈ c.support.toFinset.erase u,
      (G.induce ((c.support.toFinset.erase u : Finset V) : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · have hxC : x ∈ c.support := List.mem_toFinset.mp (Finset.mem_of_mem_erase hx)
    have hyC : y ∈ c.support := List.mem_toFinset.mp (Finset.mem_of_mem_erase hy)
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
    obtain ⟨p₁, p₂, _, _, _, hsupp, hdisj, _⟩ := cycle_arcs_of_mem c hc hxC hyC hxy
    have hlift : ∀ {a b : V} (q : G.Walk a b) (hq : ∀ z ∈ q.support, z ∈ c.support.toFinset.erase u),
        (G.induce ((c.support.toFinset.erase u : Finset V) : Set V)).Reachable
          ⟨a, hq a (SimpleGraph.Walk.start_mem_support q)⟩
          ⟨b, hq b (SimpleGraph.Walk.end_mem_support q)⟩ := by
      intro a b q
      induction q with
      | nil => intro _; exact SimpleGraph.Reachable.refl _
      | @cons a₁ b₁ d hadj r ihr =>
        intro hq
        have ha₁ : a₁ ∈ c.support.toFinset.erase u := hq a₁ (List.mem_cons_self ..)
        have hqr : ∀ z ∈ r.support, z ∈ c.support.toFinset.erase u := fun z hz =>
          hq z (List.mem_cons_of_mem _ hz)
        exact (SimpleGraph.Adj.reachable (show (G.induce ((c.support.toFinset.erase u : Finset V) : Set V)).Adj
          ⟨a₁, ha₁⟩ ⟨b₁, hqr b₁ (SimpleGraph.Walk.start_mem_support r)⟩ from hadj)).trans (ihr hqr)
    by_cases hu1 : u ∈ p₁.support
    · have hu2 : u ∉ p₂.support := hdisj u hu1 hxu.symm hyu.symm
      exact hlift p₂ (fun z hz => Finset.mem_erase.mpr
        ⟨fun h => hu2 (h ▸ hz), List.mem_toFinset.mpr ((hsupp z).mp (Or.inr hz))⟩)
    · exact hlift p₁ (fun z hz => Finset.mem_erase.mpr
        ⟨fun h => hu1 (h ▸ hz), List.mem_toFinset.mpr ((hsupp z).mp (Or.inl hz))⟩)

lemma deg_in_cycle_le_two_of_no_chord {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) {x : V} (hx : x ∈ c.support)
    (hnochord : ∀ y ∈ c.support, G.Adj x y → s(x, y) ∈ c.edges) :
    (c.support.toFinset.filter (fun y => G.Adj x y)).card ≤ 2 := by
  classical
  let c' := c.rotate x hx
  have hc' : c'.IsCycle := hc.rotate hx
  have hge3 : 3 ≤ c'.length := hc'.three_le_length
  have hsupp_eq : ∀ z, z ∈ c'.support ↔ z ∈ c.support := by
    intro z
    have h1 : c' = (c.dropUntil x hx).append (c.takeUntil x hx) := rfl
    have h2 : c = (c.takeUntil x hx).append (c.dropUntil x hx) := (SimpleGraph.Walk.take_spec c hx).symm
    rw [h1, SimpleGraph.Walk.mem_support_append_iff]
    conv_rhs => rw [h2, SimpleGraph.Walk.mem_support_append_iff]
    exact or_comm
  have hedges_eq : ∀ e, e ∈ c'.edges ↔ e ∈ c.edges := fun e => by
    have h1 : c' = (c.dropUntil x hx).append (c.takeUntil x hx) := rfl
    have h2 : c = (c.takeUntil x hx).append (c.dropUntil x hx) := (SimpleGraph.Walk.take_spec c hx).symm
    rw [h1, SimpleGraph.Walk.edges_append, List.mem_append]
    conv_rhs => rw [h2, SimpleGraph.Walk.edges_append, List.mem_append]
    exact or_comm
  cases hc'_eq : c' with
  | nil => simp [hc'_eq] at hge3
  | @cons _ a _ hxa p =>
    have hp_path : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      have hnd := hc'.support_nodup
      rw [hc'_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at hnd
      exact hnd)
    cases hpr_eq : p.reverse with
    | nil =>
      have hp0 : p.length = 0 := by rw [← SimpleGraph.Walk.length_reverse, hpr_eq]; rfl
      rw [hc'_eq, SimpleGraph.Walk.length_cons, hp0] at hge3; omega
    | @cons _ b _ hxb q =>
      have hsub : c.support.toFinset.filter (fun y => G.Adj x y) ⊆ ({a, b} : Finset V) := by
        intro y hy
        simp only [Finset.mem_filter, List.mem_toFinset] at hy
        have he : s(x, y) ∈ c'.edges := (hedges_eq s(x, y)).mpr (hnochord y hy.1 hy.2)
        rw [hc'_eq, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with h1 | h2
        · rcases Sym2.eq_iff.mp h1 with ⟨_, rfl⟩ | ⟨hxy, _⟩
          · simp
          · exact absurd hxy (G.ne_of_adj hy.2)
        · have he_rev : s(x, y) ∈ p.reverse.edges := by
            rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact h2
          rw [hpr_eq, SimpleGraph.Walk.edges_cons, List.mem_cons] at he_rev
          rcases he_rev with h1 | h3
          · rcases Sym2.eq_iff.mp h1 with ⟨_, rfl⟩ | ⟨hxy, _⟩
            · simp
            · exact absurd hxy (G.ne_of_adj hy.2)
          · exfalso
            have hx_q : x ∈ q.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges q h3
            have hnd := hp_path.reverse.support_nodup
            rw [hpr_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.1 hx_q
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

lemma exists_neighbor_outside_even {G : SimpleGraph V}
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) (heven : Even c.length)
    {x : V} (hx : x ∈ c.support)
    (hnochord : ∀ y ∈ c.support, G.Adj x y → s(x, y) ∈ c.edges) :
    ∃ w ∉ c.support.toFinset, G.Adj x w := by
  classical
  have h4 : 4 ≤ Fintype.card V := card_ge_four_of_even_cycle c hc heven
  have hdeg3 : 3 ≤ G.degree x := min_deg_three_of_three_conn h4 h3 x
  have hcard_in := deg_in_cycle_le_two_of_no_chord c hc hx hnochord
  have hsub : (G.neighborFinset x \ c.support.toFinset).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have hle : (G.neighborFinset x).card ≤ (c.support.toFinset.filter (fun y => G.Adj x y)).card := by
      apply Finset.card_le_card
      intro y hy
      exact Finset.mem_filter.mpr ⟨hemp hy, (SimpleGraph.mem_neighborFinset G x y).mp hy⟩
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
    omega
  rcases hsub with ⟨w, hw⟩
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hw
  exact ⟨w, hw.2, hw.1⟩

lemma two_mul_nat_mod_four (n : ℕ) :
    (Even n → 2 * (n : ZMod 4) = 0) ∧ (Odd n → 2 * (n : ZMod 4) = 2) := by
  constructor
  · rintro ⟨k, rfl⟩
    have h1 : 2 * ((k + k : ℕ) : ZMod 4) = (4 : ZMod 4) * (k : ZMod 4) := by push_cast; ring
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [h1, h4, zero_mul]
  · rintro ⟨k, rfl⟩
    have h1 : 2 * ((2 * k + 1 : ℕ) : ZMod 4) = (4 : ZMod 4) * (k : ZMod 4) + 2 := by push_cast; ring
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [h1, h4, zero_mul, zero_add]

lemma even_cycle_part_card_ge_two {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (heven : Even c.length)
    (col : V → ℕ) (hcol2 : ∀ u, col u < 2)
    (hcol_walk : ∀ {a b : V} (q : G.Walk a b), (∀ e ∈ q.edges, e ∈ c.edges) → (col b + col a + q.length) % 2 = 0) :
    2 ≤ (c.support.toFinset.filter fun u => col u = 0).card ∧
    2 ≤ (c.support.toFinset.filter fun u => col u = 1).card := by
  classical
  have hge4 : 4 ≤ c.length := even_cycle_length_ge_four c hc heven
  cases hc_eq : c with
  | nil => simp [hc_eq] at hge4
  | @cons _ u₁ _ h01 p₁ =>
    cases p₁ with
    | nil => simp [hc_eq] at hge4
    | @cons _ u₂ _ h12 p₂ =>
      cases p₂ with
      | nil => simp [hc_eq] at hge4
      | @cons _ u₃ _ h23 p₃ =>
        have hnd := hc.support_nodup
        rw [hc_eq, SimpleGraph.Walk.support_cons, List.tail_cons,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons] at hnd
        have hv_end : v ∈ p₃.support := SimpleGraph.Walk.end_mem_support p₃
        have hu1_in : u₁ ∈ c.support := by rw [hc_eq]; simp
        have hu2_in : u₂ ∈ c.support := by rw [hc_eq]; simp
        have hu3_in : u₃ ∈ c.support := by rw [hc_eq]; simp
        have hv_in : v ∈ c.support := SimpleGraph.Walk.start_mem_support c
        have hu1_ne_u2 : u₁ ≠ u₂ := by
          rw [List.nodup_cons] at hnd; intro h; subst h; exact hnd.1 (List.mem_cons_self ..)
        have hu1_ne_u3 : u₁ ≠ u₃ := by
          rw [List.nodup_cons] at hnd; intro h; subst h; exact hnd.1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hu2_ne_u3 : u₂ ≠ u₃ := by
          rw [List.nodup_cons, List.nodup_cons] at hnd; intro h; subst h; exact hnd.2.1 (List.mem_cons_self ..)
        have hu1_ne_v : u₁ ≠ v := by
          rw [List.nodup_cons] at hnd; intro h; subst h; exact hnd.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv_end))
        have hu2_ne_v : u₂ ≠ v := by
          rw [List.nodup_cons, List.nodup_cons] at hnd; intro h; subst h; exact hnd.2.1 (List.mem_cons_of_mem _ hv_end)
        have hu3_ne_v : u₃ ≠ v := by
          rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnd; intro h; subst h; exact hnd.2.2.1 hv_end
        have he01 : s(v, u₁) ∈ c.edges := by rw [hc_eq]; simp
        have he12 : s(u₁, u₂) ∈ c.edges := by rw [hc_eq]; simp
        have he23 : s(u₂, u₃) ∈ c.edges := by rw [hc_eq]; simp
        have hp01 := hcol_walk (SimpleGraph.Walk.cons h01 .nil) (fun e he => by simp at he; rwa [he])
        have hp12 := hcol_walk (SimpleGraph.Walk.cons h12 .nil) (fun e he => by simp at he; rwa [he])
        have hp23 := hcol_walk (SimpleGraph.Walk.cons h23 .nil) (fun e he => by simp at he; rwa [he])
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp01 hp12 hp23
        have hcv := hcol2 v; have hcu1 := hcol2 u₁; have hcu2 := hcol2 u₂; have hcu3 := hcol2 u₃
        have hcol_v_u2 : col v = col u₂ := by omega
        have hcol_u1_u3 : col u₁ = col u₃ := by omega
        have hcol_v_ne_u1 : col v ≠ col u₁ := by omega
        by_cases hcv0 : col v = 0
        · have hcu2_0 : col u₂ = 0 := by omega
          have hcu1_1 : col u₁ = 1 := by omega
          have hcu3_1 : col u₃ = 1 := by omega
          constructor
          · calc 2 = ({v, u₂} : Finset V).card := (Finset.card_pair hu2_ne_v.symm).symm
              _ ≤ _ := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> simp [List.mem_toFinset, *])
          · calc 2 = ({u₁, u₃} : Finset V).card := (Finset.card_pair hu1_ne_u3).symm
              _ ≤ _ := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> simp [List.mem_toFinset, *])
        · have hcv1 : col v = 1 := by omega
          have hcu2_1 : col u₂ = 1 := by omega
          have hcu1_0 : col u₁ = 0 := by omega
          have hcu3_0 : col u₃ = 0 := by omega
          constructor
          · calc 2 = ({u₁, u₃} : Finset V).card := (Finset.card_pair hu1_ne_u3).symm
              _ ≤ _ := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> simp [List.mem_toFinset, *])
          · calc 2 = ({v, u₂} : Finset V).card := (Finset.card_pair hu2_ne_v.symm).symm
              _ ≤ _ := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> simp [List.mem_toFinset, *])

end SignedGraphs
