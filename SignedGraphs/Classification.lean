import SignedGraphs.TwoOddCycles

/-!
# Classification of 3-Connected Non-Bipartite NOC Signed Graphs (Theorem 3.1)

Formalization of Theorem 3.1: every 3-connected, non-bipartite NOC signed graph is
switching-isomorphic to either `(K₄, +1)` or `(Petersen, -1)`.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma odd_cycle_weight_three (S : SignedGraph V) (hnoc : IsNOC S)
    {v : V} (c : S.graph.Walk v v) (hc : c.IsCycle) (hodd : Odd c.length) :
    walkModFourWeight S.sign c = 3 := by
  exact (isNOC_iff_isNOCModFour S).mp hnoc v c hc hodd

private lemma sign_triangle_prod_one (S : SignedGraph V) (hnoc : IsNOC S)
    {a b c : V} (hab : S.graph.Adj a b) (hbc : S.graph.Adj b c) (hca : S.graph.Adj c a) :
    S.sign s(a, b) * S.sign s(b, c) * S.sign s(c, a) = 1 := by
  have hne_ab : a ≠ b := S.graph.ne_of_adj hab
  have hne_bc : b ≠ c := S.graph.ne_of_adj hbc
  have hne_ca : c ≠ a := S.graph.ne_of_adj hca
  let cyc : S.graph.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hcyc : cyc.IsCycle := by
    refine ⟨⟨?_, by simp [cyc]⟩, ?_⟩
    · refine SimpleGraph.Walk.IsTrail.mk ?_
      simp [cyc, Sym2.eq_iff, hne_ab, hne_ab.symm, hne_bc, hne_bc.symm, hne_ca, hne_ca.symm]
    · simp [cyc, hne_bc, hne_ca, hne_ca.symm]
  have hw := odd_cycle_weight_three S hnoc cyc hcyc ⟨1, by simp [cyc]⟩
  simp only [cyc, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hw
  rcases S.sign_pm_one s(a, b) hab with h1 | h1 <;>
  rcases S.sign_pm_one s(b, c) hbc with h2 | h2 <;>
  rcases S.sign_pm_one s(c, a) hca with h3 | h3 <;>
  (simp [modFourWeight, h1, h2, h3] at hw ⊢; try exact absurd hw (by decide))

private lemma k4_switching_iso (S : SignedGraph V) (hnoc : IsNOC S)
    (v₁ v₂ v₃ u : V)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h1u : v₁ ≠ u)
    (h23 : v₂ ≠ v₃) (h2u : v₂ ≠ u) (h3u : v₃ ≠ u)
    (hcov : ∀ x : V, x = v₁ ∨ x = v₂ ∨ x = v₃ ∨ x = u)
    (hcomplete : ∀ x y : V, x ≠ y → S.graph.Adj x y) :
    SwitchingIso S k4SignedGraph := by
  classical
  let f : Fin 4 → V
    | 0 => v₁
    | 1 => v₂
    | 2 => v₃
    | 3 => u
  have hf_bij : Function.Bijective f := by
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢ <;> contradiction
    · intro x
      rcases hcov x with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  let φ : V ≃ Fin 4 := (Equiv.ofBijective f hf_bij).symm
  let e : S.graph ≃g k4SignedGraph.graph :=
    { toEquiv := φ
      map_rel_iff' := by
        intro x y
        simp only [k4SignedGraph, SimpleGraph.top_adj]
        constructor
        · intro hxy; exact fun h => S.graph.ne_of_adj hxy (φ.injective h)
        · intro hne; exact hcomplete x y (fun h => hne (by rw [h])) }
  let T : Finset V := Finset.univ.filter fun x => x ≠ v₁ ∧ S.sign s(v₁, x) = -1
  refine ⟨e, T, ?_⟩
  intro x y hxy
  have hne : x ≠ y := S.graph.ne_of_adj hxy
  simp only [k4SignedGraph]
  have hθ : ∀ z : V, z ≠ v₁ → (if z ∈ T then (-1 : ℤ) else 1) = S.sign s(v₁, z) := by
    intro z hz
    have hadj : S.graph.Adj v₁ z := hcomplete v₁ z hz.symm
    rcases S.sign_pm_one s(v₁, z) hadj with hs | hs
    · have hnot : z ∉ T := by simp [T, hz, hs]
      simp [hnot, hs]
    · have hmem : z ∈ T := by simp [T, hz, hs]
      simp [hmem, hs]
  have hv1_not : v₁ ∉ T := by simp [T]
  by_cases hx1 : x = v₁
  · subst hx1
    rw [if_neg hv1_not, hθ y hne.symm]
    rcases S.sign_pm_one s(x, y) hxy with hs | hs <;> simp [hs]
  · by_cases hy1 : y = v₁
    · subst hy1
      rw [hθ x hx1, if_neg hv1_not, Sym2.eq_swap]
      rcases S.sign_pm_one s(y, x) hxy.symm with hs | hs <;> simp [hs]
    · rw [hθ x hx1, hθ y hy1]
      have htri := sign_triangle_prod_one S hnoc (hcomplete v₁ x (Ne.symm hx1)) hxy (hcomplete y v₁ hy1)
      rw [Sym2.eq_swap (a := y) (b := v₁)] at htri
      linarith [mul_comm (S.sign s(v₁, y)) (S.sign s(x, y)),
        mul_assoc (S.sign s(v₁, x)) (S.sign s(v₁, y)) (S.sign s(x, y)),
        mul_assoc (S.sign s(v₁, x)) (S.sign s(x, y)) (S.sign s(v₁, y))]

/-- A finite connected acyclic vertex set `T` of size `≥ 2` has two distinct leaves,
each with at most 1 neighbor in `T`. -/
private lemma tree_two_leaves {G : SimpleGraph V} (T : Finset V) (hcard : 2 ≤ T.card)
    (hconn : ∀ (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ T),
      (G.induce (T : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩)
    (hacyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → ¬ (∀ x ∈ c.support, x ∈ T)) :
    ∃ u₁ u₂ : V, u₁ ∈ T ∧ u₂ ∈ T ∧ u₁ ≠ u₂ ∧
      (T.filter fun w => G.Adj u₁ w).card ≤ 1 ∧
      (T.filter fun w => G.Adj u₂ w).card ≤ 1 := by
  classical
  -- Maximize the length of a simple path in T
  let good : ℕ → Prop := fun n =>
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ (∀ x ∈ p.support, x ∈ T) ∧ p.length = n
  have hex_ge1 : ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ (∀ x ∈ p.support, x ∈ T) ∧ 1 ≤ p.length := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) x
    obtain ⟨r⟩ := hconn x hx y hy
    let rp := r.toPath
    let f : G.induce (T : Set V) →g G := (SimpleGraph.Embedding.induce (T : Set V)).toHom
    let p : G.Walk x y := rp.1.map f
    refine ⟨x, y, p, rp.2.map (fun _ _ h => Subtype.ext h), ?_, ?_⟩
    · intro z hz; have hz' : z ∈ (rp.1.map f).support := hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
      rcases hz' with ⟨z', _, rfl⟩; exact z'.2
    · cases hp : p with
      | nil => exact absurd rfl hyx.symm
      | cons _ _ => simp
  have hbdd : ∀ n, good n → n ≤ Fintype.card V := by
    rintro n ⟨a, b, p, hp, _, rfl⟩
    have hnd := hp.support_nodup
    have hlen : p.length + 1 = p.support.length := by simp
    have hcard_le : p.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
    rw [List.toFinset_card_of_nodup hnd] at hcard_le
    omega
  -- Find maximum length n ≤ Fintype.card V with good n
  let S_lens : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter good
  have hS_ne : S_lens.Nonempty := by
    rcases hex_ge1 with ⟨a, b, p, hp, hpT, hlen⟩
    refine ⟨p.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, a, b, p, hp, hpT, rfl⟩⟩
    have := hbdd p.length ⟨a, b, p, hp, hpT, rfl⟩; omega
  let m := S_lens.max' hS_ne
  have hm_mem : m ∈ S_lens := Finset.max'_mem S_lens hS_ne
  have hm_good : good m := (Finset.mem_filter.mp hm_mem).2
  have hm_max : ∀ n, good n → n ≤ m := by
    intro n hn
    have hle := hbdd n hn
    exact Finset.le_max' S_lens n (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩)
  have hm_ge1 : 1 ≤ m := by
    rcases hex_ge1 with ⟨a, b, p, hp, hpT, hlen⟩
    have := hm_max p.length ⟨a, b, p, hp, hpT, rfl⟩; omega
  rcases hm_good with ⟨a, b, p, hp, hpT, hp_len⟩
  have hab : a ≠ b := by
    intro h; subst h
    cases p with
    | nil => simp at hp_len; omega
    | cons _ _ =>
      have hnd := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1 (SimpleGraph.Walk.end_mem_support _)
  -- Helper: endpoint of a maximal path of length ≥ 1 in T has at most 1 neighbor in T
  have hend_deg : ∀ (u v : V) (q : G.Walk u v), q.IsPath → (∀ x ∈ q.support, x ∈ T) →
      q.length = m → (T.filter fun w => G.Adj u w).card ≤ 1 := by
    intro u v q hq hqT hq_len
    cases q with
    | nil => simp at hq_len; omega
    | @cons _ u₁ _ huu₁ r =>
      have hsub : (T.filter fun w => G.Adj u w) ⊆ {u₁} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [Finset.mem_singleton]
        by_contra hwu₁
        by_cases hwr : w ∈ r.support
        · -- Cycle: u - u₁ -(r.takeUntil w)- w - u inside T!
          let r1 := r.takeUntil w hwr
          have hr1_path : r1.IsPath := (SimpleGraph.Walk.IsPath.of_cons hq).takeUntil hwr
          have hu_not_r : u ∉ r.support := by
            have hnd := hq.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.1
          have hstep : (SimpleGraph.Walk.cons huu₁ r1).IsPath :=
            SimpleGraph.Walk.IsPath.cons hr1_path (fun hm => hu_not_r (SimpleGraph.Walk.support_takeUntil_subset r hwr hm))
          let e_uw : G.Walk u w := SimpleGraph.Walk.cons hw.2 .nil
          have he_uw : e_uw.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e_uw, G.ne_of_adj hw.2])
          have hr1_pos : 1 ≤ r1.length := by
            cases hr1 : r1 with
            | nil =>
              have : u₁ = w := by simpa [r1] using hr1
              exact absurd this.symm hwu₁
            | cons _ _ => simp
          have hcyc : ((SimpleGraph.Walk.cons huu₁ r1).append e_uw.reverse).IsCycle := by
            apply isCycle_append_reverse_of_disjoint e_uw (SimpleGraph.Walk.cons huu₁ r1) he_uw hstep _
              (by simp [e_uw, SimpleGraph.Walk.length_cons]; omega)
            intro z _ hz1 hz2 hze
            simp [e_uw] at hze; rcases hze with rfl | rfl <;> contradiction
          apply hacyc u _ hcyc
          intro z hz
          rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
          rcases hz with h1 | h2
          · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h1
            rcases h1 with rfl | h1'
            · exact hqT u (SimpleGraph.Walk.start_mem_support _)
            · exact hqT z (List.mem_cons_of_mem _ (SimpleGraph.Walk.support_takeUntil_subset r hwr h1'))
          · simp [e_uw] at h2
            rcases h2 with rfl | rfl
            · exact hqT u (SimpleGraph.Walk.start_mem_support _)
            · exact hw.1
        · -- Strictly longer path w - u - u₁ - r in T!
          have hwu : w ≠ u := (G.ne_of_adj hw.2).symm
          have hwnot : w ∉ (SimpleGraph.Walk.cons huu₁ r).support := by
            rw [SimpleGraph.Walk.support_cons, List.mem_cons]
            push Not; exact ⟨hwu, hwr⟩
          have hlong : (SimpleGraph.Walk.cons hw.2.symm (SimpleGraph.Walk.cons huu₁ r)).IsPath :=
            SimpleGraph.Walk.IsPath.cons hq hwnot
          have hlongT : ∀ z ∈ (SimpleGraph.Walk.cons hw.2.symm (SimpleGraph.Walk.cons huu₁ r)).support, z ∈ T := by
            intro z hz
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hz with rfl | h1
            · exact hw.1
            · exact hqT z h1
          have hle := hm_max _ ⟨w, v, SimpleGraph.Walk.cons hw.2.symm (SimpleGraph.Walk.cons huu₁ r), hlong, hlongT, rfl⟩
          simp only [SimpleGraph.Walk.length_cons] at hle hq_len
          omega
      exact (Finset.card_le_card hsub).trans (by simp)
  refine ⟨a, b, hpT a (SimpleGraph.Walk.start_mem_support p), hpT b (SimpleGraph.Walk.end_mem_support p), hab,
    hend_deg a b p hp hpT hp_len,
    hend_deg b a p.reverse hp.reverse (fun x hx => hpT x (by simpa [SimpleGraph.Walk.support_reverse] using hx))
      (by simp [hp_len])⟩

private lemma path_len_eq_two_mid {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) (h2 : p.length = 2) :
    ∃ m : V, m ≠ x ∧ m ≠ y ∧ G.Adj x m ∧ G.Adj m y ∧ p.support = [x, m, y] ∧
      p.edges = [s(x, m), s(m, y)] := by
  cases p with
  | nil => simp at h2
  | @cons _ m _ hxm q =>
    cases q with
    | nil => simp at h2
    | @cons _ z _ hmz r =>
      cases r with
      | nil =>
        have hnd := hp.support_nodup
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons,
          List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        exact ⟨m, G.ne_of_adj hxm |>.symm, G.ne_of_adj hmz, hxm, hmz, by simp, by simp⟩
      | cons _ _ => simp at h2

private lemma path_len_eq_one_adj_cl {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (h1 : p.length = 1) : G.Adj x y := by
  cases p with
  | nil => simp at h1
  | @cons _ m _ hxm q =>
    cases q with
    | nil => exact hxm
    | cons _ _ => simp at h1

private lemma cycle_len_eq_three_vertices {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (h3 : c.length = 3) :
    ∃ v₂ v₃ : V, v ≠ v₂ ∧ v ≠ v₃ ∧ v₂ ≠ v₃ ∧
      G.Adj v v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v ∧
      (∀ x, x ∈ c.support ↔ x = v ∨ x = v₂ ∨ x = v₃) := by
  cases c with
  | nil => simp at h3
  | @cons _ v₂ _ h12 r1 =>
    cases r1 with
    | nil => simp at h3
    | @cons _ v₃ _ h23 r2 =>
      cases r2 with
      | nil => simp at h3
      | @cons _ v₄ _ h34 r3 =>
        cases r3 with
        | nil =>
          refine ⟨v₂, v₃, G.ne_of_adj h12, (G.ne_of_adj h34).symm, G.ne_of_adj h23, h12, h23, h34, ?_⟩
          intro x; simp [or_comm, or_left_comm, or_assoc]
        | cons _ _ => simp at h3

set_option maxHeartbeats 800000 in
/-- **Theorem 3.1**: Every 3-connected, non-bipartite NOC signed graph is switching-isomorphic
to either `(K₄, +1)` or `(Petersen, -1)`. -/
theorem three_connected_non_bipartite_noc_classification (S : SignedGraph V)
    (hcard : 4 ≤ Fintype.card V)
    (hconn : S.graph.Preconnected)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnonbip : ¬ S.graph.IsBipartite)
    (hnoc : IsNOC S) :
    SwitchingIso S k4SignedGraph ∨ SwitchingIso S petersenSignedGraph := by
  classical
  let G := S.graph
  -- Step 1: Shortest odd cycle c in G
  have hex_odd : ∃ n : ℕ, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧ c.length = n := by
    by_contra hall
    push Not at hall
    apply hnonbip
    apply isBipartite_of_no_odd_cycle
    intro v c hc
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    exact hall c.length v c hc hne rfl
  obtain ⟨v₀, c, hc, hodd, hc_len_eq⟩ := Nat.find_spec hex_odd
  have hmin_odd : ∀ {v' : V} (c' : G.Walk v' v'), c'.IsCycle → Odd c'.length → c.length ≤ c'.length := by
    intro v' c' hc' hodd'
    rw [hc_len_eq]
    exact Nat.find_min' hex_odd ⟨v', c', hc', hodd', rfl⟩
  have hc_ge3 : 3 ≤ c.length := hc.three_le_length
  -- c is chordless
  have hchordless : ∀ x ∈ c.support, ∀ y ∈ c.support, G.Adj x y → s(x, y) ∈ c.edges := by
    intro x hx y hy hxy
    by_contra hch
    have hne : x ≠ y := G.ne_of_adj hxy
    obtain ⟨p₁, p₂, hp₁, hp₂, hlen, _, _, hp₁_e, hp₂_e, _⟩ := cycle_arcs_edges_subset c hc hx hy hne
    have hge2 : ∀ (p : G.Walk x y), (∀ e ∈ p.edges, e ∈ c.edges) → 2 ≤ p.length := by
      intro p hpe
      cases p with
      | nil => exact absurd rfl hne
      | @cons _ w _ _ r => cases r with
        | nil => exact False.elim (hch (hpe s(x, w) (by simp)))
        | cons _ _ => simp
    have hp₁_ge2 := hge2 p₁ hp₁_e
    have hp₂_ge2 := hge2 p₂ hp₂_e
    have hcontra : ∀ (p : G.Walk x y), p.IsPath → Even p.length → 2 ≤ p.length → p.length + 1 < c.length → False := by
      intro p hp hev h2 hlt
      let q : G.Walk x y := SimpleGraph.Walk.cons hxy .nil
      have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [q, hne])
      have hcyc : (q.append p.reverse).IsCycle := by
        apply isCycle_append_reverse_of_disjoint p q hp hq _ (by simp [q]; omega)
        intro z hz h1 h2'; simp [q] at hz; rcases hz with rfl | rfl <;> contradiction
      have hodd' : Odd (q.append p.reverse).length := by
        rcases hev with ⟨k, hk⟩
        exact ⟨k, by simp [q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      have hle := hmin_odd _ hcyc hodd'
      simp only [q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
      omega
    by_cases hev1 : Even p₁.length
    · exact hcontra p₁ hp₁ hev1 hp₁_ge2 (by omega)
    · rw [Nat.not_even_iff_odd] at hev1
      have hev2 : Even p₂.length := by
        rcases hodd with ⟨a, ha⟩; rcases hev1 with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
      exact hcontra p₂ hp₂ hev2 hp₂_ge2 (by omega)
  -- Step 2: Check whether G - V(c) has a cycle
  by_cases hex_cyc : ∃ (v' : V) (c' : G.Walk v' v'), c'.IsCycle ∧ Disjoint c'.support.toFinset c.support.toFinset
  · rcases hex_cyc with ⟨v', c', hc', hdisj'⟩
    by_cases hev' : Even c'.length
    · exact False.elim (cycle_pair_obstructions_disjoint_even_odd S hconn h3 hnoc c' c hc' hc hev' hodd hdisj')
    · rw [Nat.not_even_iff_odd] at hev'
      exact Or.inr (cycle_pair_obstructions_two_disjoint_odd_impl S hconn h3 hnoc c' c hc' hc hev' hodd hdisj')
  · push Not at hex_cyc
    -- G - V(c) is acyclic!
    have hacyc_out : ∀ (v' : V) (c' : G.Walk v' v'), c'.IsCycle → ¬ Disjoint c'.support.toFinset c.support.toFinset :=
      hex_cyc
    -- G - V(c) is nonempty (since c is chordless and min degree ≥ 3)
    have hex_out : ∃ w : V, w ∉ c.support.toFinset := by
      have hdeg := min_deg_three_of_three_conn hcard h3 v₀
      have hinc := deg_in_cycle_le_two_of_no_chord c hc (SimpleGraph.Walk.start_mem_support c)
        (fun y hy hadj => hchordless v₀ (SimpleGraph.Walk.start_mem_support c) y hy hadj)
      by_contra hall; push Not at hall
      have hsub : G.neighborFinset v₀ ⊆ c.support.toFinset.filter (fun y => G.Adj v₀ y) := by
        intro y hy
        rw [SimpleGraph.mem_neighborFinset] at hy
        exact Finset.mem_filter.mpr ⟨hall y, hy⟩
      have hle := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
      omega
    -- Connected component of u in G - V(c)
    let compOf : V → Finset V := fun u =>
      Finset.univ.filter fun w =>
        ∃ (hu : u ∈ ((c.support.toFinset : Set V)ᶜ)) (hw : w ∈ ((c.support.toFinset : Set V)ᶜ)),
          (G.induce ((c.support.toFinset : Set V)ᶜ)).Reachable ⟨u, hu⟩ ⟨w, hw⟩
    have hcomp_disj : ∀ u, Disjoint (compOf u) c.support.toFinset := by
      intro u; rw [Finset.disjoint_left]; intro w hw
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hw.2.1
    have hcomp_mem : ∀ u, u ∉ c.support.toFinset → u ∈ compOf u := by
      intro u hu; simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hu, hu, SimpleGraph.Reachable.refl _⟩
    have hcomp_closed : ∀ u, ∀ x ∈ compOf u, ∀ y : V, G.Adj x y → y ∈ compOf u ∪ c.support.toFinset := by
      intro u x hx y hxy
      by_cases hyC : y ∈ c.support.toFinset
      · exact Finset.mem_union_right _ hyC
      · refine Finset.mem_union_left _ ?_
        simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨hu, hxC, hr⟩
        exact ⟨hu, hyC, hr.trans (SimpleGraph.Adj.reachable (show (G.induce ((c.support.toFinset : Set V)ᶜ)).Adj ⟨x, hxC⟩ ⟨y, hyC⟩ from hxy))⟩
    have hcomp_conn : ∀ u, ∀ (x : V) (hx : x ∈ compOf u) (y : V) (hy : y ∈ compOf u),
        (G.induce (compOf u : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro u x hx y hy
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hx with ⟨hu, hxC, hrx⟩; rcases hy with ⟨_, hyC, hry⟩
      obtain ⟨r⟩ := hrx.symm.trans hry
      let f_ind : G.induce ((c.support.toFinset : Set V)ᶜ) →g G :=
        (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
      have hr_in : ∀ z ∈ (r.map f_ind).support, z ∈ compOf u := by
        intro z hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
        rcases hz with ⟨z', hz', rfl⟩
        simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hu, z'.2, hrx.trans ⟨r.takeUntil z' hz'⟩⟩
      exact ⟨(r.map f_ind).induce (compOf u : Set V) hr_in⟩
    have hcomp_acyc : ∀ u (v' : V) (c' : G.Walk v' v'), c'.IsCycle → ¬ (∀ x ∈ c'.support, x ∈ compOf u) := by
      intro u v' c' hc' hsub
      apply hacyc_out v' c' hc'
      rw [Finset.disjoint_left]
      intro x hx
      exact Finset.disjoint_left.mp (hcomp_disj u) (hsub x (List.mem_toFinset.mp hx))
    -- Pick a vertex w_max outside c maximizing (compOf w).card
    let outSet : Finset V := Finset.univ.filter fun w => w ∉ c.support.toFinset
    have hout_ne : outSet.Nonempty := by
      rcases hex_out with ⟨w, hw⟩; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
    obtain ⟨w_max, hw_max_mem, hw_max_ge⟩ := Finset.exists_max_image outSet (fun w => (compOf w).card) hout_ne
    have hw_max_nC : w_max ∉ c.support.toFinset := (Finset.mem_filter.mp hw_max_mem).2
    let T : Finset V := compOf w_max
    have hT_disj : Disjoint T c.support.toFinset := hcomp_disj w_max
    have hT_pos : 1 ≤ T.card := Finset.card_pos.mpr ⟨w_max, hcomp_mem w_max hw_max_nC⟩
    -- Helper: for any x ∈ T, every neighbor of x outside T is in c.support.toFinset
    have hT_nbrs : ∀ x ∈ T, G.neighborFinset x ⊆ (T.filter fun w => G.Adj x w) ∪ (c.support.toFinset.filter fun w => G.Adj x w) := by
      intro x hx y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      rcases Finset.mem_union.mp (hcomp_closed w_max x hx y hy) with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h1, hy⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h2, hy⟩)
    -- Helper: for any u ∉ c.support and two distinct neighbors x, y ∈ c.support of u,
    -- the even-length arc of c between x and y has length 2
    have heven_arc_two : ∀ (u : V), u ∉ c.support → ∀ (x y : V), x ∈ c.support → y ∈ c.support → x ≠ y →
        G.Adj u x → G.Adj u y →
        ∀ (p₁ p₂ : G.Walk x y), p₁.IsPath → p₂.IsPath → p₁.length + p₂.length = c.length →
          (∀ z ∈ p₁.support, z ∈ c.support) → (∀ z ∈ p₂.support, z ∈ c.support) →
          (Even p₁.length ∧ p₁.length = 2) ∨ (Even p₂.length ∧ p₂.length = 2) := by
      intro u hu x y hx hy hxy hux huy p₁ p₂ hp₁ hp₂ hlen hp₁C hp₂C
      have hodd_bound : ∀ (p q : G.Walk x y), p.IsPath → q.IsPath → p.length + q.length = c.length →
          (∀ z ∈ p.support, z ∈ c.support) → Odd p.length → Even q.length ∧ q.length = 2 := by
        intro p q hp hq hl hpC hodd_p
        let r : G.Walk x y := SimpleGraph.Walk.cons hux.symm (SimpleGraph.Walk.cons huy .nil)
        have hr : r.IsPath := SimpleGraph.Walk.IsPath.mk' (by
          simp [r, hxy, (G.ne_of_adj hux).symm, G.ne_of_adj huy])
        have hcyc : (r.append p.reverse).IsCycle := by
          apply isCycle_append_reverse_of_disjoint p r hp hr _ (by
            have : 1 ≤ p.length := by cases p with | nil => exact absurd rfl hxy | cons _ _ => simp
            simp [r]; omega)
          intro z hzr hz1 hz2 hzp
          simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hzr
          rcases hzr with rfl | rfl | rfl
          · exact absurd rfl hz1
          · exact hu (hpC z hzp)
          · exact absurd rfl hz2
        have hodd_r : Odd (r.append p.reverse).length := by
          rcases hodd_p with ⟨k, hk⟩
          exact ⟨k + 1, by simp [r, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        have hle := hmin_odd _ hcyc hodd_r
        simp only [r, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
          SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
        have hq_pos : 1 ≤ q.length := by cases q with | nil => exact absurd rfl hxy | cons _ _ => simp
        have hq_ev : Even q.length := by
          rcases hodd with ⟨a, ha⟩; rcases hodd_p with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
        refine ⟨hq_ev, ?_⟩
        rcases hq_ev with ⟨m, hm⟩; omega
      by_cases hp1_odd : Odd p₁.length
      · exact Or.inr (hodd_bound p₁ p₂ hp₁ hp₂ hlen hp₁C hp1_odd)
      · rw [Nat.not_odd_iff_even] at hp1_odd
        have hp2_odd : Odd p₂.length := by
          rcases hodd with ⟨a, ha⟩; rcases hp1_odd with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
        exact Or.inl (hodd_bound p₂ p₁ hp₂ hp₁ (by omega) hp₂C hp2_odd)
    -- Dispatch on c.length = 3 vs c.length ≥ 5
    by_cases hc3 : c.length = 3
    · -- CASE 1: c is a triangle {v₀, v₂, v₃}
      obtain ⟨v₂, v₃, hv02, hv03, hv23, h02, h23, h30, hc_supp⟩ := cycle_len_eq_three_vertices c hc hc3
      by_cases hT1 : T.card = 1
      · -- Every component of G - V(c) has size 1!
        have hT_eq : T = {w_max} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hcomp_mem w_max hw_max_nC, fun x hx => by
            have := Finset.card_eq_one.mp hT1
            rcases this with ⟨a, ha⟩
            have h1 : w_max = a := Finset.mem_singleton.mp (ha ▸ hcomp_mem w_max hw_max_nC)
            have h2 : x = a := Finset.mem_singleton.mp (ha ▸ hx)
            rw [h2, h1]⟩
        -- Any isolated vertex u outside c is adjacent to all 3 vertices v₀, v₂, v₃
        have hall_adj : ∀ u : V, u ∉ c.support.toFinset → G.Adj u v₀ ∧ G.Adj u v₂ ∧ G.Adj u v₃ := by
          intro u hu
          have hcu_le1 : (compOf u).card ≤ 1 := by
            have := hw_max_ge u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
            omega
          have hcu_eq : compOf u = {u} := by
            have h1 : (compOf u).card = 1 := le_antisymm hcu_le1 (Finset.card_pos.mpr ⟨u, hcomp_mem u hu⟩)
            rcases Finset.card_eq_one.mp h1 with ⟨a, ha⟩
            have hua : u = a := Finset.mem_singleton.mp (ha ▸ hcomp_mem u hu)
            rw [ha, hua]
          have hdeg := min_deg_three_of_three_conn hcard h3 u
          have hsub : G.neighborFinset u ⊆ c.support.toFinset := by
            intro y hy
            rw [SimpleGraph.mem_neighborFinset] at hy
            rcases Finset.mem_union.mp (hcomp_closed u u (hcomp_mem u hu) y hy) with h1 | h2
            · rw [hcu_eq, Finset.mem_singleton] at h1
              exact absurd h1 (G.ne_of_adj hy).symm
            · exact h2
          have hcard_c : c.support.toFinset.card = 3 := by rw [cycle_support_card c hc, hc3]
          have heq : G.neighborFinset u = c.support.toFinset :=
            Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
          have hmem : ∀ z, z ∈ c.support → G.Adj u z := fun z hz =>
            (SimpleGraph.mem_neighborFinset G u z).mp (heq ▸ List.mem_toFinset.mpr hz)
          exact ⟨hmem v₀ ((hc_supp v₀).mpr (Or.inl rfl)),
            hmem v₂ ((hc_supp v₂).mpr (Or.inr (Or.inl rfl))),
            hmem v₃ ((hc_supp v₃).mpr (Or.inr (Or.inr rfl)))⟩
        by_cases hall_cov : ∀ x : V, x = v₀ ∨ x = v₂ ∨ x = v₃ ∨ x = w_max
        · -- Subcase 1a: V = {v₀, v₂, v₃, w_max} → (K₄, +1)!
          have hw0 : v₀ ≠ w_max := fun h => hw_max_nC (h ▸ List.mem_toFinset.mpr ((hc_supp v₀).mpr (Or.inl rfl)))
          have hw2 : v₂ ≠ w_max := fun h => hw_max_nC (h ▸ List.mem_toFinset.mpr ((hc_supp v₂).mpr (Or.inr (Or.inl rfl))))
          have hw3 : v₃ ≠ w_max := fun h => hw_max_nC (h ▸ List.mem_toFinset.mpr ((hc_supp v₃).mpr (Or.inr (Or.inr rfl))))
          obtain ⟨hw0_adj, hw2_adj, hw3_adj⟩ := hall_adj w_max hw_max_nC
          left
          apply k4_switching_iso S hnoc v₀ v₂ v₃ w_max hv02 hv03 hw0 hv23 hw2 hw3 hall_cov
          intro x y hne
          rcases hall_cov x with rfl | rfl | rfl | rfl <;>
          rcases hall_cov y with rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl hne | exact h02 | exact h02.symm | exact h23 | exact h23.symm |
            exact h30 | exact h30.symm | exact hw0_adj | exact hw0_adj.symm |
            exact hw2_adj | exact hw2_adj.symm | exact hw3_adj | exact hw3_adj.symm
        · -- Subcase 1b: Another vertex u' ∉ {v₀, v₂, v₃, w_max} → 5-cycle contradiction!
          push Not at hall_cov
          rcases hall_cov with ⟨u', hu0, hu2, hu3, huw⟩
          have hu'nC : u' ∉ c.support.toFinset := by
            intro hm; have := (hc_supp u').mp (List.mem_toFinset.mp hm); tauto
          obtain ⟨hw0_adj, hw2_adj, hw3_adj⟩ := hall_adj w_max hw_max_nC
          obtain ⟨hu0_adj, hu2_adj, hu3_adj⟩ := hall_adj u' hu'nC
          have hw0 : v₀ ≠ w_max := (G.ne_of_adj hw0_adj).symm
          have hw2 : v₂ ≠ w_max := (G.ne_of_adj hw2_adj).symm
          have hw3 : v₃ ≠ w_max := (G.ne_of_adj hw3_adj).symm
          -- 5-cycle: v₀ - w_max - v₂ - u' - v₃ - v₀
          let c5 : G.Walk v₀ v₀ :=
            .cons hw0_adj.symm (.cons hw2_adj (.cons hu2_adj.symm (.cons hu3_adj (.cons h30 .nil))))
          have hc5 : c5.IsCycle := by
            refine ⟨⟨?_, by simp [c5]⟩, ?_⟩
            · refine SimpleGraph.Walk.IsTrail.mk ?_
              simp [c5, Sym2.eq_iff, hw0, hw0.symm, hw2, hw2.symm, hw3, hw3.symm,
                hu0, hu0.symm, hu2, hu2.symm, hu3, hu3.symm, huw, huw.symm,
                hv02, hv02.symm, hv03, hv03.symm, hv23, hv23.symm]
            · simp [c5, hw2, hw2.symm, huw, huw.symm, hw3, hw3.symm, hw0, hw0.symm,
                hu2, hu2.symm, hv23, hv23.symm, hv02, hv02.symm, hu3, hu3.symm, hv03, hv03.symm, hu0, hu0.symm]
          -- Triangles T₁ = v₀-w_max-v₂-v₀, T₂ = v₂-u'-v₃-v₂, T₃ = v₀-v₂-v₃-v₀
          let t1 : G.Walk v₀ v₀ := .cons hw0_adj.symm (.cons hw2_adj (.cons h02.symm .nil))
          let t2 : G.Walk v₂ v₂ := .cons hu2_adj.symm (.cons hu3_adj (.cons h23.symm .nil))
          let t3 : G.Walk v₀ v₀ := .cons h02 (.cons h23 (.cons h30 .nil))
          have ht1 : t1.IsCycle := by
            refine ⟨⟨⟨?_⟩, by simp [t1]⟩, ?_⟩
            · simp [t1, Sym2.eq_iff, hw0, hw0.symm, hw2, hw2.symm, hv02, hv02.symm]
            · simp [t1, hw2, hw2.symm, hw0, hw0.symm, hv02, hv02.symm]
          have ht2 : t2.IsCycle := by
            refine ⟨⟨⟨?_⟩, by simp [t2]⟩, ?_⟩
            · simp [t2, Sym2.eq_iff, hu2, hu2.symm, hu3, hu3.symm, hv23, hv23.symm]
            · simp [t2, hu3, hu3.symm, hu2, hu2.symm, hv23, hv23.symm]
          have ht3 : t3.IsCycle := by
            refine ⟨⟨⟨?_⟩, by simp [t3]⟩, ?_⟩
            · simp [t3, Sym2.eq_iff, hv02, hv02.symm, hv23, hv23.symm, hv03, hv03.symm]
            · simp [t3, hv23, hv23.symm, hv02, hv02.symm, hv03, hv03.symm]
          have hw_c5 := odd_cycle_weight_three S hnoc c5 hc5 ⟨2, by simp [c5]⟩
          have hw_t1 := odd_cycle_weight_three S hnoc t1 ht1 ⟨1, by simp [t1]⟩
          have hw_t2 := odd_cycle_weight_three S hnoc t2 ht2 ⟨1, by simp [t2]⟩
          have hw_t3 := odd_cycle_weight_three S hnoc t3 ht3 ⟨1, by simp [t3]⟩
          simp only [c5, t1, t2, t3, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hw_c5 hw_t1 hw_t2 hw_t3
          rw [Sym2.eq_swap (a := v₂) (b := v₀)] at hw_t1
          rw [Sym2.eq_swap (a := v₃) (b := v₂)] at hw_t2
          have h2_02 := two_mul_modFourWeight S.sign s(v₀, v₂)
          have h2_23 := two_mul_modFourWeight S.sign s(v₂, v₃)
          have hsum : (3 : ZMod 4) + 3 + 3 =
              (modFourWeight S.sign s(v₀, w_max) + modFourWeight S.sign s(w_max, v₂) +
                modFourWeight S.sign s(v₂, u') + modFourWeight S.sign s(u', v₃) +
                modFourWeight S.sign s(v₃, v₀)) +
              2 * modFourWeight S.sign s(v₀, v₂) + 2 * modFourWeight S.sign s(v₂, v₃) := by
            linear_combination -hw_t1 - hw_t2 - hw_t3
          rw [hw_c5, h2_02, h2_23] at hsum
          exact absurd hsum (by decide)
      · -- Subcase 1c: |T| ≥ 2! Two leaves u₁ ≠ u₂ share a neighbor on c = {v₀, v₂, v₃}
        have hT_ge2 : 2 ≤ T.card := by omega
        obtain ⟨u₁, u₂, hu₁T, hu₂T, hu12, hdeg1, hdeg2⟩ :=
          tree_two_leaves T hT_ge2 (hcomp_conn w_max) (hcomp_acyc w_max)
        have hnc_ge2 : ∀ u ∈ T, (T.filter fun w => G.Adj u w).card ≤ 1 →
            2 ≤ (c.support.toFinset.filter fun w => G.Adj u w).card := by
          intro u huT hdu
          have hdeg := min_deg_three_of_three_conn hcard h3 u
          have hle := Finset.card_le_card (hT_nbrs u huT)
          have hu_le := hle.trans (Finset.card_union_le _ _)
          rw [SimpleGraph.card_neighborFinset_eq_degree] at hu_le
          omega
        have hnc1 := hnc_ge2 u₁ hu₁T hdeg1
        have hnc2 := hnc_ge2 u₂ hu₂T hdeg2
        -- Pigeonhole on the 3-element set c.support.toFinset: u₁ and u₂ share a neighbor a ∈ c.support
        have hshared_nbr : ∃ a ∈ c.support.toFinset, G.Adj u₁ a ∧ G.Adj u₂ a := by
          let N1 := c.support.toFinset.filter fun w => G.Adj u₁ w
          let N2 := c.support.toFinset.filter fun w => G.Adj u₂ w
          have hcard_c : c.support.toFinset.card = 3 := by rw [cycle_support_card c hc, hc3]
          have hunion : (N1 ∪ N2).card ≤ 3 := by
            calc (N1 ∪ N2).card ≤ c.support.toFinset.card :=
                  Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
              _ = 3 := hcard_c
          have hinter : 0 < (N1 ∩ N2).card := by
            have := Finset.card_union_add_card_inter N1 N2; omega
          obtain ⟨a, ha⟩ := Finset.card_pos.mp hinter
          rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at ha
          exact ⟨a, ha.1.1, ha.1.2, ha.2.2⟩
        rcases hshared_nbr with ⟨a, haC_fin, hu1a, hu2a⟩
        -- u₁ also has a second neighbor b ∈ c.support \ {a}
        obtain ⟨b, hbN1, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (c.support.toFinset.filter fun w => G.Adj u₁ w).card) a
        have hbC_fin : b ∈ c.support.toFinset := (Finset.mem_filter.mp hbN1).1
        have hu1b : G.Adj u₁ b := (Finset.mem_filter.mp hbN1).2
        -- And there is a third vertex d ∈ c.support \ {a, b}
        have hcard_c : c.support.toFinset.card = 3 := by rw [cycle_support_card c hc, hc3]
        obtain ⟨d, hd_mem⟩ := Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, hbC_fin⟩), Finset.card_erase_of_mem haC_fin]; omega :
          0 < ((c.support.toFinset.erase a).erase b).card)
        have hdb : d ≠ b := (Finset.mem_erase.mp hd_mem).1
        have hda : d ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hd_mem).2).1
        have hdC_fin : d ∈ c.support.toFinset := (Finset.mem_erase.mp (Finset.mem_erase.mp hd_mem).2).2
        -- All 3 pairs among a, b, d are adjacent in G (since c is a triangle on {v₀, v₂, v₃})
        have htri_adj : ∀ x ∈ c.support.toFinset, ∀ y ∈ c.support.toFinset, x ≠ y → G.Adj x y := by
          intro x hx y hy hne
          have hx' := (hc_supp x).mp (List.mem_toFinset.mp hx)
          have hy' := (hc_supp y).mp (List.mem_toFinset.mp hy)
          rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
          first | exact absurd rfl hne | exact h02 | exact h02.symm | exact h23 | exact h23.symm | exact h30 | exact h30.symm
        have hab_adj : G.Adj a b := htri_adj a haC_fin b hbC_fin hba.symm
        have hbd_adj : G.Adj b d := htri_adj b hbC_fin d hdC_fin hdb.symm
        have hda_adj : G.Adj d a := htri_adj d hdC_fin a haC_fin hda
        -- Path P in T from u₁ to u₂
        obtain ⟨r⟩ := hcomp_conn w_max u₁ hu₁T u₂ hu₂T
        let rp := r.toPath
        let fT : G.induce (T : Set V) →g G := (SimpleGraph.Embedding.induce (T : Set V)).toHom
        let P : G.Walk u₁ u₂ := rp.1.map fT
        have hP : P.IsPath := rp.2.map (fun _ _ h => Subtype.ext h)
        have hP_T : ∀ z ∈ P.support, z ∈ T := by
          intro z hz; have hz' : z ∈ (rp.1.map fT).support := hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
          rcases hz' with ⟨z', _, rfl⟩; exact z'.2
        have hP_pos : 1 ≤ P.length := by cases P with | nil => exact absurd rfl hu12 | cons _ _ => simp
        have hP_nC : ∀ z ∈ P.support, z ∉ c.support.toFinset := fun z hz =>
          Finset.disjoint_left.mp hT_disj (hP_T z hz)
        -- Cycle C_a = a - u₁ -(P)- u₂ - a (length |P| + 2)
        have hstep_a : (SimpleGraph.Walk.cons hu1a.symm P).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP (fun hm => hP_nC a hm haC_fin)
        let e_au2 : G.Walk a u₂ := SimpleGraph.Walk.cons hu2a.symm .nil
        have he_au2 : e_au2.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e_au2, (G.ne_of_adj hu2a).symm])
        let C_a : G.Walk a a := (SimpleGraph.Walk.cons hu1a.symm P).append e_au2.reverse
        have hCa_cyc : C_a.IsCycle := by
          apply isCycle_append_reverse_of_disjoint e_au2 (SimpleGraph.Walk.cons hu1a.symm P) he_au2 hstep_a _
            (by simp [e_au2, SimpleGraph.Walk.length_cons]; omega)
          intro z _ hz1 hz2 hze; simp [e_au2] at hze; rcases hze with rfl | rfl <;> contradiction
        by_cases hP_ev : Even P.length
        · -- Even |P| → C_a is even, intersecting odd cycle c in {a}, contradicting Lemma 3.4(2)!
          have hCa_ev : Even C_a.length := by
            rcases hP_ev with ⟨k, hk⟩
            exact ⟨k + 1, by simp [C_a, e_au2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
          have hinter_a : C_a.support.toFinset ∩ c.support.toFinset = {a} := by
            ext z
            simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
            constructor
            · rintro ⟨hzCa, hzC⟩
              dsimp only [C_a] at hzCa
              rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzCa
              rcases hzCa with h1 | h2
              · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h1
                rcases h1 with rfl | hP'
                · rfl
                · exact False.elim (hP_nC z hP' (List.mem_toFinset.mpr hzC))
              · simp [e_au2] at h2
                rcases h2 with rfl | rfl
                · rfl
                · exact False.elim (Finset.disjoint_left.mp hT_disj hu₂T (List.mem_toFinset.mpr hzC))
            · rintro rfl
              exact ⟨SimpleGraph.Walk.start_mem_support C_a, List.mem_toFinset.mp haC_fin⟩
          exact False.elim (cycle_pair_obstructions_one_vertex_even_odd S hconn h3 hnoc C_a c hCa_cyc hc hCa_ev hodd hinter_a)
        · -- Odd |P| → 4 odd cycles C_a, C_b, c_abd, t_abu1 contradict NOC mod 4!
          rw [Nat.not_even_iff_odd] at hP_ev
          have hCa_odd : Odd C_a.length := by
            rcases hP_ev with ⟨k, hk⟩
            exact ⟨k + 1, by simp [C_a, e_au2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
          -- C_b = b - u₁ -(P)- u₂ - a - d - b (length |P| + 4, odd!)
          let p_bu2 : G.Walk b u₂ := SimpleGraph.Walk.cons hu1b.symm P
          have hp_bu2 : p_bu2.IsPath := SimpleGraph.Walk.IsPath.cons hP (fun hm => hP_nC b hm hbC_fin)
          let q_bu2 : G.Walk b u₂ := SimpleGraph.Walk.cons hbd_adj (SimpleGraph.Walk.cons hda_adj (SimpleGraph.Walk.cons hu2a.symm .nil))
          have hq_bu2 : q_bu2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
            have hu2b : u₂ ≠ b := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ hbC_fin)
            have hu2d : u₂ ≠ d := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ hdC_fin)
            have hu2a_ne : u₂ ≠ a := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ haC_fin)
            simp [q_bu2, hdb.symm, hba.symm, hda, hu2b.symm, hu2d.symm, hu2a_ne.symm])
          let C_b : G.Walk b b := p_bu2.append q_bu2.reverse
          have hCb_cyc : C_b.IsCycle := by
            apply isCycle_append_reverse_of_disjoint q_bu2 p_bu2 hq_bu2 hp_bu2 _
              (by simp [p_bu2, q_bu2]; omega)
            intro z hz hz1 hz2 hzq
            dsimp only [p_bu2] at hz
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hz with rfl | hzP
            · exact absurd rfl hz1
            · simp only [q_bu2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at hzq
              rcases hzq with rfl | rfl | rfl | rfl
              · exact absurd rfl hz1
              · exact hP_nC d hzP hdC_fin
              · exact hP_nC a hzP haC_fin
              · exact absurd rfl hz2
          have hCb_odd : Odd C_b.length := by
            rcases hP_ev with ⟨k, hk⟩
            exact ⟨k + 2, by simp [C_b, p_bu2, q_bu2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
          -- Triangles c_abd = a-b-d-a and t_abu1 = a-b-u₁-a
          let c_abd : G.Walk a a := .cons hab_adj (.cons hbd_adj (.cons hda_adj .nil))
          let t_abu1 : G.Walk a a := .cons hab_adj (.cons hu1b.symm (.cons hu1a .nil))
          have hcabd : c_abd.IsCycle := by
            refine ⟨⟨⟨?_⟩, by simp [c_abd]⟩, ?_⟩
            · simp [c_abd, Sym2.eq_iff, hba, hba.symm, hdb, hdb.symm, hda, hda.symm]
            · simp [c_abd, hdb, hdb.symm, hda, hda.symm, hba, hba.symm]
          have htabu1 : t_abu1.IsCycle := by
            have hu1a_ne : u₁ ≠ a := G.ne_of_adj hu1a
            have hu1b_ne : u₁ ≠ b := G.ne_of_adj hu1b
            refine ⟨⟨⟨?_⟩, by simp [t_abu1]⟩, ?_⟩
            · simp [t_abu1, Sym2.eq_iff, hba, hba.symm, hu1a_ne, hu1a_ne.symm, hu1b_ne, hu1b_ne.symm]
            · simp [t_abu1, hu1a_ne, hu1a_ne.symm, hu1b_ne, hu1b_ne.symm, hba, hba.symm]
          have hwCa := odd_cycle_weight_three S hnoc C_a hCa_cyc hCa_odd
          have hwCb := odd_cycle_weight_three S hnoc C_b hCb_cyc hCb_odd
          have hwCabd := odd_cycle_weight_three S hnoc c_abd hcabd ⟨1, by simp [c_abd]⟩
          have hwTabu1 := odd_cycle_weight_three S hnoc t_abu1 htabu1 ⟨1, by simp [t_abu1]⟩
          -- Expand weights of C_a, C_b, c_abd, t_abu1
          have hCa_exp : walkModFourWeight S.sign C_a =
              modFourWeight S.sign s(a, u₁) + walkModFourWeight S.sign P + modFourWeight S.sign s(a, u₂) := by
            simp only [C_a, e_au2, walkModFourWeight_append, walkModFourWeight_reverse]
            simp [walkModFourWeight, add_assoc]
          have hCb_exp : walkModFourWeight S.sign C_b =
              modFourWeight S.sign s(b, u₁) + walkModFourWeight S.sign P +
              modFourWeight S.sign s(b, d) + modFourWeight S.sign s(d, a) + modFourWeight S.sign s(a, u₂) := by
            simp only [C_b, p_bu2, q_bu2, walkModFourWeight_append, walkModFourWeight_reverse]
            simp [walkModFourWeight]; ring
          have hCabd_exp : walkModFourWeight S.sign c_abd =
              modFourWeight S.sign s(a, b) + modFourWeight S.sign s(b, d) + modFourWeight S.sign s(d, a) := by
            simp [c_abd, walkModFourWeight, add_assoc]
          have hTabu1_exp : walkModFourWeight S.sign t_abu1 =
              modFourWeight S.sign s(a, b) + modFourWeight S.sign s(b, u₁) + modFourWeight S.sign s(a, u₁) := by
            simp [t_abu1, walkModFourWeight, Sym2.eq_swap (a := u₁) (b := a), add_assoc]
          have hsum : (3 : ZMod 4) + 3 + 3 + 3 =
              2 * modFourWeight S.sign s(a, u₁) + 2 * modFourWeight S.sign s(b, u₁) +
              2 * walkModFourWeight S.sign P + 2 * modFourWeight S.sign s(a, u₂) +
              2 * modFourWeight S.sign s(b, d) + 2 * modFourWeight S.sign s(d, a) +
              2 * modFourWeight S.sign s(a, b) := by
            linear_combination -hwCa - hwCb - hwCabd - hwTabu1 + hCa_exp + hCb_exp + hCabd_exp + hTabu1_exp
          rw [two_mul_modFourWeight, two_mul_modFourWeight, two_mul_walkModFourWeight,
            two_mul_modFourWeight, two_mul_modFourWeight, two_mul_modFourWeight,
            two_mul_modFourWeight, (two_mul_nat_mod_four P.length).2 hP_ev] at hsum
          exact absurd hsum (by decide)
    · -- CASE 2: c.length ≥ 5 (odd)
      have hc_ge5 : 5 ≤ c.length := by rcases hodd with ⟨k, hk⟩; omega
      -- Every vertex u ∉ c.support has at most 2 neighbors on c!
      have hdeg_on_c_le2 : ∀ u : V, u ∉ c.support.toFinset →
          (c.support.toFinset.filter fun w => G.Adj u w).card ≤ 2 := by
        intro u hu
        by_contra hgt
        push Not at hgt
        let N := c.support.toFinset.filter fun w => G.Adj u w
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
        obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx]; omega : 0 < (N.erase x).card)
        have hyN : y ∈ N := (Finset.mem_erase.mp hy).2
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        obtain ⟨z, hz⟩ := Finset.card_pos.mp
          (by rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega : 0 < ((N.erase x).erase y).card)
        have hzN : z ∈ N := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
        have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
        have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
        have hxC : x ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
        have hyC : y ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hyN).1
        have hzC : z ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hzN).1
        have hux : G.Adj u x := (Finset.mem_filter.mp hx).2
        have huy : G.Adj u y := (Finset.mem_filter.mp hyN).2
        have huz : G.Adj u z := (Finset.mem_filter.mp hzN).2
        have huC : u ∉ c.support := fun h => hu (List.mem_toFinset.mpr h)
        obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, hAdisj, _, _, _⟩ := cycle_arcs_edges_subset c hc hxC hyC hyx.symm
        -- WLOG z lies on A_u (either A₁ or A₂)
        have h3split : ∀ (Au Ao : G.Walk x y), Au.IsPath → Ao.IsPath → Au.length + Ao.length = c.length →
            (∀ w, w ∈ Au.support ∨ w ∈ Ao.support ↔ w ∈ c.support) →
            (∀ w ∈ Au.support, w ≠ x → w ≠ y → w ∉ Ao.support) →
            z ∈ Au.support → False := by
          intro Au Ao hAu hAo hlen hsupp hdisj hzAu
          let P1 := Au.takeUntil z hzAu
          let P2 := Au.dropUntil z hzAu
          have hspec := SimpleGraph.Walk.take_spec Au hzAu
          have hsum12 : P1.length + P2.length = Au.length := by rw [← SimpleGraph.Walk.length_append, hspec]
          have hP1_pos : 1 ≤ P1.length := by cases P1 with | nil => exact absurd rfl hzx.symm | cons _ _ => simp
          have hP2_pos : 1 ≤ P2.length := by cases P2 with | nil => exact absurd rfl hzy | cons _ _ => simp
          have hAo_pos : 1 ≤ Ao.length := by cases Ao with | nil => exact absurd rfl hyx.symm | cons _ _ => simp
          -- Pair (x, y): arcs Au and Ao
          have hxy_2 := heven_arc_two u huC x y hxC hyC hyx.symm hux huy Au Ao hAu hAo hlen
            (fun w hw => (hsupp w).mp (Or.inl hw)) (fun w hw => (hsupp w).mp (Or.inr hw))
          -- Pair (x, z): arcs P1 and Ao.append P2.reverse
          have hAoP2 : (Ao.append P2.reverse).IsPath := by
            apply isPath_append_of_disjoint_pc Ao P2.reverse hAo (hAu.dropUntil hzAu).reverse
            intro w hw1 hw2
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw2
            have hwAu := SimpleGraph.Walk.support_dropUntil_subset Au hzAu hw2
            by_cases hwy : w = y
            · exact hwy
            · by_cases hwx : w = x
              · subst hwx
                have hnd := hAu.support_nodup
                rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                have hdc : P2.support = z :: P2.support.tail := by cases P2 <;> simp
                rw [hdc, List.mem_cons] at hw2
                exact False.elim (hnd.2.2 x (SimpleGraph.Walk.start_mem_support P1) x (hw2.resolve_left hzx.symm) rfl)
              · exact False.elim (hdisj w hwAu hwx hwy hw1)
          have hxz_2 := heven_arc_two u huC x z hxC hzC hzx.symm hux huz P1 (Ao.append P2.reverse)
            (hAu.takeUntil hzAu) hAoP2 (by simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega)
            (fun w hw => (hsupp w).mp (Or.inl (SimpleGraph.Walk.support_takeUntil_subset Au hzAu hw)))
            (fun w hw => by
              rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
              rcases hw with h1 | h2
              · exact (hsupp w).mp (Or.inr h1)
              · exact (hsupp w).mp (Or.inl (SimpleGraph.Walk.support_dropUntil_subset Au hzAu h2)))
          -- Pair (z, y): arcs P2 and P1.reverse.append Ao
          have hP1Ao : (P1.reverse.append Ao).IsPath := by
            apply isPath_append_of_disjoint_pc P1.reverse Ao (hAu.takeUntil hzAu).reverse hAo
            intro w hw1 hw2
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw1
            have hwAu := SimpleGraph.Walk.support_takeUntil_subset Au hzAu hw1
            by_cases hwx : w = x
            · exact hwx
            · by_cases hwy : w = y
              · subst hwy
                have hnd := hAu.support_nodup
                rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                have hdc : P2.support = z :: P2.support.tail := by cases P2 <;> simp
                have hyP2 : y ∈ P2.support := SimpleGraph.Walk.end_mem_support P2
                rw [hdc, List.mem_cons] at hyP2
                exact False.elim (hnd.2.2 y hw1 y (hyP2.resolve_left hzy.symm) rfl)
              · exact False.elim (hdisj w hwAu hwx hwy hw2)
          have hzy_2 := heven_arc_two u huC z y hzC hyC hzy huz huy P2 (P1.reverse.append Ao)
            (hAu.dropUntil hzAu) hP1Ao (by simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega)
            (fun w hw => (hsupp w).mp (Or.inl (SimpleGraph.Walk.support_dropUntil_subset Au hzAu hw)))
            (fun w hw => by
              rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
              rcases hw with h1 | h2
              · exact (hsupp w).mp (Or.inl (SimpleGraph.Walk.support_takeUntil_subset Au hzAu h1))
              · exact (hsupp w).mp (Or.inr h2))
          simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hxz_2 hzy_2
          rcases hodd with ⟨k, hk⟩
          rcases hxy_2 with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
          rcases hxz_2 with ⟨_, h2⟩ | ⟨_, h2⟩ <;>
          rcases hzy_2 with ⟨_, h3'⟩ | ⟨_, h3'⟩ <;> omega
        rcases (hAsupp z).mpr hzC with hz1 | hz2
        · exact h3split A₁ A₂ hA₁ hA₂ hAlen hAsupp hAdisj hz1
        · exact h3split A₂ A₁ hA₂ hA₁ (by omega) (fun w => by rw [or_comm]; exact hAsupp w)
            (fun w hw hwx hwy hm => hAdisj w hm hwx hwy hw) hz2
      -- Therefore |T| ≥ 2 (since any singleton component would have deg ≤ 2)
      have hT_ge2 : 2 ≤ T.card := by
        by_contra hlt
        have hT1 : T.card = 1 := by omega
        have hT_eq : T = {w_max} := by
          rcases Finset.card_eq_one.mp hT1 with ⟨a, ha⟩
          have hwa : w_max = a := Finset.mem_singleton.mp (ha ▸ hcomp_mem w_max hw_max_nC)
          rw [ha, hwa]
        have hdeg := min_deg_three_of_three_conn hcard h3 w_max
        have hle := Finset.card_le_card (hT_nbrs w_max (hcomp_mem w_max hw_max_nC))
        have hle2 := hle.trans (Finset.card_union_le _ _)
        have hT0 : (T.filter fun w => G.Adj w_max w).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro w hw; rw [hT_eq, Finset.mem_singleton] at hw; subst hw; exact G.loopless w_max
        have hc2 := hdeg_on_c_le2 w_max hw_max_nC
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hle2
        omega
      -- Pick two leaves u₁ ≠ u₂ of T
      obtain ⟨u₁, u₂, hu₁T, hu₂T, hu12, hdeg1, hdeg2⟩ :=
        tree_two_leaves T hT_ge2 (hcomp_conn w_max) (hcomp_acyc w_max)
      have hleaf_nc : ∀ u ∈ T, (T.filter fun w => G.Adj u w).card ≤ 1 →
          (c.support.toFinset.filter fun w => G.Adj u w).card = 2 := by
        intro u huT hdu
        have hdeg := min_deg_three_of_three_conn hcard h3 u
        have hle := (Finset.card_le_card (hT_nbrs u huT)).trans (Finset.card_union_le _ _)
        have hu_nC : u ∉ c.support.toFinset := Finset.disjoint_left.mp hT_disj huT
        have hle2 := hdeg_on_c_le2 u hu_nC
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
        omega
      have hnc1 := hleaf_nc u₁ hu₁T hdeg1
      have hnc2 := hleaf_nc u₂ hu₂T hdeg2
      -- Extract the 2 neighbors a, b of u₁ on c, joined by a 2-path a - m - b on c
      let N1 := c.support.toFinset.filter fun w => G.Adj u₁ w
      obtain ⟨a, haN1⟩ := Finset.card_pos.mp (by omega : 0 < N1.card)
      obtain ⟨b, hbN1, hba⟩ := Finset.exists_mem_ne (by omega : 1 < N1.card) a
      have haC : a ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp haN1).1
      have hbC : b ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hbN1).1
      have hu1a : G.Adj u₁ a := (Finset.mem_filter.mp haN1).2
      have hu1b : G.Adj u₁ b := (Finset.mem_filter.mp hbN1).2
      have hu1_nC : u₁ ∉ c.support := fun hm => Finset.disjoint_left.mp hT_disj hu₁T (List.mem_toFinset.mpr hm)
      obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, hAdisj, _, _, hAw⟩ :=
        cycle_arcs_edges_subset c hc haC hbC hba.symm
      -- WLOG short arc S_arc has length 2 and long arc L_arc has length c.length - 2 (odd)
      have hshort_long : ∃ (S_arc L_arc : G.Walk a b), S_arc.IsPath ∧ L_arc.IsPath ∧
          S_arc.length = 2 ∧ L_arc.length + 2 = c.length ∧
          (∀ w, w ∈ S_arc.support ∨ w ∈ L_arc.support ↔ w ∈ c.support) ∧
          (∀ w ∈ S_arc.support, w ≠ a → w ≠ b → w ∉ L_arc.support) ∧
          walkModFourWeight S.sign S_arc + walkModFourWeight S.sign L_arc = walkModFourWeight S.sign c := by
        rcases heven_arc_two u₁ hu1_nC a b haC hbC hba.symm hu1a hu1b A₁ A₂ hA₁ hA₂ hAlen
          (fun w hw => (hAsupp w).mp (Or.inl hw)) (fun w hw => (hAsupp w).mp (Or.inr hw)) with ⟨_, h1⟩ | ⟨_, h2⟩
        · exact ⟨A₁, A₂, hA₁, hA₂, h1, by omega, hAsupp, hAdisj, hAw S.sign⟩
        · exact ⟨A₂, A₁, hA₂, hA₁, h2, by omega, fun w => by rw [or_comm]; exact hAsupp w,
            fun w hw hwa hwb hm => hAdisj w hm hwa hwb hw, by rw [add_comm]; exact hAw S.sign⟩
      rcases hshort_long with ⟨S_arc, L_arc, hS_path, hL_path, hS2, hLlen, hSL_supp, hSL_disj, hSL_w⟩
      obtain ⟨m, hma, hmb, ham, hmb_adj, hS_supp, hS_edges⟩ := path_len_eq_two_mid S_arc hS_path hS2
      have hm_not_L : m ∉ L_arc.support :=
        hSL_disj m (by rw [hS_supp]; simp) hma hmb
      -- Weight of the 4-cycle Q = u₁ - a - m - b - u₁ is 0 mod 4!
      have hQ_w0 : modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(a, m) +
          modFourWeight S.sign s(m, b) + modFourWeight S.sign s(b, u₁) = 0 := by
        -- Odd cycle c' = (u₁ - a - u₁? No: a - u₁ - b ++ L_arc.reverse) has length c.length (odd)
        let r : G.Walk a b := SimpleGraph.Walk.cons hu1a.symm (SimpleGraph.Walk.cons hu1b .nil)
        have hr : r.IsPath := SimpleGraph.Walk.IsPath.mk' (by
          simp [r, hba.symm, (G.ne_of_adj hu1a).symm, G.ne_of_adj hu1b])
        have hc'_cyc : (r.append L_arc.reverse).IsCycle := by
          apply isCycle_append_reverse_of_disjoint L_arc r hL_path hr _ (by simp [r]; omega)
          intro z hzr hz1 hz2 hzL
          simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hzr
          rcases hzr with rfl | rfl | rfl
          · exact absurd rfl hz1
          · exact hu1_nC ((hSL_supp u₁).mp (Or.inr hzL))
          · exact absurd rfl hz2
        have hc'_odd : Odd (r.append L_arc.reverse).length := by
          rcases hodd with ⟨k, hk⟩
          exact ⟨k, by simp [r, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        have hw_c := odd_cycle_weight_three S hnoc c hc hodd
        have hw_c' := odd_cycle_weight_three S hnoc (r.append L_arc.reverse) hc'_cyc hc'_odd
        have hS_w : walkModFourWeight S.sign S_arc = modFourWeight S.sign s(a, m) + modFourWeight S.sign s(m, b) := by
          simp [walkModFourWeight, hS_edges]
        have hr_w : walkModFourWeight S.sign (r.append L_arc.reverse) =
            modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(b, u₁) + walkModFourWeight S.sign L_arc := by
          simp only [walkModFourWeight_append, walkModFourWeight_reverse, r, walkModFourWeight,
            SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
          rw [Sym2.eq_swap (a := a) (b := u₁), Sym2.eq_swap (a := u₁) (b := b)]; ring
        have hL_odd : Odd L_arc.length := by rcases hodd with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
        have h2L : 2 * walkModFourWeight S.sign L_arc = 2 := by
          rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four L_arc.length).2 hL_odd]
        have hsum : (3 : ZMod 4) + 3 =
            (modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(a, m) +
             modFourWeight S.sign s(m, b) + modFourWeight S.sign s(b, u₁)) +
            2 * walkModFourWeight S.sign L_arc := by
          linear_combination -hw_c - hw_c' - hSL_w + hS_w + hr_w
        rw [h2L] at hsum
        -- hsum : 3 + 3 = Q + 2, so Q = 0 in ZMod 4!
        have h6 : (3 : ZMod 4) + 3 = 2 := by decide
        rw [h6] at hsum
        calc modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(a, m) +
              modFourWeight S.sign s(m, b) + modFourWeight S.sign s(b, u₁)
            = (modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(a, m) +
               modFourWeight S.sign s(m, b) + modFourWeight S.sign s(b, u₁) + 2) - 2 := by ring
          _ = 2 - 2 := by rw [← hsum]
          _ = 0 := by decide
      -- Claim: No vertex in T has a neighbor in c.support \ {a, m, b}!
      have hNT_sub : ∀ w ∈ T, ∀ v₃ ∈ c.support, G.Adj w v₃ → v₃ = a ∨ v₃ = m ∨ v₃ = b := by
        intro w hwT v₃ hv₃C hwv3
        by_contra hnot
        push Not at hnot
        rcases hnot with ⟨hv3a, hv3m, hv3b⟩
        have hv3L : v₃ ∈ L_arc.support := by
          rcases (hSL_supp v₃).mpr hv₃C with hS | hL
          · rw [hS_supp] at hS; simp at hS; tauto
          · exact hL
        -- Path P_w in T from u₁ to w
        obtain ⟨rw⟩ := hcomp_conn w_max u₁ hu₁T w hwT
        let rwp := rw.toPath
        let fT : G.induce (T : Set V) →g G := (SimpleGraph.Embedding.induce (T : Set V)).toHom
        let P_w : G.Walk u₁ w := rwp.1.map fT
        have hPw : P_w.IsPath := rwp.2.map (fun _ _ h => Subtype.ext h)
        have hPw_T : ∀ z ∈ P_w.support, z ∈ T := by
          intro z hz; have hz' : z ∈ (rwp.1.map fT).support := hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
          rcases hz' with ⟨z', _, rfl⟩; exact z'.2
        have hPw_nC : ∀ z ∈ P_w.support, z ∉ c.support := fun z hz hm =>
          Finset.disjoint_left.mp hT_disj (hPw_T z hz) (List.mem_toFinset.mpr hm)
        let R : G.Walk u₁ v₃ := P_w.append (SimpleGraph.Walk.cons hwv3 .nil)
        have hR : R.IsPath := by
          apply isPath_append_of_disjoint_pc P_w (SimpleGraph.Walk.cons hwv3 .nil) hPw
            (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj hwv3]))
          intro z hz1 hz2
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hz2
          rcases hz2 with rfl | rfl
          · rfl
          · exact False.elim (hPw_nC v₃ hz1 hv₃C)
        have hR_int : ∀ z ∈ R.support, z ≠ v₃ → z ∉ c.support := by
          intro z hz hzv3
          dsimp only [R] at hz
          rw [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with h1 | h2
          · exact hPw_nC z h1
          · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl
            · exact hPw_nC w (SimpleGraph.Walk.end_mem_support P_w)
            · exact absurd rfl hzv3
        let L1 := L_arc.takeUntil v₃ hv3L
        let L2 := L_arc.dropUntil v₃ hv3L
        have hspecL := SimpleGraph.Walk.take_spec L_arc hv3L
        have hL_sum : L1.length + L2.length = L_arc.length := by rw [← SimpleGraph.Walk.length_append, hspecL]
        have hL1_pos : 1 ≤ L1.length := by cases L1 with | nil => exact absurd rfl hv3a.symm | cons _ _ => simp
        have hL2_pos : 1 ≤ L2.length := by cases L2 with | nil => exact absurd rfl hv3b | cons _ _ => simp
        have hR_pos : 1 ≤ R.length := by
          simp [R, SimpleGraph.Walk.length_append]
        -- Helper: given endpoint x ∈ {a, b}, other y ∈ {a, b}, subarc Lx : x → v₃ avoiding {y, m}
        -- with Odd (R.length + Lx.length + 1), get contradiction via Q_u1!
        have hside : ∀ (x y : V) (hyC : y ∈ c.support) (hux : G.Adj u₁ x) (huy : G.Adj u₁ y) (hxm : G.Adj x m) (hmy : G.Adj m y)
            (hxy : x ≠ y) (hxm_ne : x ≠ m) (hym_ne : y ≠ m) (hv3x : v₃ ≠ x) (hv3y : v₃ ≠ y)
            (Lx : G.Walk x v₃), Lx.IsPath → 1 ≤ Lx.length →
            (∀ z ∈ Lx.support, z ∈ c.support) → y ∉ Lx.support → m ∉ Lx.support →
            Odd (R.length + Lx.length + 1) →
            modFourWeight S.sign s(u₁, x) + modFourWeight S.sign s(x, m) +
              modFourWeight S.sign s(m, y) + modFourWeight S.sign s(y, u₁) = 0 → False := by
          intro x y hyC hux huy hxm hmy hxy hxm_ne hym_ne hv3x hv3y Lx hLx hLx_pos hLxC hyLx hmLx hodd_side hQ0
          let RL : G.Walk u₁ x := R.append Lx.reverse
          have hRL : RL.IsPath := by
            apply isPath_append_of_disjoint_pc R Lx.reverse hR hLx.reverse
            intro z hz1 hz2
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz2
            by_contra hzv3
            exact hR_int z hz1 hzv3 (hLxC z hz2)
          -- Cycle 1: RL ++ (x - u₁)
          let e1 : G.Walk u₁ x := SimpleGraph.Walk.cons hux .nil
          have he1 : e1.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e1, G.ne_of_adj hux])
          let C1 : G.Walk u₁ u₁ := RL.append e1.reverse
          have hC1 : C1.IsCycle := by
            apply isCycle_append_reverse_of_disjoint e1 RL he1 hRL _
              (by simp [RL, e1, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega)
            intro z _ hz1 hz2 hze; simp [e1] at hze; rcases hze with rfl | rfl <;> contradiction
          have hC1_odd : Odd C1.length := by
            simpa [C1, RL, e1, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using hodd_side
          -- Cycle 2: RL ++ (x - m - y - u₁)
          let e2 : G.Walk u₁ x := SimpleGraph.Walk.cons huy (SimpleGraph.Walk.cons hmy.symm (SimpleGraph.Walk.cons hxm.symm .nil))
          have he2 : e2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
            have hu1m : u₁ ≠ m := fun h => hu1_nC (h ▸ (hSL_supp m).mp (Or.inl (by rw [hS_supp]; simp)))
            simp [e2, G.ne_of_adj huy, hu1m, G.ne_of_adj hux, hym_ne, hxy.symm, hxm_ne.symm])
          let C2 : G.Walk u₁ u₁ := RL.append e2.reverse
          have hC2 : C2.IsCycle := by
            apply isCycle_append_reverse_of_disjoint e2 RL he2 hRL _
              (by simp [RL, e2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega)
            intro z hzRL hz1 hz2 hze2
            simp only [e2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hze2
            dsimp only [RL] at hzRL
            rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzRL
            rcases hze2 with rfl | rfl | rfl | rfl
            · exact absurd rfl hz1
            · rcases hzRL with h1 | h2
              · exact hR_int y h1 hv3y.symm hyC
              · exact hyLx h2
            · rcases hzRL with h1 | h2
              · exact hR_int m h1 hv3m.symm ((hSL_supp m).mp (Or.inl (by rw [hS_supp]; simp)))
              · exact hmLx h2
            · exact absurd rfl hz2
          have hC2_odd : Odd C2.length := by
            rcases hodd_side with ⟨k, hk⟩
            exact ⟨k + 1, by simp [C2, RL, e2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
          have hw1 := odd_cycle_weight_three S hnoc C1 hC1 hC1_odd
          have hw2 := odd_cycle_weight_three S hnoc C2 hC2 hC2_odd
          have hRL_ev : Even RL.length := by
            rcases hodd_side with ⟨k, hk⟩
            exact ⟨k, by simp [RL, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
          have h2RL : 2 * walkModFourWeight S.sign RL = 0 := by
            rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four RL.length).1 hRL_ev]
          have h1_exp : walkModFourWeight S.sign C1 = walkModFourWeight S.sign RL + modFourWeight S.sign s(u₁, x) := by
            simp only [C1, e1, walkModFourWeight_append, walkModFourWeight_reverse, walkModFourWeight,
              SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, add_zero]
          have h2_exp : walkModFourWeight S.sign C2 = walkModFourWeight S.sign RL +
              modFourWeight S.sign s(x, m) + modFourWeight S.sign s(m, y) + modFourWeight S.sign s(y, u₁) := by
            simp only [C2, e2, walkModFourWeight_append, walkModFourWeight_reverse, walkModFourWeight,
              SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, add_zero]
            rw [Sym2.eq_swap (a := u₁) (b := y), Sym2.eq_swap (a := y) (b := m), Sym2.eq_swap (a := m) (b := x)]
            ring
          have hsum : (3 : ZMod 4) + 3 =
              2 * walkModFourWeight S.sign RL +
              (modFourWeight S.sign s(u₁, x) + modFourWeight S.sign s(x, m) +
               modFourWeight S.sign s(m, y) + modFourWeight S.sign s(y, u₁)) := by
            linear_combination -hw1 - hw2 + h1_exp + h2_exp
          rw [h2RL, hQ0] at hsum
          exact absurd hsum (by decide)
        --Wait: avoid the messy hy_nS in hside by passing hyC : y ∈ c.support!
        have hb_not_L1 : b ∉ L1.support := by
          intro hb1
          have hnd := hL_path.support_nodup
          rw [← hspecL, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
          have hdc : L2.support = v₃ :: L2.support.tail := by cases L2 <;> simp
          have hb2 : b ∈ L2.support := SimpleGraph.Walk.end_mem_support L2
          rw [hdc, List.mem_cons] at hb2
          exact hnd.2.2 b hb1 b (hb2.resolve_left hv3b.symm) rfl
        have ha_not_L2 : a ∉ L2.support := by
          intro ha2
          have hnd := hL_path.support_nodup
          rw [← hspecL, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
          have hdc : L2.support = v₃ :: L2.support.tail := by cases L2 <;> simp
          rw [hdc, List.mem_cons] at ha2
          exact hnd.2.2 a (SimpleGraph.Walk.start_mem_support L1) a (ha2.resolve_left hv3a.symm) rfl
        by_cases h1 : Odd (R.length + L1.length + 1)
        · exact hside a b hbC hu1a hu1b ham hmb_adj hba.symm hma.symm hmb.symm hv3a hv3b L1
            (hL_path.takeUntil hv3L) hL1_pos
            (fun z hz => (hSL_supp z).mp (Or.inr (SimpleGraph.Walk.support_takeUntil_subset L_arc hv3L hz)))
            hb_not_L1 (fun hm => hm_not_L (SimpleGraph.Walk.support_takeUntil_subset L_arc hv3L hm)) h1 hQ_w0
        · have h2 : Odd (R.length + L2.length + 1) := by
            rw [Nat.not_odd_iff_even] at h1
            rcases hodd with ⟨k, hk⟩; rcases h1 with ⟨j, hj⟩
            exact ⟨R.length + k - j - 1, by omega⟩
          have hQ0' : modFourWeight S.sign s(u₁, b) + modFourWeight S.sign s(b, m) +
              modFourWeight S.sign s(m, a) + modFourWeight S.sign s(a, u₁) = 0 := by
            rw [Sym2.eq_swap (a := u₁) (b := b), Sym2.eq_swap (a := b) (b := m),
                Sym2.eq_swap (a := m) (b := a), Sym2.eq_swap (a := a) (b := u₁)]
            rw [← hQ_w0]; ring
          exact hside b a haC hu1b hu1a hmb_adj.symm ham.symm hba hmb.symm hma.symm hv3b hv3a L2.reverse
            (hL_path.dropUntil hv3L).reverse (by simp [hL2_pos])
            (fun z hz => (hSL_supp z).mp (Or.inr (SimpleGraph.Walk.support_dropUntil_subset L_arc hv3L (by simpa [SimpleGraph.Walk.support_reverse] using hz))))
            (by simpa [SimpleGraph.Walk.support_reverse] using ha_not_L2)
            (fun hm => hm_not_L (SimpleGraph.Walk.support_dropUntil_subset L_arc hv3L (by simpa [SimpleGraph.Walk.support_reverse] using hm)))
            (by simpa [SimpleGraph.Walk.length_reverse] using h2) hQ0'
      -- Now examine the second leaf u₂ ∈ T \ {u₁}: its 2 neighbors on c must be {a, b}!
      have hu2_not_m : ¬ G.Adj u₂ m := by
        intro hu2m
        let N2 := c.support.toFinset.filter fun w => G.Adj u₂ w
        have hmN2 : m ∈ N2 := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((hSL_supp m).mp (Or.inl (by rw [hS_supp]; simp))), hu2m⟩
        obtain ⟨z, hzN2, hzm⟩ := Finset.exists_mem_ne (by omega : 1 < N2.card) m
        have hzC : z ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hzN2).1
        have hu2z : G.Adj u₂ z := (Finset.mem_filter.mp hzN2).2
        have hzm_adj : G.Adj z m := by
          rcases hNT_sub u₂ hu₂T z hzC hu2z with rfl | rfl | rfl
          · exact ham
          · exact absurd rfl hzm
          · exact hmb_adj.symm
        -- Triangle u₂ - z - m - u₂ has length 3 < 5 ≤ c.length!
        let tri : G.Walk u₂ u₂ := .cons hu2z (.cons hzm_adj (.cons hu2m.symm .nil))
        have htri : tri.IsCycle := by
          refine ⟨⟨⟨?_⟩, by simp [tri]⟩, ?_⟩
          · simp [tri, Sym2.eq_iff, G.ne_of_adj hu2z, (G.ne_of_adj hu2z).symm,
              G.ne_of_adj hu2m, (G.ne_of_adj hu2m).symm, hzm, hzm.symm]
          · simp [tri, G.ne_of_adj hu2z, (G.ne_of_adj hu2z).symm,
              G.ne_of_adj hu2m, (G.ne_of_adj hu2m).symm, hzm, hzm.symm]
        have hle := hmin_odd tri htri ⟨1, by simp [tri]⟩
        simp [tri] at hle; omega
      have hu2a : G.Adj u₂ a := by
        let N2 := c.support.toFinset.filter fun w => G.Adj u₂ w
        have hsub : N2 ⊆ {a, b} := by
          intro z hz
          have hzC : z ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hz).1
          have hu2z : G.Adj u₂ z := (Finset.mem_filter.mp hz).2
          rcases hNT_sub u₂ hu₂T z hzC hu2z with rfl | rfl | rfl
          · simp
          · exact absurd hu2z hu2_not_m
          · simp
        have heq : N2 = {a, b} := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hba.symm]; omega)
        have : a ∈ N2 := by rw [heq]; simp
        exact (Finset.mem_filter.mp this).2
      -- Path P in T from u₁ to u₂
      obtain ⟨r⟩ := hcomp_conn w_max u₁ hu₁T u₂ hu₂T
      let rp := r.toPath
      let fT : G.induce (T : Set V) →g G := (SimpleGraph.Embedding.induce (T : Set V)).toHom
      let P : G.Walk u₁ u₂ := rp.1.map fT
      have hP : P.IsPath := rp.2.map (fun _ _ h => Subtype.ext h)
      have hP_T : ∀ z ∈ P.support, z ∈ T := by
        intro z hz; have hz' : z ∈ (rp.1.map fT).support := hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
        rcases hz' with ⟨z', _, rfl⟩; exact z'.2
      have hP_nC : ∀ z ∈ P.support, z ∉ c.support.toFinset := fun z hz =>
        Finset.disjoint_left.mp hT_disj (hP_T z hz)
      have hP_pos : 1 ≤ P.length := by cases P with | nil => exact absurd rfl hu12 | cons _ _ => simp
      -- Cycle C_a = a - u₁ -(P)- u₂ - a (length |P| + 2)
      have haC_fin : a ∈ c.support.toFinset := List.mem_toFinset.mpr haC
      have hbC_fin : b ∈ c.support.toFinset := List.mem_toFinset.mpr hbC
      have hmC_fin : m ∈ c.support.toFinset := List.mem_toFinset.mpr ((hSL_supp m).mp (Or.inl (by rw [hS_supp]; simp)))
      have hstep_a : (SimpleGraph.Walk.cons hu1a.symm P).IsPath :=
        SimpleGraph.Walk.IsPath.cons hP (fun hm => hP_nC a hm haC_fin)
      let e_au2 : G.Walk a u₂ := SimpleGraph.Walk.cons hu2a.symm .nil
      have he_au2 : e_au2.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e_au2, (G.ne_of_adj hu2a).symm])
      let C_a : G.Walk a a := (SimpleGraph.Walk.cons hu1a.symm P).append e_au2.reverse
      have hCa_cyc : C_a.IsCycle := by
        apply isCycle_append_reverse_of_disjoint e_au2 (SimpleGraph.Walk.cons hu1a.symm P) he_au2 hstep_a _
          (by simp [e_au2, SimpleGraph.Walk.length_cons]; omega)
        intro z _ hz1 hz2 hze; simp [e_au2] at hze; rcases hze with rfl | rfl <;> contradiction
      by_cases hP_ev : Even P.length
      · -- Even |P| → C_a is even, intersecting odd cycle c in {a}, contradicting Lemma 3.4(2)!
        have hCa_ev : Even C_a.length := by
          rcases hP_ev with ⟨k, hk⟩
          exact ⟨k + 1, by simp [C_a, e_au2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        have hinter_a : C_a.support.toFinset ∩ c.support.toFinset = {a} := by
          ext z
          simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
          constructor
          · rintro ⟨hzCa, hzC⟩
            dsimp only [C_a] at hzCa
            rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzCa
            rcases hzCa with h1 | h2
            · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h1
              rcases h1 with rfl | hP'
              · rfl
              · exact False.elim (hP_nC z hP' (List.mem_toFinset.mpr hzC))
            · simp [e_au2] at h2
              rcases h2 with rfl | rfl
              · rfl
              · exact False.elim (Finset.disjoint_left.mp hT_disj hu₂T (List.mem_toFinset.mpr hzC))
          · rintro rfl
            exact ⟨SimpleGraph.Walk.start_mem_support C_a, haC⟩
        exact False.elim (cycle_pair_obstructions_one_vertex_even_odd S hconn h3 hnoc C_a c hCa_cyc hc hCa_ev hodd hinter_a)
      · -- Odd |P| → C_a and C_b = a - m - b - u₁ -(P)- u₂ - a are both odd, sum = 2*w(P)+2*w(u₂a)+w(Q) = 0 ≠ 2!
        rw [Nat.not_even_iff_odd] at hP_ev
        have hCa_odd : Odd C_a.length := by
          rcases hP_ev with ⟨k, hk⟩
          exact ⟨k + 1, by simp [C_a, e_au2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        let p_bu2 : G.Walk b u₂ := SimpleGraph.Walk.cons hu1b.symm P
        have hp_bu2 : p_bu2.IsPath := SimpleGraph.Walk.IsPath.cons hP (fun hm => hP_nC b hm hbC_fin)
        let q_bu2 : G.Walk b u₂ := SimpleGraph.Walk.cons hmb_adj.symm (SimpleGraph.Walk.cons ham.symm (SimpleGraph.Walk.cons hu2a.symm .nil))
        have hq_bu2 : q_bu2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
          have hu2b : u₂ ≠ b := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ hbC_fin)
          have hu2m : u₂ ≠ m := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ hmC_fin)
          have hu2a_ne : u₂ ≠ a := fun h => Finset.disjoint_left.mp hT_disj hu₂T (h ▸ haC_fin)
          simp [q_bu2, hmb.symm, hba, hma, hu2b.symm, hu2m.symm, hu2a_ne.symm])
        let C_b : G.Walk b b := p_bu2.append q_bu2.reverse
        have hCb_cyc : C_b.IsCycle := by
          apply isCycle_append_reverse_of_disjoint q_bu2 p_bu2 hq_bu2 hp_bu2 _
            (by simp [p_bu2, q_bu2]; omega)
          intro z hz hz1 hz2 hzq
          dsimp only [p_bu2] at hz
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hzP
          · exact absurd rfl hz1
          · simp only [q_bu2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hzq
            rcases hzq with rfl | rfl | rfl | rfl
            · exact absurd rfl hz1
            · exact hP_nC m hzP hmC_fin
            · exact hP_nC a hzP haC_fin
            · exact absurd rfl hz2
        have hCb_odd : Odd C_b.length := by
          rcases hP_ev with ⟨k, hk⟩
          exact ⟨k + 2, by simp [C_b, p_bu2, q_bu2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        have hwCa := odd_cycle_weight_three S hnoc C_a hCa_cyc hCa_odd
        have hwCb := odd_cycle_weight_three S hnoc C_b hCb_cyc hCb_odd
        have hCa_exp : walkModFourWeight S.sign C_a =
            modFourWeight S.sign s(u₁, a) + walkModFourWeight S.sign P + modFourWeight S.sign s(a, u₂) := by
          simp only [C_a, e_au2, walkModFourWeight_append, walkModFourWeight_reverse, walkModFourWeight,
            SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
          rw [Sym2.eq_swap (a := a) (b := u₁)]; ring
        have hCb_exp : walkModFourWeight S.sign C_b =
            modFourWeight S.sign s(b, u₁) + walkModFourWeight S.sign P +
            modFourWeight S.sign s(m, b) + modFourWeight S.sign s(a, m) + modFourWeight S.sign s(a, u₂) := by
          simp only [C_b, p_bu2, q_bu2, walkModFourWeight_append, walkModFourWeight_reverse, walkModFourWeight,
            SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
          rw [Sym2.eq_swap (a := b) (b := m), Sym2.eq_swap (a := m) (b := a)]; ring
        have hsum : (3 : ZMod 4) + 3 =
            2 * walkModFourWeight S.sign P + 2 * modFourWeight S.sign s(a, u₂) +
            (modFourWeight S.sign s(u₁, a) + modFourWeight S.sign s(a, m) +
             modFourWeight S.sign s(m, b) + modFourWeight S.sign s(b, u₁)) := by
          linear_combination -hwCa - hwCb + hCa_exp + hCb_exp
        rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four P.length).2 hP_ev,
          two_mul_modFourWeight, hQ_w0] at hsum
        exact absurd hsum (by decide)

end SignedGraphs
