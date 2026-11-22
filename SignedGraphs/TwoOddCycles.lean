import SignedGraphs.PetersenSwitching

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000 in
/-- **Lemma 3.4(3)** (complete zero-sorry proof): If a 3-connected NOC signed graph contains two
vertex-disjoint odd cycles, then it is switching-isomorphic to `(Petersen, -1)`. -/
theorem cycle_pair_obstructions_two_disjoint_odd_impl (S : SignedGraph V)
    (hconn : S.graph.Preconnected)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {v₁₀ v₂₀ : V} (c₁₀ : S.graph.Walk v₁₀ v₁₀) (c₂₀ : S.graph.Walk v₂₀ v₂₀)
    (hc₁₀ : c₁₀.IsCycle) (hc₂₀ : c₂₀.IsCycle)
    (hodd₁₀ : Odd c₁₀.length) (hodd₂₀ : Odd c₂₀.length)
    (hdisj₀ : Disjoint c₁₀.support.toFinset c₂₀.support.toFinset) :
    SwitchingIso S petersenSignedGraph := by
  classical
  let G := S.graph
  -- Step 1: Minimize |C₁| + |C₂| over all pairs of disjoint odd cycles
  have hex_pair : ∃ n : ℕ, ∃ (v₁ v₂ : V) (c₁ : G.Walk v₁ v₁) (c₂ : G.Walk v₂ v₂),
      c₁.IsCycle ∧ c₂.IsCycle ∧ Odd c₁.length ∧ Odd c₂.length ∧
      Disjoint c₁.support.toFinset c₂.support.toFinset ∧ c₁.length + c₂.length = n :=
    ⟨c₁₀.length + c₂₀.length, v₁₀, v₂₀, c₁₀, c₂₀, hc₁₀, hc₂₀, hodd₁₀, hodd₂₀, hdisj₀, rfl⟩
  obtain ⟨v₁, v₂, c₁, c₂, hc₁, hc₂, hodd₁, hodd₂, hdisj, hsum_eq⟩ := Nat.find_spec hex_pair
  have hmin_sum : ∀ {u₁ u₂ : V} (d₁ : G.Walk u₁ u₁) (d₂ : G.Walk u₂ u₂),
      d₁.IsCycle → d₂.IsCycle → Odd d₁.length → Odd d₂.length →
      Disjoint d₁.support.toFinset d₂.support.toFinset →
      c₁.length + c₂.length ≤ d₁.length + d₂.length := by
    intro u₁ u₂ d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj
    rw [hsum_eq]
    exact Nat.find_min' hex_pair ⟨u₁, u₂, d₁, d₂, hd₁, hd₂, ho₁, ho₂, hdj, rfl⟩
  let C1 : Finset V := c₁.support.toFinset
  let C2 : Finset V := c₂.support.toFinset
  have hC1_card : C1.card = c₁.length := cycle_support_card c₁ hc₁
  have hC2_card : C2.card = c₂.length := cycle_support_card c₂ hc₂
  have hc1_ge3 : 3 ≤ c₁.length := hc₁.three_le_length
  have hc2_ge3 : 3 ≤ c₂.length := hc₂.three_le_length
  have hcard_ge6 : 6 ≤ Fintype.card V := by
    have hu : (C1 ∪ C2).card ≤ Fintype.card V := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hC1_card, hC2_card] at hu
    omega
  have hcard_ge4 : 4 ≤ Fintype.card V := by omega
  -- Helper: chordlessness of any cycle in a minimal disjoint odd pair
  have hchordless_gen : ∀ {u₁ u₂ : V} (d₁ : G.Walk u₁ u₁) (d₂ : G.Walk u₂ u₂),
      d₁.IsCycle → d₂.IsCycle → Odd d₁.length → Odd d₂.length →
      Disjoint d₁.support.toFinset d₂.support.toFinset →
      d₁.length + d₂.length = c₁.length + c₂.length →
      ∀ x ∈ d₁.support, ∀ y ∈ d₁.support, G.Adj x y → s(x, y) ∈ d₁.edges := by
    intro u₁ u₂ d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj hsum x hx y hy hxy
    by_contra hch
    have hne : x ≠ y := G.ne_of_adj hxy
    obtain ⟨p₁, p₂, hp₁, hp₂, hlen, hsupp, _, hp₁_e, hp₂_e, _⟩ := cycle_arcs_edges_subset d₁ hd₁ hx hy hne
    have hge2 : ∀ (p : G.Walk x y), (∀ e ∈ p.edges, e ∈ d₁.edges) → 2 ≤ p.length := by
      intro p hpe; cases p with
      | nil => exact absurd rfl hne
      | @cons _ w _ _ r => cases r with
        | nil => exact False.elim (hch (hpe s(x, w) (by simp)))
        | cons _ _ => simp
    have htry : ∀ (p : G.Walk x y), p.IsPath → Even p.length → 2 ≤ p.length → p.length + 1 < d₁.length →
        (∀ z ∈ p.support, z ∈ d₁.support) → False := by
      intro p hp hev h2 hlt hpC
      let q : G.Walk x y := SimpleGraph.Walk.cons hxy .nil
      have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [q, hne])
      let d₁' : G.Walk x x := q.append p.reverse
      have hd₁' : d₁'.IsCycle := by
        apply isCycle_append_reverse_of_disjoint p q hp hq _ (by simp [q]; omega)
        intro z hz h1 h2'; simp [q] at hz; rcases hz with rfl | rfl <;> contradiction
      have ho₁' : Odd d₁'.length := by
        rcases hev with ⟨k, hk⟩
        exact ⟨k, by simp [d₁', q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      have hsub : d₁'.support.toFinset ⊆ d₁.support.toFinset := by
        intro z hz; have hz' := List.mem_toFinset.mp hz
        dsimp only [d₁'] at hz'
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
        rcases hz' with hq' | hp'
        · simp [q] at hq'; rcases hq' with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
        · exact List.mem_toFinset.mpr (hpC z hp')
      have hle := hmin_sum d₁' d₂ hd₁' hd₂ ho₁' ho₂ (hdj.mono_left hsub)
      simp only [d₁', q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
      omega
    have hp1_2 := hge2 p₁ hp₁_e
    have hp2_2 := hge2 p₂ hp₂_e
    by_cases hev1 : Even p₁.length
    · exact htry p₁ hp₁ hev1 hp1_2 (by omega) (fun z hz => (hsupp z).mp (Or.inl hz))
    · rw [Nat.not_even_iff_odd] at hev1
      have hev2 : Even p₂.length := by rcases ho₁ with ⟨a, ha⟩; rcases hev1 with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
      exact htry p₂ hp₂ hev2 hp2_2 (by omega) (fun z hz => (hsupp z).mp (Or.inr hz))
  have hc1_chordless := hchordless_gen c₁ c₂ hc₁ hc₂ hodd₁ hodd₂ hdisj rfl
  have hc2_chordless := hchordless_gen c₂ c₁ hc₂ hc₁ hodd₂ hodd₁ hdisj.symm (add_comm _ _)
  -- Step 2: V = V(C₁) ∪ V(C₂)
  have hV_cov : ∀ x : V, x ∈ C1 ∨ x ∈ C2 := by
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨w₀, hw₀1, hw₀2⟩
    let U : Finset V := C1 ∪ C2
    have hw₀U : w₀ ∉ U := by simp [U, hw₀1, hw₀2]
    let Q : Finset V := Finset.univ.filter fun u =>
      ∃ hu : u ∈ ((U : Set V)ᶜ), (G.induce ((U : Set V)ᶜ)).Reachable ⟨w₀, hw₀U⟩ ⟨u, hu⟩
    have hw₀Q : w₀ ∈ Q := by simp [Q]; exact ⟨hw₀U, SimpleGraph.Reachable.refl _⟩
    have hQ_disj : Disjoint Q U := by
      rw [Finset.disjoint_left]; intro x hx; simp [Q] at hx; exact hx.1
    have hQ_closed : ∀ x ∈ Q, ∀ y : V, G.Adj x y → y ∈ Q ∪ U := by
      intro x hx y hxy
      by_cases hyU : y ∈ U
      · exact Finset.mem_union_right _ hyU
      · refine Finset.mem_union_left _ ?_
        simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨hxU, hr⟩
        exact ⟨hyU, hr.trans (SimpleGraph.Adj.reachable (show (G.induce ((U : Set V)ᶜ)).Adj ⟨x, hxU⟩ ⟨y, hyU⟩ from hxy))⟩
    have hQ_conn : ∀ (x : V) (hx : x ∈ Q) (y : V) (hy : y ∈ Q), (G.induce (Q : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x hx y hy
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hx with ⟨hxU, hrx⟩; rcases hy with ⟨hyU, hry⟩
      obtain ⟨r⟩ := hrx.symm.trans hry
      let fU : G.induce ((U : Set V)ᶜ) →g G := (SimpleGraph.Embedding.induce ((U : Set V)ᶜ)).toHom
      have hrQ : ∀ z ∈ (r.map fU).support, z ∈ Q := by
        intro z hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
        rcases hz with ⟨z', hz', rfl⟩
        simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨z'.2, hrx.trans ⟨r.takeUntil z' hz'⟩⟩
      exact ⟨(r.map fU).induce (Q : Set V) hrQ⟩
    let NQ : Finset V := U.filter fun u => ∃ x ∈ Q, G.Adj x u
    have hNQ_card : 3 ≤ NQ.card := by
      -- Need a vertex outside Q ∪ NQ? Wait: if U ⊆ NQ, then NQ.card = U.card ≥ 6 ≥ 3!
      by_cases hex_out : ∃ z : V, z ∉ Q ∧ z ∉ NQ
      · rcases hex_out with ⟨z, hzQ, hzNQ⟩
        apply sep_card_ge_three_of_three_conn h3 Q NQ w₀ z hw₀Q hzQ hzNQ (hQ_disj.mono_right (Finset.filter_subset _ _))
        intro x hx y hxy
        rcases Finset.mem_union.mp (hQ_closed x hx y hxy) with h1 | h2
        · exact Finset.mem_union_left _ h1
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h2, x, hx, hxy⟩)
      · push Not at hex_out
        have hsub : U ⊆ NQ := fun z hz => hex_out z (Finset.disjoint_right.mp hQ_disj hz)
        have hle := Finset.card_le_card hsub
        have hU_card : U.card = c₁.length + c₂.length := by
          rw [Finset.card_union_of_disjoint hdisj, hC1_card, hC2_card]
        omega
    -- By pigeonhole, Q has ≥ 2 neighbors on C₁ or ≥ 2 neighbors on C₂
    have htwo_on_one : ∀ {u₁ u₂ : V} (d₁ : G.Walk u₁ u₁) (d₂ : G.Walk u₂ u₂),
        d₁.IsCycle → d₂.IsCycle → Odd d₁.length → Odd d₂.length →
        Disjoint d₁.support.toFinset d₂.support.toFinset →
        Disjoint Q d₁.support.toFinset → Disjoint Q d₂.support.toFinset →
        2 ≤ (d₁.support.toFinset.filter fun u => ∃ x ∈ Q, G.Adj x u).card → False := by
      intro u₁ u₂ d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj hQd1 hQd2 hge2
      let N := d₁.support.toFinset.filter fun u => ∃ x ∈ Q, G.Adj x u
      obtain ⟨a, haN⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
      obtain ⟨b, hbN, hba⟩ := Finset.exists_mem_ne (by omega : 1 < N.card) a
      have haD : a ∈ d₁.support := List.mem_toFinset.mp (Finset.mem_filter.mp haN).1
      have hbD : b ∈ d₁.support := List.mem_toFinset.mp (Finset.mem_filter.mp hbN).1
      rcases (Finset.mem_filter.mp haN).2 with ⟨xa, hxaQ, hxa_adj⟩
      rcases (Finset.mem_filter.mp hbN).2 with ⟨xb, hxbQ, hxb_adj⟩
      obtain ⟨r⟩ := hQ_conn xa hxaQ xb hxbQ
      let rp := r.toPath
      let fQ : G.induce (Q : Set V) →g G := (SimpleGraph.Embedding.induce (Q : Set V)).toHom
      let rG : G.Walk xa xb := rp.1.map fQ
      have hrG_path : rG.IsPath := rp.2.map (fun _ _ h => Subtype.ext h)
      have hrG_Q : ∀ z ∈ rG.support, z ∈ Q := by
        intro z hz; have hz' : z ∈ (rp.1.map fQ).support := hz
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
        rcases hz' with ⟨z', _, rfl⟩; exact z'.2
      have ha_nQ : a ∉ Q := Finset.disjoint_right.mp hQd1 (List.mem_toFinset.mpr haD)
      have hb_nQ : b ∉ Q := Finset.disjoint_right.mp hQd1 (List.mem_toFinset.mpr hbD)
      have h1' : (SimpleGraph.Walk.cons hxa_adj.symm rG).IsPath :=
        SimpleGraph.Walk.IsPath.cons hrG_path (fun hm => ha_nQ (hrG_Q a hm))
      let P : G.Walk a b := (SimpleGraph.Walk.cons hxa_adj.symm rG).append (SimpleGraph.Walk.cons hxb_adj .nil)
      have hP : P.IsPath := by
        apply isPath_append_of_disjoint_pc _ _ h1' (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj hxb_adj]))
        intro z hz1 hz2
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz2
        rcases hz2 with rfl | rfl
        · rfl
        · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz1
          rcases hz1 with h | h
          · exact False.elim (hba h)
          · exact False.elim (hb_nQ (hrG_Q b h))
      have hP_int : ∀ z ∈ P.support, z ≠ a → z ≠ b → z ∈ Q := by
        intro z hz hza hzb
        dsimp only [P] at hz
        rw [SimpleGraph.Walk.mem_support_append_iff] at hz
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with (rfl | h) | (rfl | rfl)
        · exact absurd rfl hza
        · exact hrG_Q z h
        · exact hxbQ
        · exact absurd rfl hzb
      have hP_ge2 : 2 ≤ P.length := by simp [P, SimpleGraph.Walk.length_append]
      obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, _, _, _, _⟩ := cycle_arcs_edges_subset d₁ hd₁ haD hbD hba.symm
      -- Pick arc A of d₁ with same parity as P so P ++ A.reverse is an even cycle disjoint from d₂!
      have hex_arc : ∃ A : G.Walk a b, A.IsPath ∧ (∀ z ∈ A.support, z ∈ d₁.support) ∧ Even (P.length + A.length) := by
        by_cases hev1 : Even (P.length + A₁.length)
        · exact ⟨A₁, hA₁, fun z hz => (hAsupp z).mp (Or.inl hz), hev1⟩
        · refine ⟨A₂, hA₂, fun z hz => (hAsupp z).mp (Or.inr hz), ?_⟩
          rw [Nat.not_even_iff_odd] at hev1
          rcases hev1 with ⟨k, hk⟩; rcases ho₁ with ⟨m, hm⟩
          exact ⟨P.length + m - k, by omega⟩
      rcases hex_arc with ⟨A, hA, hAD, hPA_ev⟩
      have hA_pos : 1 ≤ A.length := by cases A with | nil => exact absurd rfl hba.symm | cons _ _ => simp
      let ce : G.Walk a a := P.append A.reverse
      have hce : ce.IsCycle := by
        apply isCycle_append_reverse_of_disjoint A P hA hP _ (by omega)
        intro z hzP hza hzb hzA
        exact Finset.disjoint_left.mp hQd1 (hP_int z hzP hza hzb) (List.mem_toFinset.mpr (hAD z hzA))
      have hce_ev : Even ce.length := by simpa [ce, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using hPA_ev
      have hce_disj : Disjoint ce.support.toFinset d₂.support.toFinset := by
        rw [Finset.disjoint_left]
        intro z hz hz2
        have hz' := List.mem_toFinset.mp hz
        dsimp only [ce] at hz'
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
        rcases hz' with hzP | hzA
        · by_cases hza : z = a
          · subst hza; exact Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr haD) hz2
          · by_cases hzb : z = b
            · subst hzb; exact Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr hbD) hz2
            · exact Finset.disjoint_left.mp hQd2 (hP_int z hzP hza hzb) hz2
        · exact Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr (hAD z hzA)) hz2
      exact cycle_pair_obstructions_disjoint_even_odd S hconn h3 hnoc ce d₂ hce hd₂ hce_ev ho₂ hce_disj
    have hNQ_sub : NQ ⊆ (C1.filter fun u => ∃ x ∈ Q, G.Adj x u) ∪ (C2.filter fun u => ∃ x ∈ Q, G.Adj x u) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rcases Finset.mem_union.mp hu.1 with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h1, hu.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h2, hu.2⟩)
    have hcard_le := (Finset.card_le_card hNQ_sub).trans (Finset.card_union_le _ _)
    by_cases h1 : 2 ≤ (C1.filter fun u => ∃ x ∈ Q, G.Adj x u).card
    · exact htwo_on_one c₁ c₂ hc₁ hc₂ hodd₁ hodd₂ hdisj
        (hQ_disj.mono_right Finset.subset_union_left) (hQ_disj.mono_right Finset.subset_union_right) h1
    · exact htwo_on_one c₂ c₁ hc₂ hc₁ hodd₂ hodd₁ hdisj.symm
        (hQ_disj.mono_right Finset.subset_union_right) (hQ_disj.mono_right Finset.subset_union_left) (by omega)
  -- Step 3: Perfect matching between C₁ and C₂
  have hcross_le1 : ∀ {u₁ u₂ : V} (d₁ : G.Walk u₁ u₁) (d₂ : G.Walk u₂ u₂),
      d₁.IsCycle → d₂.IsCycle → Odd d₁.length → Odd d₂.length →
      Disjoint d₁.support.toFinset d₂.support.toFinset →
      ∀ x ∈ d₁.support.toFinset, (d₂.support.toFinset.filter fun y => G.Adj x y).card ≤ 1 := by
    intro u₁ u₂ d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj x hx
    by_contra hgt; push Not at hgt
    let Nx := d₂.support.toFinset.filter fun y => G.Adj x y
    obtain ⟨y₁, hy₁N⟩ := Finset.card_pos.mp (by omega : 0 < Nx.card)
    obtain ⟨y₂, hy₂N, hy21⟩ := Finset.exists_mem_ne (by omega : 1 < Nx.card) y₁
    have hy₁D : y₁ ∈ d₂.support := List.mem_toFinset.mp (Finset.mem_filter.mp hy₁N).1
    have hy₂D : y₂ ∈ d₂.support := List.mem_toFinset.mp (Finset.mem_filter.mp hy₂N).1
    have hxy₁ : G.Adj x y₁ := (Finset.mem_filter.mp hy₁N).2
    have hxy₂ : G.Adj x y₂ := (Finset.mem_filter.mp hy₂N).2
    have hx_nD2 : x ∉ d₂.support := fun hm => Finset.disjoint_left.mp hdj hx (List.mem_toFinset.mpr hm)
    obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, _, _, _, _⟩ := cycle_arcs_edges_subset d₂ hd₂ hy₁D hy₂D hy21.symm
    have hex_ev : ∃ A : G.Walk y₁ y₂, A.IsPath ∧ (∀ z ∈ A.support, z ∈ d₂.support) ∧ Even A.length := by
      by_cases h1 : Even A₁.length
      · exact ⟨A₁, hA₁, fun z hz => (hAsupp z).mp (Or.inl hz), h1⟩
      · rw [Nat.not_even_iff_odd] at h1
        rcases ho₂ with ⟨a, ha⟩; rcases h1 with ⟨b, hb⟩
        exact ⟨A₂, hA₂, fun z hz => (hAsupp z).mp (Or.inr hz), ⟨a - b, by omega⟩⟩
    rcases hex_ev with ⟨A, hA, hAD, hA_ev⟩
    have hA_pos : 1 ≤ A.length := by cases A with | nil => exact absurd rfl hy21.symm | cons _ _ => simp
    let r : G.Walk y₁ y₂ := SimpleGraph.Walk.cons hxy₁.symm (SimpleGraph.Walk.cons hxy₂ .nil)
    have hr : r.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp [r, hy21.symm, (G.ne_of_adj hxy₁).symm, G.ne_of_adj hxy₂])
    let ce : G.Walk y₁ y₁ := r.append A.reverse
    have hce : ce.IsCycle := by
      apply isCycle_append_reverse_of_disjoint A r hA hr _ (by simp [r]; omega)
      intro z hzr hz1 hz2 hzA
      simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hzr
      rcases hzr with rfl | rfl | rfl
      · exact absurd rfl hz1
      · exact hx_nD2 (hAD z hzA)
      · exact absurd rfl hz2
    have hce_ev : Even ce.length := by
      rcases hA_ev with ⟨k, hk⟩
      exact ⟨k + 1, by simp [ce, r, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
    have hinter : ce.support.toFinset ∩ d₁.support.toFinset = {x} := by
      ext z; simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hzce, hzd1⟩
        dsimp only [ce] at hzce
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzce
        rcases hzce with hzr | hzA
        · simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hzr
          rcases hzr with rfl | rfl | rfl
          · exact False.elim (Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr hzd1) (List.mem_toFinset.mpr hy₁D))
          · rfl
          · exact False.elim (Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr hzd1) (List.mem_toFinset.mpr hy₂D))
        · exact False.elim (Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr hzd1) (List.mem_toFinset.mpr (hAD z hzA)))
      · rintro rfl
        refine ⟨?_, List.mem_toFinset.mp hx⟩
        dsimp only [ce]; rw [SimpleGraph.Walk.mem_support_append_iff]; left; simp [r]
    exact cycle_pair_obstructions_one_vertex_even_odd S hconn h3 hnoc ce d₁ hce hd₁ hce_ev ho₁ hinter
  have hcross_eq1 : ∀ {u₁ u₂ : V} (d₁ : G.Walk u₁ u₁) (d₂ : G.Walk u₂ u₂),
      d₁.IsCycle → d₂.IsCycle → Odd d₁.length → Odd d₂.length →
      Disjoint d₁.support.toFinset d₂.support.toFinset →
      (∀ z : V, z ∈ d₁.support.toFinset ∨ z ∈ d₂.support.toFinset) →
      (∀ a ∈ d₁.support, ∀ b ∈ d₁.support, G.Adj a b → s(a, b) ∈ d₁.edges) →
      ∀ x ∈ d₁.support.toFinset, (d₂.support.toFinset.filter fun y => G.Adj x y).card = 1 := by
    intro u₁ u₂ d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj hcov hnoch x hx
    have hle1 := hcross_le1 d₁ d₂ hd₁ hd₂ ho₁ ho₂ hdj x hx
    have hdeg := min_deg_three_of_three_conn hcard_ge4 h3 x
    have hind := deg_in_cycle_le_two_of_no_chord d₁ hd₁ (List.mem_toFinset.mp hx)
      (fun y hy hxy => hnoch x (List.mem_toFinset.mp hx) y hy hxy)
    have hsub : G.neighborFinset x ⊆
        (d₁.support.toFinset.filter fun y => G.Adj x y) ∪ (d₂.support.toFinset.filter fun y => G.Adj x y) := by
      intro y hy; rw [SimpleGraph.mem_neighborFinset] at hy
      rcases hcov y with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h1, hy⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h2, hy⟩)
    have hge := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hge
    omega
  have hm1 : ∀ x ∈ C1, ∃! y, y ∈ C2 ∧ G.Adj x y := by
    intro x hx
    have h1 := hcross_eq1 c₁ c₂ hc₁ hc₂ hodd₁ hodd₂ hdisj hV_cov hc1_chordless x hx
    rcases Finset.card_eq_one.mp h1 with ⟨y, hy⟩
    refine ⟨y, ?_, ?_⟩
    · have : y ∈ C2.filter (fun z => G.Adj x z) := by rw [hy]; simp
      exact Finset.mem_filter.mp this
    · intro z hz
      have : z ∈ C2.filter (fun w => G.Adj x w) := Finset.mem_filter.mpr hz
      rw [hy, Finset.mem_singleton] at this; exact this
  have hm2 : ∀ y ∈ C2, ∃! x, x ∈ C1 ∧ G.Adj y x := by
    intro y hy
    have h1 := hcross_eq1 c₂ c₁ hc₂ hc₁ hodd₂ hodd₁ hdisj.symm (fun z => (hV_cov z).symm) hc2_chordless y hy
    rcases Finset.card_eq_one.mp h1 with ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · have : x ∈ C1.filter (fun z => G.Adj y z) := by rw [hx]; simp
      exact Finset.mem_filter.mp this
    · intro z hz
      have : z ∈ C1.filter (fun w => G.Adj y w) := Finset.mem_filter.mpr hz
      rw [hx, Finset.mem_singleton] at this; exact this
  -- Define the matching involution M : V → V swapping C1 and C2
  let M : V → V := fun z =>
    if hz : z ∈ C1 then (hm1 z hz).choose
    else if hz2 : z ∈ C2 then (hm2 z hz2).choose
    else z
  have hM_C1 : ∀ x ∈ C1, M x ∈ C2 ∧ G.Adj x (M x) := by
    intro x hx; simp only [M, dif_pos hx]; exact (hm1 x hx).choose_spec.1
  have hM_C2 : ∀ y ∈ C2, M y ∈ C1 ∧ G.Adj y (M y) := by
    intro y hy
    have hy1 : y ∉ C1 := Finset.disjoint_right.mp hdisj hy
    simp only [M, dif_neg hy1, dif_pos hy]; exact (hm2 y hy).choose_spec.1
  have hM_uniq1 : ∀ x ∈ C1, ∀ y ∈ C2, G.Adj x y → M x = y := by
    intro x hx y hy hxy
    simp only [M, dif_pos hx]
    exact ((hm1 x hx).choose_spec.2 y ⟨hy, hxy⟩).symm
  have hM_uniq2 : ∀ y ∈ C2, ∀ x ∈ C1, G.Adj y x → M y = x := by
    intro y hy x hx hyx
    have hy1 : y ∉ C1 := Finset.disjoint_right.mp hdisj hy
    simp only [M, dif_neg hy1, dif_pos hy]
    exact ((hm2 y hy).choose_spec.2 x ⟨hx, hyx⟩).symm
  have hM_inv : ∀ z : V, M (M z) = z := by
    intro z
    rcases hV_cov z with hz | hz
    · exact hM_uniq2 (M z) (hM_C1 z hz).1 z hz (hM_C1 z hz).2.symm
    · exact hM_uniq1 (M z) (hM_C2 z hz).1 z hz (hM_C2 z hz).2.symm
  have hM_inj : Function.Injective M := fun a b h => by rw [← hM_inv a, ← hM_inv b, h]
  have hL_eq : c₁.length = c₂.length := by
    have h1 : C1.card ≤ C2.card := Finset.card_le_card_of_injOn M (fun x hx => (hM_C1 x hx).1)
      (fun a _ b _ h => hM_inj h)
    have h2 : C2.card ≤ C1.card := Finset.card_le_card_of_injOn M (fun y hy => (hM_C2 y hy).1)
      (fun a _ b _ h => hM_inj h)
    rw [hC1_card, hC2_card] at h1 h2; omega
  -- Helper: complementary path of an edge on a chordless cycle
  have hcomp_path : ∀ {w : V} (d : G.Walk w w) (hd : d.IsCycle)
      (hnoch : ∀ x ∈ d.support, ∀ y ∈ d.support, G.Adj x y → s(x, y) ∈ d.edges)
      {a b : V} (ha : a ∈ d.support) (hb : b ∈ d.support) (hab : G.Adj a b),
      ∃ P : G.Walk a b, P.IsPath ∧ P.length + 1 = d.length ∧
        (∀ z, z ∈ P.support ↔ z ∈ d.support) ∧
        walkModFourWeight S.sign P + modFourWeight S.sign s(a, b) = walkModFourWeight S.sign d := by
    intro w d hd hnoch a b ha hb hab
    have hne : a ≠ b := G.ne_of_adj hab
    obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, hAdisj, _, _, hAw⟩ := cycle_arcs_edges_subset d hd ha hb hne
    have hlen1 : A₁.length = 1 ∨ A₂.length = 1 := by
      by_contra hnot; push Not at hnot
      have h1p : 1 ≤ A₁.length := by cases A₁ with | nil => exact absurd rfl hne | cons _ _ => simp
      have h2p : 1 ≤ A₂.length := by cases A₂ with | nil => exact absurd rfl hne | cons _ _ => simp
      obtain ⟨w₁, haw₁, _, hA1_eq, _, hw1a, hw1b, _, _, _⟩ := path_split_first A₁ hA₁ (by omega)
      obtain ⟨w₂, haw₂, _, hA2_eq, _, hw2a, hw2b, _, _, _⟩ := path_split_first A₂ hA₂ (by omega)
      have hw1_in : w₁ ∈ A₁.support := by rw [hA1_eq]; simp
      have hw2_in : w₂ ∈ A₂.support := by rw [hA2_eq]; simp
      have hw12 : w₁ ≠ w₂ := fun heq => hAdisj w₁ hw1_in hw1a hw1b (heq ▸ hw2_in)
      have hsub3 : ({b, w₁, w₂} : Finset V) ⊆ d.support.toFinset.filter (fun y => G.Adj a y) := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb, hab⟩
        · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((hAsupp w₁).mp (Or.inl hw1_in)), haw₁⟩
        · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((hAsupp w₂).mp (Or.inr hw2_in)), haw₂⟩
      have hcard3 : ({b, w₁, w₂} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hw12]
        simp [hw1b.symm, hw2b.symm]
      have hle2 := deg_in_cycle_le_two_of_no_chord d hd ha (fun y hy h => hnoch a ha y hy h)
      have := Finset.card_le_card hsub3; omega
    rcases hlen1 with h1 | h2
    · refine ⟨A₂, hA₂, by omega, fun z => ⟨fun hz => (hAsupp z).mp (Or.inr hz), fun hz => ?_⟩, ?_⟩
      · rcases (hAsupp z).mpr hz with hz1 | hz2
        · cases A₁ with
          | nil => simp at h1
          | cons _ r => cases r with
            | nil => simp at hz1; rcases hz1 with rfl | rfl; exact SimpleGraph.Walk.start_mem_support A₂; exact SimpleGraph.Walk.end_mem_support A₂
            | cons _ _ => simp at h1
        · exact hz2
      · have hA1w : walkModFourWeight S.sign A₁ = modFourWeight S.sign s(a, b) := by
          cases A₁ with | nil => simp at h1 | cons _ r => cases r with | nil => simp [walkModFourWeight] | cons _ _ => simp at h1
        rw [add_comm, ← hA1w]; exact hAw S.sign
    · refine ⟨A₁, hA₁, by omega, fun z => ⟨fun hz => (hAsupp z).mp (Or.inl hz), fun hz => ?_⟩, ?_⟩
      · rcases (hAsupp z).mpr hz with hz1 | hz2
        · exact hz1
        · cases A₂ with
          | nil => simp at h2
          | cons _ r => cases r with
            | nil => simp at hz2; rcases hz2 with rfl | rfl; exact SimpleGraph.Walk.start_mem_support A₁; exact SimpleGraph.Walk.end_mem_support A₁
            | cons _ _ => simp at h2
      · have hA2w : walkModFourWeight S.sign A₂ = modFourWeight S.sign s(a, b) := by
          cases A₂ with | nil => simp at h2 | cons _ r => cases r with | nil => simp [walkModFourWeight] | cons _ _ => simp at h2
        rw [← hA2w]; exact hAw S.sign
  -- Step 4: No edge u₁u₂ of C₁ has M u₁ adjacent to M u₂ in C₂!
  have hno_quad : ∀ u₁ u₂ : V, s(u₁, u₂) ∈ c₁.edges → ¬ G.Adj (M u₁) (M u₂) := by
    intro u₁ u₂ hu12 hM_adj
    have hu1C : u₁ ∈ c₁.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c₁ hu12
    have hu2C : u₂ ∈ c₁.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges c₁ hu12
    have hu12_adj : G.Adj u₁ u₂ := SimpleGraph.Walk.adj_of_mem_edges c₁ hu12
    have hu12_ne : u₁ ≠ u₂ := G.ne_of_adj hu12_adj
    have hu1C1 : u₁ ∈ C1 := List.mem_toFinset.mpr hu1C
    have hu2C1 : u₂ ∈ C1 := List.mem_toFinset.mpr hu2C
    have hMu1C2 : M u₁ ∈ C2 := (hM_C1 u₁ hu1C1).1
    have hMu2C2 : M u₂ ∈ C2 := (hM_C1 u₂ hu2C1).1
    have hMu1_adj : G.Adj u₁ (M u₁) := (hM_C1 u₁ hu1C1).2
    have hMu2_adj : G.Adj u₂ (M u₂) := (hM_C1 u₂ hu2C1).2
    have hMu12_ne : M u₁ ≠ M u₂ := G.ne_of_adj hM_adj
    -- Weight of any 4-cycle Q = a - b - M b - M a - a is 2 mod 4!
    have hquad_w2 : ∀ a b : V, s(a, b) ∈ c₁.edges → G.Adj (M a) (M b) →
        modFourWeight S.sign s(a, b) + modFourWeight S.sign s(b, M b) +
        modFourWeight S.sign s(M b, M a) + modFourWeight S.sign s(M a, a) = 2 := by
      intro a b hab_e hMab
      have haC : a ∈ c₁.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c₁ hab_e
      have hbC : b ∈ c₁.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges c₁ hab_e
      have hab_adj : G.Adj a b := SimpleGraph.Walk.adj_of_mem_edges c₁ hab_e
      have hab_ne : a ≠ b := G.ne_of_adj hab_adj
      have haC1 : a ∈ C1 := List.mem_toFinset.mpr haC
      have hbC1 : b ∈ C1 := List.mem_toFinset.mpr hbC
      obtain ⟨P, hP, hPlen, hPC, hPw⟩ := hcomp_path c₁ hc₁ hc1_chordless haC hbC hab_adj
      let q : G.Walk a b := SimpleGraph.Walk.cons (hM_C1 a haC1).2
        (SimpleGraph.Walk.cons hMab (SimpleGraph.Walk.cons (hM_C1 b hbC1).2.symm .nil))
      have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by
        have hMa_nC1 : M a ∉ C1 := Finset.disjoint_right.mp hdisj (hM_C1 a haC1).1
        have hMb_nC1 : M b ∉ C1 := Finset.disjoint_right.mp hdisj (hM_C1 b hbC1).1
        have hMa_ne_a : a ≠ M a := fun h => hMa_nC1 (h ▸ haC1)
        have hMb_ne_a : a ≠ M b := fun h => hMb_nC1 (h ▸ haC1)
        have hMa_ne_b : M a ≠ b := fun h => hMa_nC1 (h ▸ hbC1)
        have hMb_ne_b : M b ≠ b := fun h => hMb_nC1 (h ▸ hbC1)
        simp [q, hMa_ne_a, hMb_ne_a, hab_ne, G.ne_of_adj hMab, hMa_ne_b, hMb_ne_b])
      let c1' : G.Walk a a := P.append q.reverse
      have hc1' : c1'.IsCycle := by
        apply isCycle_append_reverse_of_disjoint q P hq hP _ (by simp [q]; omega)
        intro z hzP hza hzb hzq
        simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hzq
        rcases hzq with rfl | rfl | rfl | rfl
        · exact absurd rfl hza
        · exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr ((hPC z).mp hzP)) (hM_C1 a haC1).1
        · exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr ((hPC z).mp hzP)) (hM_C1 b hbC1).1
        · exact absurd rfl hzb
      have hc1'_odd : Odd c1'.length := by
        rcases hodd₁ with ⟨k, hk⟩
        exact ⟨k + 1, by simp [c1', q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      have hw_c1 := odd_cycle_w3 S hnoc c₁ hc₁ hodd₁
      have hw_c1' := odd_cycle_w3 S hnoc c1' hc1' hc1'_odd
      have hP_ev : Even P.length := by rcases hodd₁ with ⟨k, hk⟩; exact ⟨k, by omega⟩
      have h2P : 2 * walkModFourWeight S.sign P = 0 := by
        rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four P.length).1 hP_ev]
      have hsum : (3 : ZMod 4) + 3 =
          2 * walkModFourWeight S.sign P +
          (modFourWeight S.sign s(a, b) + modFourWeight S.sign s(b, M b) +
           modFourWeight S.sign s(M b, M a) + modFourWeight S.sign s(M a, a)) := by
        rw [← hw_c1, ← hw_c1', ← hPw]
        simp only [c1', q, walkModFourWeight_append, walkModFourWeight_reverse, walkModFourWeight,
          SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        rw [Sym2.eq_swap (a := a) (b := M a), Sym2.eq_swap (a := M a) (b := M b), Sym2.eq_swap (a := M b) (b := b)]
        ring
      rw [h2P, zero_add] at hsum
      exact hsum.symm
    -- Dispatch L = 3 vs L ≥ 5
    by_cases hL3 : c₁.length = 3
    · obtain ⟨a, b, hva, hvb, hab, hva_adj, hab_adj, hbv_adj, hc1_s⟩ := cycle_len_eq_three_verts c₁ hc₁ hL3
      have hc2_3 : c₂.length = 3 := by omega
      obtain ⟨y1, y2, hy01, hy02, hy12, h01, h12, h20, hc2_s⟩ := cycle_len_eq_three_verts c₂ hc₂ hc2_3
      have hC2_complete : ∀ x ∈ C2, ∀ y ∈ C2, x ≠ y → G.Adj x y := by
        intro x hx y hy hne
        have hx' := (hc2_s x).mp (List.mem_toFinset.mp hx)
        have hy' := (hc2_s y).mp (List.mem_toFinset.mp hy)
        rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
        first | exact absurd rfl hne | exact h01 | exact h01.symm | exact h12 | exact h12.symm | exact h20 | exact h20.symm
      have hvC1 : v₁ ∈ C1 := List.mem_toFinset.mpr ((hc1_s v₁).mpr (Or.inl rfl))
      have haC1 : a ∈ C1 := List.mem_toFinset.mpr ((hc1_s a).mpr (Or.inr (Or.inl rfl)))
      have hbC1 : b ∈ C1 := List.mem_toFinset.mpr ((hc1_s b).mpr (Or.inr (Or.inr rfl)))
      have hMva : G.Adj (M v₁) (M a) := hC2_complete _ (hM_C1 v₁ hvC1).1 _ (hM_C1 a haC1).1 (fun h => hva (hM_inj h))
      have hMab : G.Adj (M a) (M b) := hC2_complete _ (hM_C1 a haC1).1 _ (hM_C1 b hbC1).1 (fun h => hab (hM_inj h))
      have hMbv : G.Adj (M b) (M v₁) := hC2_complete _ (hM_C1 b hbC1).1 _ (hM_C1 v₁ hvC1).1 (fun h => hvb.symm (hM_inj h))
      have he_va : s(v₁, a) ∈ c₁.edges := hc1_chordless v₁ (List.mem_toFinset.mp hvC1) a (List.mem_toFinset.mp haC1) hva_adj
      have he_ab : s(a, b) ∈ c₁.edges := hc1_chordless a (List.mem_toFinset.mp haC1) b (List.mem_toFinset.mp hbC1) hab_adj
      have he_bv : s(b, v₁) ∈ c₁.edges := hc1_chordless b (List.mem_toFinset.mp hbC1) v₁ (List.mem_toFinset.mp hvC1) hbv_adj
      have hq1 := hquad_w2 v₁ a he_va hMva
      have hq2 := hquad_w2 a b he_ab hMab
      have hq3 := hquad_w2 b v₁ he_bv hMbv
      let t1 : G.Walk v₁ v₁ := .cons hva_adj (.cons hab_adj (.cons hbv_adj .nil))
      let t2 : G.Walk (M v₁) (M v₁) := .cons hMva (.cons hMab (.cons hMbv .nil))
      have ht1 : t1.IsCycle := by
        refine SimpleGraph.Walk.IsCycle.mk' (SimpleGraph.Walk.IsTrail.mk ?_) (by simp [t1]) ?_
        · simp [t1, Sym2.eq_iff, hva, hva.symm, hab, hab.symm, hvb, hvb.symm]
        · simp [t1, hab, hab.symm, hvb, hvb.symm, hva, hva.symm]
      have ht2 : t2.IsCycle := by
        have h1 : M v₁ ≠ M a := fun h => hva (hM_inj h)
        have h2 : M a ≠ M b := fun h => hab (hM_inj h)
        have h3' : M b ≠ M v₁ := fun h => hvb.symm (hM_inj h)
        refine SimpleGraph.Walk.IsCycle.mk' (SimpleGraph.Walk.IsTrail.mk ?_) (by simp [t2]) ?_
        · simp [t2, Sym2.eq_iff, h1, h1.symm, h2, h2.symm, h3', h3'.symm]
        · simp [t2, h2, h2.symm, h3', h3'.symm, h1, h1.symm]
      have hwt1 := odd_cycle_w3 S hnoc t1 ht1 ⟨1, by simp [t1]⟩
      have hwt2 := odd_cycle_w3 S hnoc t2 ht2 ⟨1, by simp [t2]⟩
      simp only [t1, t2, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hwt1 hwt2
      have hsum : (2 : ZMod 4) + 2 + 2 =
          (3 : ZMod 4) + 3 +
          2 * modFourWeight S.sign s(v₁, M v₁) + 2 * modFourWeight S.sign s(a, M a) +
          2 * modFourWeight S.sign s(b, M b) := by
        rw [← hq1, ← hq2, ← hq3, ← hwt1, ← hwt2]
        rw [Sym2.eq_swap (a := M a) (b := M v₁), Sym2.eq_swap (a := M b) (b := M a),
            Sym2.eq_swap (a := M v₁) (b := M b), Sym2.eq_swap (a := M v₁) (b := v₁),
            Sym2.eq_swap (a := M a) (b := a), Sym2.eq_swap (a := M b) (b := b)]
        ring
      rw [two_mul_modFourWeight, two_mul_modFourWeight, two_mul_modFourWeight] at hsum
      exact absurd hsum (by decide)
    · -- L ≥ 5: H' = G - V(Q) is bipartite → CD₁ + CD₂ contradicts NOC mod 4!
      have hL5 : 5 ≤ c₁.length := by rcases hodd₁ with ⟨k, hk⟩; omega
      let Qset : Finset V := {u₁, u₂, M u₁, M u₂}
      let Qcyc : G.Walk u₁ u₁ :=
        .cons hu12_adj (.cons hMu2_adj (.cons hM_adj.symm (.cons hMu1_adj.symm .nil)))
      have hQcyc : Qcyc.IsCycle := by
        have h1 : u₁ ≠ M u₁ := fun h => Finset.disjoint_left.mp hdisj hu1C1 (h ▸ hMu1C2)
        have h2 : u₁ ≠ M u₂ := fun h => Finset.disjoint_left.mp hdisj hu1C1 (h ▸ hMu2C2)
        have h3' : u₂ ≠ M u₁ := fun h => Finset.disjoint_left.mp hdisj hu2C1 (h ▸ hMu1C2)
        have h4 : u₂ ≠ M u₂ := fun h => Finset.disjoint_left.mp hdisj hu2C1 (h ▸ hMu2C2)
        refine SimpleGraph.Walk.IsCycle.mk' (SimpleGraph.Walk.IsTrail.mk ?_) (by simp [Qcyc]) ?_
        · simp [Qcyc, Sym2.eq_iff, hu12_ne, hu12_ne.symm, h1, h1.symm, h2, h2.symm,
            h3', h3'.symm, h4, h4.symm, hMu12_ne, hMu12_ne.symm]
        · simp [Qcyc, hu12_ne, hu12_ne.symm, h1, h1.symm, h2, h2.symm,
            h3', h3'.symm, h4, h4.symm, hMu12_ne, hMu12_ne.symm]
      have hQsupp : Qcyc.support.toFinset = Qset := by
        ext z; simp [Qcyc, Qset, or_comm, or_left_comm, or_assoc]
      have hH'_bip : (G.induce ((Qset : Set V)ᶜ)).IsBipartite := by
        apply isBipartite_of_no_odd_cycle
        intro z d hd
        by_contra hodd_d
        rw [Nat.not_even_iff_odd] at hodd_d
        let fQ : G.induce ((Qset : Set V)ᶜ) →g G := (SimpleGraph.Embedding.induce ((Qset : Set V)ᶜ)).toHom
        let dG : G.Walk z.1 z.1 := d.map fQ
        have hdG : dG.IsCycle := hd.map (fun _ _ h => Subtype.ext h)
        have hdG_odd : Odd dG.length := by simpa [dG] using hodd_d
        have hdj_Q : Disjoint Qcyc.support.toFinset dG.support.toFinset := by
          rw [hQsupp, Finset.disjoint_right]
          intro w hw
          have hw' : w ∈ (d.map fQ).support := List.mem_toFinset.mp hw
          rw [SimpleGraph.Walk.support_map, List.mem_map] at hw'
          rcases hw' with ⟨w', _, rfl⟩
          exact w'.2
        exact cycle_pair_obstructions_disjoint_even_odd S hconn h3 hnoc Qcyc dG hQcyc hdG ⟨2, by simp [Qcyc]⟩ hdG_odd hdj_Q
      obtain ⟨fcol⟩ := hH'_bip
      let col : V → Bool := fun z => if hz : z ∈ ((Qset : Set V)ᶜ) then (fcol ⟨z, hz⟩ : Bool) else false
      have hcol_adj : ∀ x y : V, x ∉ Qset → y ∉ Qset → G.Adj x y → col x ≠ col y := by
        intro x y hx hy hxy
        have h1 : (G.induce ((Qset : Set V)ᶜ)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        have hne := fcol.valid h1
        simpa [col, hx, hy] using hne
      obtain ⟨P₁, hP₁, hP1_len, hP1_supp, hP1_w⟩ := hcomp_path c₁ hc₁ hc1_chordless hu1C hu2C hu12_adj
      obtain ⟨P₂, hP₂, hP2_len, hP2_supp, hP2_w⟩ := hcomp_path c₂ hc₂ hc2_chordless
        (List.mem_toFinset.mp hMu1C2) (List.mem_toFinset.mp hMu2C2) hM_adj
      obtain ⟨x₁, hu1x1, P1_tail, hP1_eq, hP1t_path, hx1u1, hx1u2, hP1t_pos, hP1t_len, hu1_nP1t⟩ :=
        path_split_first P₁ hP₁ (by omega)
      obtain ⟨x₂, hMu1x2, P2_tail, hP2_eq, hP2t_path, hx2Mu1, hx2Mu2, hP2t_pos, hP2t_len, hMu1_nP2t⟩ :=
        path_split_first P₂ hP₂ (by omega)
      obtain ⟨y₁, hu2y1, Q₁_rev, hP1t_rev_eq, hQ1r_path, hy1u2, hy1x1, hQ1r_pos, hQ1r_len, hu2_nQ1r⟩ :=
        path_split_first P1_tail.reverse hP1t_path.reverse (by simp; omega)
      obtain ⟨y₂, hMu2y2, Q₂_rev, hP2t_rev_eq, hQ2r_path, hy2Mu2, hy2x2, hQ2r_pos, hQ2r_len, hMu2_nQ2r⟩ :=
        path_split_first P2_tail.reverse hP2t_path.reverse (by simp; omega)
      let Q₁ : G.Walk x₁ y₁ := Q₁_rev.reverse
      let Q₂ : G.Walk x₂ y₂ := Q₂_rev.reverse
      have hQ1_path : Q₁.IsPath := hQ1r_path.reverse
      have hQ2_path : Q₂.IsPath := hQ2r_path.reverse
      have hQ1_len : Q₁.length = c₁.length - 3 := by simp [Q₁]; omega
      have hQ2_len : Q₂.length = c₂.length - 3 := by simp [Q₂]; omega
      have hQ1_supp : ∀ z, z ∈ Q₁.support ↔ z ∈ C1 ∧ z ≠ u₁ ∧ z ≠ u₂ := by
        intro z; constructor
        · intro hz
          have hz' : z ∈ Q₁_rev.support := by simpa [Q₁, SimpleGraph.Walk.support_reverse] using hz
          have hzP1t : z ∈ P1_tail.support := by
            rw [← List.mem_reverse, ← SimpleGraph.Walk.support_reverse, hP1t_rev_eq]
            exact List.mem_cons_of_mem _ hz'
          have hzP1 : z ∈ P₁.support := by rw [hP1_eq]; exact List.mem_cons_of_mem _ hzP1t
          refine ⟨List.mem_toFinset.mpr ((hP1_supp z).mp hzP1), fun h => hu1_nP1t (h ▸ hzP1t), fun h => hu2_nQ1r (h ▸ hz')⟩
        · rintro ⟨hzC1, hzu1, hzu2⟩
          have hzP1 : z ∈ P₁.support := (hP1_supp z).mpr (List.mem_toFinset.mp hzC1)
          rw [hP1_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at hzP1
          have hzP1t : z ∈ P1_tail.support := hzP1.resolve_left hzu1
          have hzP1tr : z ∈ P1_tail.reverse.support := by simpa [SimpleGraph.Walk.support_reverse] using hzP1t
          rw [hP1t_rev_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at hzP1tr
          simpa [Q₁, SimpleGraph.Walk.support_reverse] using hzP1tr.resolve_left hzu2
      have hQ2_supp : ∀ z, z ∈ Q₂.support ↔ z ∈ C2 ∧ z ≠ M u₁ ∧ z ≠ M u₂ := by
        intro z; constructor
        · intro hz
          have hz' : z ∈ Q₂_rev.support := by simpa [Q₂, SimpleGraph.Walk.support_reverse] using hz
          have hzP2t : z ∈ P2_tail.support := by
            rw [← List.mem_reverse, ← SimpleGraph.Walk.support_reverse, hP2t_rev_eq]
            exact List.mem_cons_of_mem _ hz'
          have hzP2 : z ∈ P₂.support := by rw [hP2_eq]; exact List.mem_cons_of_mem _ hzP2t
          refine ⟨List.mem_toFinset.mpr ((hP2_supp z).mp hzP2), fun h => hMu1_nP2t (h ▸ hzP2t), fun h => hMu2_nQ2r (h ▸ hz')⟩
        · rintro ⟨hzC2, hz1, hz2⟩
          have hzP2 : z ∈ P₂.support := (hP2_supp z).mpr (List.mem_toFinset.mp hzC2)
          rw [hP2_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at hzP2
          have hzP2t : z ∈ P2_tail.support := hzP2.resolve_left hz1
          have hzP2tr : z ∈ P2_tail.reverse.support := by simpa [SimpleGraph.Walk.support_reverse] using hzP2t
          rw [hP2t_rev_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at hzP2tr
          simpa [Q₂, SimpleGraph.Walk.support_reverse] using hzP2tr.resolve_left hz2
      have hQ1_nQset : ∀ z ∈ Q₁.support, z ∉ Qset := by
        intro z hz hm
        have ⟨hzC1, hz1, hz2⟩ := (hQ1_supp z).mp hz
        simp only [Qset, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl
        · exact hz1 rfl
        · exact hz2 rfl
        · exact Finset.disjoint_left.mp hdisj hzC1 hMu1C2
        · exact Finset.disjoint_left.mp hdisj hzC1 hMu2C2
      have hQ2_nQset : ∀ z ∈ Q₂.support, z ∉ Qset := by
        intro z hz hm
        have ⟨hzC2, hz1, hz2⟩ := (hQ2_supp z).mp hz
        simp only [Qset, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl
        · exact Finset.disjoint_right.mp hdisj hzC2 hu1C1
        · exact Finset.disjoint_right.mp hdisj hzC2 hu2C1
        · exact hz1 rfl
        · exact hz2 rfl
      have hQ1_col : ∀ a b, s(a, b) ∈ Q₁.edges → col a ≠ col b := fun a b he =>
        hcol_adj a b (hQ1_nQset a (SimpleGraph.Walk.fst_mem_support_of_mem_edges Q₁ he))
          (hQ1_nQset b (SimpleGraph.Walk.snd_mem_support_of_mem_edges Q₁ he))
          (SimpleGraph.Walk.adj_of_mem_edges Q₁ he)
      have hQ2_col : ∀ a b, s(a, b) ∈ Q₂.edges → col a ≠ col b := fun a b he =>
        hcol_adj a b (hQ2_nQset a (SimpleGraph.Walk.fst_mem_support_of_mem_edges Q₂ he))
          (hQ2_nQset b (SimpleGraph.Walk.snd_mem_support_of_mem_edges Q₂ he))
          (SimpleGraph.Walk.adj_of_mem_edges Q₂ he)
      have hpath_color_counts : ∀ {a b : V} (Q : G.Walk a b), Q.IsPath →
          (∀ x y, s(x, y) ∈ Q.edges → col x ≠ col y) →
          (Even Q.length → (Q.support.toFinset.filter fun z => col z = col a).card = Q.length / 2 + 1 ∧
            (Q.support.toFinset.filter fun z => col z ≠ col a).card = Q.length / 2) ∧
          (Odd Q.length → (Q.support.toFinset.filter fun z => col z = col a).card = Q.length / 2 + 1 ∧
            (Q.support.toFinset.filter fun z => col z ≠ col a).card = Q.length / 2 + 1) := by
        intro a b Q hQ hQc
        induction Q with
        | nil =>
          constructor
          · intro _; simp
          · intro ho; rcases ho with ⟨k, hk⟩; simp at hk
        | @cons u v w huv r ih =>
          have hnd := hQ.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
          have hunr : u ∉ r.support.toFinset := by simpa using hnd.1
          have hne : col u ≠ col v := hQc u v (by simp)
          have ihr := ih (SimpleGraph.Walk.IsPath.of_cons hQ) (fun x y hxy => hQc x y (by simp [hxy]))
          have hfilt_eq : (SimpleGraph.Walk.cons huv r).support.toFinset.filter (fun z => col z = col u) =
              insert u (r.support.toFinset.filter (fun z => col z ≠ col v)) := by
            ext z; simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons, Finset.mem_filter,
              Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hz, hcz⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hz, by rw [hcz]; exact hne⟩
            · rintro (rfl | ⟨hz, hcz⟩)
              · exact ⟨Or.inl rfl, rfl⟩
              · refine ⟨Or.inr hz, ?_⟩
                cases hu' : col u <;> cases hv' : col v <;> cases hz' : col z <;> simp_all
          have hfilt_ne : (SimpleGraph.Walk.cons huv r).support.toFinset.filter (fun z => col z ≠ col u) =
              r.support.toFinset.filter (fun z => col z = col v) := by
            ext z; simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons, Finset.mem_filter,
              Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hz, hcz⟩
              · exact absurd rfl hcz
              · refine ⟨hz, ?_⟩
                cases hu' : col u <;> cases hv' : col v <;> cases hz' : col z <;> simp_all
            · rintro ⟨hz, hcz⟩
              exact ⟨Or.inr hz, by rw [hcz]; exact hne.symm⟩
          have hunf : u ∉ r.support.toFinset.filter (fun z => col z ≠ col v) := fun h => hunr (Finset.mem_filter.mp h).1
          rw [hfilt_eq, hfilt_ne, Finset.card_insert_of_notMem hunf]
          constructor
          · intro hev
            have hodd_r : Odd r.length := by rcases hev with ⟨k, hk⟩; simp at hk; exact ⟨k - 1, by omega⟩
            have := ihr.2 hodd_r; simp; omega
          · intro hodd_c
            have hev_r : Even r.length := by rcases hodd_c with ⟨k, hk⟩; simp at hk; exact ⟨k, by omega⟩
            have := ihr.1 hev_r; simp; omega
      have hQ1_ev : Even Q₁.length := by rcases hodd₁ with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      have hQ2_ev : Even Q₂.length := by rcases hodd₁ with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      have hcnt1 := (hpath_color_counts Q₁ hQ1_path hQ1_col).1 hQ1_ev
      have hcnt2 := (hpath_color_counts Q₂ hQ2_path hQ2_col).1 hQ2_ev
      have hcol_x12 : col x₁ ≠ col x₂ := by
        intro heq
        let A1 := Q₁.support.toFinset.filter fun z => col z = col x₁
        let B2 := Q₂.support.toFinset.filter fun z => col z ≠ col x₂
        have hmap : ∀ z ∈ A1, M z ∈ B2 := by
          intro z hz
          rw [Finset.mem_filter] at hz
          have hzQ1 : z ∈ Q₁.support := List.mem_toFinset.mp hz.1
          have ⟨hzC1, hzu1, hzu2⟩ := (hQ1_supp z).mp hzQ1
          have hMzQ2 : M z ∈ Q₂.support := (hQ2_supp (M z)).mpr
            ⟨(hM_C1 z hzC1).1, fun h => hzu1 (hM_inj h), fun h => hzu2 (hM_inj h)⟩
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hMzQ2, ?_⟩
          have hdiff := hcol_adj z (M z) (hQ1_nQset z hzQ1) (hQ2_nQset (M z) hMzQ2) (hM_C1 z hzC1).2
          rw [hz.2, heq] at hdiff; exact hdiff.symm
        have hle := Finset.card_le_card_of_injOn M hmap (fun a _ b _ h => hM_inj h)
        omega
      have hx1Q1 : x₁ ∈ Q₁.support := SimpleGraph.Walk.start_mem_support Q₁
      have ⟨hx1C1, _, _⟩ := (hQ1_supp x₁).mp hx1Q1
      have hx1'Q2 : M x₁ ∈ Q₂.support := (hQ2_supp (M x₁)).mpr
        ⟨(hM_C1 x₁ hx1C1).1, fun h => hx1u1 (hM_inj h), fun h => hx1u2 (hM_inj h)⟩
      have hcol_Mx1 : col (M x₁) = col x₂ := by
        have hdiff := hcol_adj x₁ (M x₁) (hQ1_nQset x₁ hx1Q1) (hQ2_nQset (M x₁) hx1'Q2) (hM_C1 x₁ hx1C1).2
        cases h1 : col x₁ <;> cases h2 : col x₂ <;> cases h3' : col (M x₁) <;> simp_all
      have hx1'P2 : M x₁ ∈ P₂.support := (hP2_supp (M x₁)).mpr (List.mem_toFinset.mp (hM_C1 x₁ hx1C1).1)
      let P2a : G.Walk (M u₁) (M x₁) := P₂.takeUntil (M x₁) hx1'P2
      let P2b : G.Walk (M x₁) (M u₂) := P₂.dropUntil (M x₁) hx1'P2
      have hP2_spec := SimpleGraph.Walk.take_spec P₂ hx1'P2
      have hP2_sum_len : P2a.length + P2b.length = P₂.length := by rw [← SimpleGraph.Walk.length_append, hP2_spec]
      have hMx1_ne_Mu1 : M x₁ ≠ M u₁ := fun h => hx1u1 (hM_inj h)
      have hMx1_ne_Mu2 : M x₁ ≠ M u₂ := fun h => hx1u2 (hM_inj h)
      have hP2a_odd : Odd P2a.length := by
        have hx1'P2t : M x₁ ∈ P2_tail.support := by
          have := hx1'P2; rw [hP2_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at this
          exact this.resolve_left hMx1_ne_Mu1
        have htake_eq : P2a = SimpleGraph.Walk.cons hMu1x2 (P2_tail.takeUntil (M x₁) hx1'P2t) := by
          dsimp only [P2a]; generalize_proofs hp1
          revert hp1; rw [hP2_eq]; intro hp1
          simp [SimpleGraph.Walk.takeUntil, hMx1_ne_Mu1.symm]
        let R := P2_tail.takeUntil (M x₁) hx1'P2t
        have hR_in_Q2 : ∀ z ∈ R.support, z ∈ Q₂.support := by
          intro z hz
          have hzP2t := SimpleGraph.Walk.support_takeUntil_subset P2_tail hx1'P2t hz
          have hzP2 : z ∈ P₂.support := by rw [hP2_eq]; exact List.mem_cons_of_mem _ hzP2t
          have hzu2 : z ≠ M u₂ := by
            intro h; rw [h] at hz
            have hspec := SimpleGraph.Walk.take_spec P2_tail hx1'P2t
            have hnd := hP2t_path.support_nodup
            rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdc : (P2_tail.dropUntil (M x₁) hx1'P2t).support = M x₁ :: (P2_tail.dropUntil (M x₁) hx1'P2t).support.tail := by
              cases P2_tail.dropUntil (M x₁) hx1'P2t <;> simp
            have hMu2_d : M u₂ ∈ (P2_tail.dropUntil (M x₁) hx1'P2t).support := SimpleGraph.Walk.end_mem_support _
            rw [hdc, List.mem_cons] at hMu2_d
            exact hnd.2.2 (M u₂) hz (M u₂) (hMu2_d.resolve_left hMx1_ne_Mu2) rfl
          exact (hQ2_supp z).mpr ⟨List.mem_toFinset.mpr ((hP2_supp z).mp hzP2), fun h => hMu1_nP2t (h ▸ hzP2t), hzu2⟩
        have hR_col : ∀ a b, s(a, b) ∈ R.edges → col a ≠ col b := fun a b hab =>
          hcol_adj a b (hQ2_nQset a (hR_in_Q2 a (SimpleGraph.Walk.fst_mem_support_of_mem_edges R hab)))
            (hQ2_nQset b (hR_in_Q2 b (SimpleGraph.Walk.snd_mem_support_of_mem_edges R hab)))
            (SimpleGraph.Walk.adj_of_mem_edges R hab)
        have hR_ev : Even R.length := (path_bipartite_parity R col hR_col).mp hcol_Mx1
        rcases hR_ev with ⟨k, hk⟩
        exact ⟨k, by rw [htake_eq]; simp; omega⟩
      have hP2b_odd : Odd P2b.length := by
        rcases hodd₁ with ⟨a, ha⟩; rcases hP2a_odd with ⟨b, hb⟩; exact ⟨a - b - 1, by omega⟩
      -- Build the two odd cycles CD₁ and CD₂:
      -- CD₁ = (u₁ - u₂) ++ P1_tail.reverse ++ (x₁ - M x₁) ++ P2a.reverse ++ (M u₁ - u₁)
      have hP1t_C1 : ∀ z ∈ P1_tail.support, z ∈ C1 := fun z hz =>
        List.mem_toFinset.mpr ((hP1_supp z).mp (by rw [hP1_eq]; exact List.mem_cons_of_mem _ hz))
      have hP2a_C2 : ∀ z ∈ P2a.support, z ∈ C2 := fun z hz =>
        List.mem_toFinset.mpr ((hP2_supp z).mp (SimpleGraph.Walk.support_takeUntil_subset P₂ hx1'P2 hz))
      have hP2b_C2 : ∀ z ∈ P2b.support, z ∈ C2 := fun z hz =>
        List.mem_toFinset.mpr ((hP2_supp z).mp (SimpleGraph.Walk.support_dropUntil_subset P₂ hx1'P2 hz))
      let A_cd1 : G.Walk u₁ x₁ := SimpleGraph.Walk.cons hu12_adj P1_tail.reverse
      have hA_cd1 : A_cd1.IsPath := SimpleGraph.Walk.IsPath.cons hP1t_path.reverse
        (fun hm => hu1_nP1t (by simpa [SimpleGraph.Walk.support_reverse] using hm))
      let B_cd1 : G.Walk u₁ x₁ := SimpleGraph.Walk.cons hMu1_adj (P2a.append (SimpleGraph.Walk.cons (hM_C1 x₁ hx1C1).2.symm .nil))
      have hB_cd1_sub : (P2a.append (SimpleGraph.Walk.cons (hM_C1 x₁ hx1C1).2.symm .nil)).IsPath := by
        apply isPath_append_of_disjoint_pc P2a _ (hP₂.takeUntil hx1'P2)
          (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj (hM_C1 x₁ hx1C1).2.symm]))
        intro z hz1 hz2
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz2
        rcases hz2 with rfl | rfl
        · rfl
        · exact False.elim (Finset.disjoint_left.mp hdisj hx1C1 (hP2a_C2 x₁ hz1))
      have hB_cd1 : B_cd1.IsPath := SimpleGraph.Walk.IsPath.cons hB_cd1_sub (fun hm => by
        rw [SimpleGraph.Walk.mem_support_append_iff] at hm
        rcases hm with h1 | h2
        · exact Finset.disjoint_left.mp hdisj hu1C1 (hP2a_C2 u₁ h1)
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at h2
          rcases h2 with h | h
          · exact Finset.disjoint_left.mp hdisj hu1C1 (h ▸ (hM_C1 x₁ hx1C1).1)
          · exact hx1u1 h.symm)
      let CD₁ : G.Walk u₁ u₁ := A_cd1.append B_cd1.reverse
      have hCD1 : CD₁.IsCycle := by
        apply isCycle_append_reverse_of_disjoint B_cd1 A_cd1 hB_cd1 hA_cd1 _ (by simp [A_cd1, B_cd1, SimpleGraph.Walk.length_append]; omega)
        intro z hzA hzu1 hzx1 hzB
        dsimp only [A_cd1] at hzA
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hzA
        have hzC1 : z ∈ C1 := hP1t_C1 z (by simpa [SimpleGraph.Walk.support_reverse] using hzA.resolve_left hzu1)
        dsimp only [B_cd1] at hzB
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hzB
        have hzB' := hzB.resolve_left hzu1
        rw [SimpleGraph.Walk.mem_support_append_iff] at hzB'
        rcases hzB' with h1 | h2
        · exact Finset.disjoint_left.mp hdisj hzC1 (hP2a_C2 z h1)
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at h2
          rcases h2 with rfl | rfl
          · exact Finset.disjoint_left.mp hdisj hzC1 (hM_C1 x₁ hx1C1).1
          · exact absurd rfl hzx1
      have hCD1_odd : Odd CD₁.length := by
        rcases hodd₁ with ⟨a, ha⟩; rcases hP2a_odd with ⟨b, hb⟩
        exact ⟨a + b + 1, by simp [CD₁, A_cd1, B_cd1, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      -- CD₂ = (u₂ - u₁ - x₁) ++ (x₁ - M x₁) ++ P2b ++ (M u₂ - u₂)
      let A_cd2 : G.Walk u₂ x₁ := SimpleGraph.Walk.cons hu12_adj.symm (SimpleGraph.Walk.cons hu1x1 .nil)
      have hA_cd2 : A_cd2.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [A_cd2, hu12_ne.symm, hx1u2.symm, hx1u1.symm])
      let B_cd2 : G.Walk u₂ x₁ := SimpleGraph.Walk.cons hMu2_adj (P2b.reverse.append (SimpleGraph.Walk.cons (hM_C1 x₁ hx1C1).2.symm .nil))
      have hB_cd2_sub : (P2b.reverse.append (SimpleGraph.Walk.cons (hM_C1 x₁ hx1C1).2.symm .nil)).IsPath := by
        apply isPath_append_of_disjoint_pc P2b.reverse _ (hP₂.dropUntil hx1'P2).reverse
          (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj (hM_C1 x₁ hx1C1).2.symm]))
        intro z hz1 hz2
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz2
        rcases hz2 with rfl | rfl
        · rfl
        · exact False.elim (Finset.disjoint_left.mp hdisj hx1C1 (hP2b_C2 x₁ (by simpa [SimpleGraph.Walk.support_reverse] using hz1)))
      have hB_cd2 : B_cd2.IsPath := SimpleGraph.Walk.IsPath.cons hB_cd2_sub (fun hm => by
        rw [SimpleGraph.Walk.mem_support_append_iff] at hm
        rcases hm with h1 | h2
        · exact Finset.disjoint_left.mp hdisj hu2C1 (hP2b_C2 u₂ (by simpa [SimpleGraph.Walk.support_reverse] using h1))
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at h2
          rcases h2 with h | h
          · exact Finset.disjoint_left.mp hdisj hu2C1 (h ▸ (hM_C1 x₁ hx1C1).1)
          · exact hx1u2 h.symm)
      let CD₂ : G.Walk u₂ u₂ := A_cd2.append B_cd2.reverse
      have hCD2 : CD₂.IsCycle := by
        apply isCycle_append_reverse_of_disjoint B_cd2 A_cd2 hB_cd2 hA_cd2 _ (by simp [A_cd2, B_cd2, SimpleGraph.Walk.length_append]; omega)
        intro z hzA hzu2 hzx1 hzB
        simp only [A_cd2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hzA
        rcases hzA with rfl | rfl | rfl
        · exact absurd rfl hzu2
        · dsimp only [B_cd2] at hzB
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hzB
          have hzB' := hzB.resolve_left hu12_ne
          rw [SimpleGraph.Walk.mem_support_append_iff] at hzB'
          rcases hzB' with h1 | h2
          · exact Finset.disjoint_left.mp hdisj hu1C1 (hP2b_C2 u₁ (by simpa [SimpleGraph.Walk.support_reverse] using h1))
          · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at h2
            rcases h2 with h | h
            · exact Finset.disjoint_left.mp hdisj hu1C1 (h ▸ (hM_C1 x₁ hx1C1).1)
            · exact hx1u1 h.symm
        · exact absurd rfl hzx1
      have hCD2_odd : Odd CD₂.length := by
        rcases hP2b_odd with ⟨b, hb⟩
        exact ⟨b + 2, by simp [CD₂, A_cd2, B_cd2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      have hwCD1 := odd_cycle_w3 S hnoc CD₁ hCD1 hCD1_odd
      have hwCD2 := odd_cycle_w3 S hnoc CD₂ hCD2 hCD2_odd
      have hwC1 := odd_cycle_w3 S hnoc c₁ hc₁ hodd₁
      have hwC2 := odd_cycle_w3 S hnoc c₂ hc₂ hodd₂
      have hwQ := hquad_w2 u₁ u₂ hu12 hM_adj
      have hP1_split_w : walkModFourWeight S.sign P₁ = modFourWeight S.sign s(u₁, x₁) + walkModFourWeight S.sign P1_tail := by
        rw [hP1_eq]; simp [walkModFourWeight]
      have hP2_split_w : walkModFourWeight S.sign P₂ = walkModFourWeight S.sign P2a + walkModFourWeight S.sign P2b := by
        rw [← walkModFourWeight_append, hP2_spec]
      have hCD1_w : walkModFourWeight S.sign CD₁ =
          modFourWeight S.sign s(u₁, u₂) + walkModFourWeight S.sign P1_tail +
          modFourWeight S.sign s(u₁, M u₁) + walkModFourWeight S.sign P2a + modFourWeight S.sign s(M x₁, x₁) := by
        simp only [CD₁, A_cd1, B_cd1, walkModFourWeight_append, walkModFourWeight_reverse]
        simp [walkModFourWeight]; ring
      have hCD2_w : walkModFourWeight S.sign CD₂ =
          modFourWeight S.sign s(u₁, u₂) + modFourWeight S.sign s(u₁, x₁) +
          modFourWeight S.sign s(u₂, M u₂) + walkModFourWeight S.sign P2b + modFourWeight S.sign s(M x₁, x₁) := by
        simp only [CD₂, A_cd2, B_cd2, walkModFourWeight_append, walkModFourWeight_reverse]
        simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [Sym2.eq_swap (a := u₂) (b := u₁)]; ring
      have hsum : (3 : ZMod 4) + 3 + 2 * modFourWeight S.sign s(u₁, u₂) + 2 * modFourWeight S.sign s(M u₁, M u₂) =
          (3 : ZMod 4) + 3 + 2 + 2 * modFourWeight S.sign s(u₁, u₂) + 2 * modFourWeight S.sign s(M x₁, x₁) := by
        rw [← hwCD1, ← hwCD2, ← hwC1, ← hwC2, ← hwQ, ← hP1_w, ← hP2_w, hP1_split_w, hP2_split_w, hCD1_w, hCD2_w]
        rw [Sym2.eq_swap (a := M u₂) (b := M u₁), Sym2.eq_swap (a := M u₁) (b := u₁)]
        ring
      rw [two_mul_modFourWeight, two_mul_modFourWeight, two_mul_modFourWeight] at hsum
      exact absurd hsum (by decide)
  -- Step 5: L ≥ 5 (since L = 3 would have every pair adjacent in C₂!)
  have hL_ge5 : 5 ≤ c₁.length := by
    by_contra hlt
    have hL3 : c₁.length = 3 := by rcases hodd₁ with ⟨k, hk⟩; omega
    obtain ⟨a, b, hva, hvb, hab, hva_adj, _, _, hc1_s⟩ := cycle_len_eq_three_verts c₁ hc₁ hL3
    have hc2_3 : c₂.length = 3 := by omega
    obtain ⟨y1, y2, _, _, _, h01, h12, h20, hc2_s⟩ := cycle_len_eq_three_verts c₂ hc₂ hc2_3
    have hC2_comp : ∀ x ∈ C2, ∀ y ∈ C2, x ≠ y → G.Adj x y := by
      intro x hx y hy hne
      rcases (hc2_s x).mp (List.mem_toFinset.mp hx) with rfl | rfl | rfl <;>
      rcases (hc2_s y).mp (List.mem_toFinset.mp hy) with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | exact h01 | exact h01.symm | exact h12 | exact h12.symm | exact h20 | exact h20.symm
    have hvC1 : v₁ ∈ C1 := List.mem_toFinset.mpr ((hc1_s v₁).mpr (Or.inl rfl))
    have haC1 : a ∈ C1 := List.mem_toFinset.mpr ((hc1_s a).mpr (Or.inr (Or.inl rfl)))
    exact hno_quad v₁ a (hc1_chordless v₁ (List.mem_toFinset.mp hvC1) a (List.mem_toFinset.mp haC1) hva_adj)
      (hC2_comp _ (hM_C1 v₁ hvC1).1 _ (hM_C1 a haC1).1 (fun h => hva (hM_inj h)))
  -- Dispatch L = 5 vs L ≥ 7!
  by_cases hL5 : c₁.length = 5
  · -- L = 5: G ≅ Petersen, apply petersen_switching_iso!
    obtain ⟨a1, a2, a3, a4, hnd1, h01, h12, h23, h34, h40, hc1_s, hc1_e⟩ := cycle_len_eq_five_vertices c₁ hc₁ hL5
    let v : Fin 5 → V
      | 0 => v₁
      | 1 => a1
      | 2 => a2
      | 3 => a3
      | 4 => a4
    have hv_C1 : ∀ i : Fin 5, v i ∈ C1 := by
      intro i; fin_cases i <;> exact List.mem_toFinset.mpr ((hc1_s _).mpr (by tauto))
    have hv_inj : Function.Injective v := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd1
      intro i j hij; fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> tauto
    have hv_cov1 : ∀ x ∈ C1, ∃ i : Fin 5, x = v i := by
      intro x hx; rcases (hc1_s x).mp (List.mem_toFinset.mp hx) with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
    let f : Fin 10 → V := fun i =>
      if h : i.val < 5 then v ⟨i.val, h⟩ else M (v ⟨i.val - 5, by omega⟩)
    have hf_bij : Function.Bijective f := by
      constructor
      · intro i j hij
        by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
        · simp only [f, dif_pos hi, dif_pos hj] at hij
          have := hv_inj hij; ext; simpa using congrArg Fin.val this
        · simp only [f, dif_pos hi, dif_neg hj] at hij
          exact False.elim (Finset.disjoint_left.mp hdisj (hv_C1 _) (hij ▸ (hM_C1 _ (hv_C1 _)).1))
        · simp only [f, dif_neg hi, dif_pos hj] at hij
          exact False.elim (Finset.disjoint_left.mp hdisj (hv_C1 _) (hij.symm ▸ (hM_C1 _ (hv_C1 _)).1))
        · simp only [f, dif_neg hi, dif_neg hj] at hij
          have := hv_inj (hM_inj hij); ext; have := congrArg Fin.val this; dsimp at this; omega
      · intro x
        rcases hV_cov x with hx1 | hx2
        · rcases hv_cov1 x hx1 with ⟨i, rfl⟩
          exact ⟨⟨i.val, by omega⟩, by simp [f, i.isLt]⟩
        · rcases hv_cov1 (M x) (hM_C2 x hx2).1 with ⟨i, hi⟩
          refine ⟨⟨i.val + 5, by omega⟩, ?_⟩
          have h1 : ¬ i.val + 5 < 5 := by omega
          simp only [f, dif_neg h1]
          have : (⟨i.val + 5 - 5, by omega⟩ : Fin 5) = i := by ext; simp
          rw [this, ← hi, hM_inv]
    -- Outer edges on C1
    have hv_adj_iff : ∀ i j : Fin 5, G.Adj (v i) (v j) ↔ j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5 := by
      intro i j
      constructor
      · intro hadj
        have he := hc1_chordless (v i) (List.mem_toFinset.mp (hv_C1 i)) (v j) (List.mem_toFinset.mp (hv_C1 j)) hadj
        rw [hc1_e] at he
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd1
        fin_cases i <;> fin_cases j <;> simp [v, Sym2.eq_iff] at he ⊢ <;> tauto
      · intro h
        fin_cases i <;> fin_cases j <;> simp [v] at h ⊢
        all_goals first | exact h01 | exact h01.symm | exact h12 | exact h12.symm |
          exact h23 | exact h23.symm | exact h34 | exact h34.symm | exact h40 | exact h40.symm
    -- Inner edges on C2: M (v i) has degree 2 in C2, and is NOT adjacent to M (v (i±1)) by hno_quad!
    have hM_not_adj_1 : ∀ i j : Fin 5, (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5) → ¬ G.Adj (M (v i)) (M (v j)) := by
      intro i j h
      have hadj : G.Adj (v i) (v j) := (hv_adj_iff i j).mpr h
      exact hno_quad (v i) (v j) (hc1_chordless (v i) (List.mem_toFinset.mp (hv_C1 i)) (v j) (List.mem_toFinset.mp (hv_C1 j)) hadj)
    have hM_adj_iff : ∀ i j : Fin 5, G.Adj (M (v i)) (M (v j)) ↔ j.val = (i.val + 2) % 5 ∨ i.val = (j.val + 2) % 5 := by
      intro i j
      -- Every w ∈ C2 has degree = 2 in C2 (since deg_G w ≥ 3, deg_C1 w = 1, and deg_C2 w ≤ 2 by chordlessness!)
      have hdeg2_C2 : ∀ k : Fin 5, (C2.filter fun z => G.Adj (M (v k)) z).card = 2 := by
        intro k
        have hwkC2 : M (v k) ∈ C2 := (hM_C1 (v k) (hv_C1 k)).1
        have hle2 := deg_in_cycle_le_two_of_no_chord c₂ hc₂ (List.mem_toFinset.mp hwkC2)
          (fun y hy h => hc2_chordless _ (List.mem_toFinset.mp hwkC2) y hy h)
        have hdeg := min_deg_three_of_three_conn hcard_ge4 h3 (M (v k))
        have hcross := hcross_eq1 c₂ c₁ hc₂ hc₁ hodd₂ hodd₁ hdisj.symm (fun z => (hV_cov z).symm) hc2_chordless (M (v k)) hwkC2
        have hsub : G.neighborFinset (M (v k)) ⊆ (C2.filter fun z => G.Adj (M (v k)) z) ∪ (C1.filter fun z => G.Adj (M (v k)) z) := by
          intro z hz; rw [SimpleGraph.mem_neighborFinset] at hz
          rcases hV_cov z with h1 | h2
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h1, hz⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h2, hz⟩)
        have hge := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hge
        omega
      let k2 : Fin 5 := ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
      let k3 : Fin 5 := ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩
      have hk23_ne : M (v k2) ≠ M (v k3) := fun h => by
        have := congrArg Fin.val (hv_inj (hM_inj h)); dsimp [k2, k3] at this; omega
      have hsub2 : C2.filter (fun z => G.Adj (M (v i)) z) ⊆ {M (v k2), M (v k3)} := by
        intro z hz
        rw [Finset.mem_filter] at hz
        rcases hv_cov1 (M z) (hM_C2 z hz.1).1 with ⟨m, hm⟩
        have hzm : z = M (v m) := by rw [← hm, hM_inv]
        rw [hzm] at hz ⊢
        have hmi : m ≠ i := fun h => G.loopless (M (v i)) (h ▸ hz.2)
        have hnot1 : ¬ (m.val = (i.val + 1) % 5 ∨ i.val = (m.val + 1) % 5) :=
          fun h => hM_not_adj_1 i m h hz.2
        have hcase : m = k2 ∨ m = k3 := by
          fin_cases i <;> fin_cases m <;> simp [k2, k3] at hmi hnot1 ⊢ <;> omega
        rcases hcase with rfl | rfl <;> simp
      have heq2 : C2.filter (fun z => G.Adj (M (v i)) z) = {M (v k2), M (v k3)} :=
        Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hk23_ne, hdeg2_C2 i])
      have hadj_iff : G.Adj (M (v i)) (M (v j)) ↔ M (v j) ∈ ({M (v k2), M (v k3)} : Finset V) := by
        rw [← heq2, Finset.mem_filter]; exact ⟨fun h => ⟨(hM_C1 _ (hv_C1 j)).1, h⟩, fun h => h.2⟩
      rw [hadj_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have := congrArg Fin.val (hv_inj (hM_inj h)); dsimp [k2] at this; left; exact this
        · have := congrArg Fin.val (hv_inj (hM_inj h)); dsimp [k3] at this; right; omega
      · intro h
        have : j = k2 ∨ j = k3 := by fin_cases i <;> fin_cases j <;> simp [k2, k3] at h ⊢ <;> omega
        rcases this with rfl | rfl <;> simp
    apply petersen_switching_iso S hnoc f hf_bij
    intro i j
    simp only [petersenGraph, SimpleGraph.fromRel_adj]
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · simp only [f, dif_pos hi, dif_pos hj]
      rw [hv_adj_iff]
      constructor
      · rintro ⟨h, _⟩
        rcases h with (⟨_, _, h1⟩ | ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩) | (⟨_, _, h1⟩ | ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩)
        · exact h1
        · omega
        · omega
        · omega
        · exact h1.symm
        · omega
        · omega
        · omega
      · intro h
        refine ⟨Or.inl (Or.inl ⟨hi, hj, h⟩), ?_⟩
        intro heq; subst heq; omega
    · simp only [f, dif_pos hi, dif_neg hj]
      have hcross_iff : G.Adj (v ⟨i.val, hi⟩) (M (v ⟨j.val - 5, by omega⟩)) ↔ j.val = i.val + 5 := by
        constructor
        · intro hadj
          have heq := hM_uniq1 (v ⟨i.val, hi⟩) (hv_C1 _) (M (v ⟨j.val - 5, by omega⟩)) (hM_C1 _ (hv_C1 _)).1 hadj
          have := congrArg Fin.val (hv_inj (hM_inj heq)); dsimp at this; omega
        · intro heq
          have : (⟨j.val - 5, by omega⟩ : Fin 5) = ⟨i.val, hi⟩ := by ext; dsimp; omega
          rw [this]; exact (hM_C1 _ (hv_C1 _)).2
      rw [hcross_iff]
      constructor
      · rintro ⟨h, _⟩
        rcases h with (⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1⟩) <;> omega
      · intro h; refine ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨hi, h⟩))), fun heq => by subst heq; omega⟩
    · simp only [f, dif_neg hi, dif_pos hj]
      have hcross_iff : G.Adj (M (v ⟨i.val - 5, by omega⟩)) (v ⟨j.val, hj⟩) ↔ i.val = j.val + 5 := by
        constructor
        · intro hadj
          have heq := hM_uniq1 (v ⟨j.val, hj⟩) (hv_C1 _) (M (v ⟨i.val - 5, by omega⟩)) (hM_C1 _ (hv_C1 _)).1 hadj.symm
          have := congrArg Fin.val (hv_inj (hM_inj heq)); dsimp at this; omega
        · intro heq
          have : (⟨i.val - 5, by omega⟩ : Fin 5) = ⟨j.val, hj⟩ := by ext; dsimp; omega
          rw [this]; exact (hM_C1 _ (hv_C1 _)).2.symm
      rw [hcross_iff]
      constructor
      · rintro ⟨h, _⟩
        rcases h with (⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1⟩) | (⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨h1, _⟩) <;> omega
      · intro h; refine ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨hj, h⟩))), fun heq => by subst heq; omega⟩
    · simp only [f, dif_neg hi, dif_neg hj]
      rw [hM_adj_iff]
      constructor
      · rintro ⟨h, _⟩
        rcases h with (⟨h1, _⟩ | ⟨_, _, h1⟩ | ⟨h1, _⟩ | ⟨_, h1⟩) | (⟨h1, _⟩ | ⟨_, _, h1⟩ | ⟨h1, _⟩ | ⟨_, h1⟩)
        · omega
        · exact h1
        · omega
        · omega
        · omega
        · exact h1.symm
        · omega
        · omega
      · intro h
        refine ⟨Or.inl (Or.inr (Or.inl ⟨by omega, by omega, h⟩)), ?_⟩
        intro heq; subst heq; dsimp at h; omega
  · -- L ≥ 7: minimize distance d_{C₂}(M u₁, M u₂) over edges u₁u₂ ∈ E(C₁) → contradiction!
    exfalso
    have hL7 : 7 ≤ c₁.length := by rcases hodd₁ with ⟨k, hk⟩; omega
    -- Distance along C₂ between M a and M b for an edge s(a, b) ∈ c₁.edges
    let edgeDist : V → V → ℕ → Prop := fun a b d =>
      s(a, b) ∈ c₁.edges ∧
      ∃ (A_ev A_od : G.Walk (M a) (M b)), A_ev.IsPath ∧ A_od.IsPath ∧
        A_ev.length + A_od.length = c₂.length ∧ Even A_ev.length ∧ Odd A_od.length ∧
        (∀ z, z ∈ A_ev.support ∨ z ∈ A_od.support ↔ z ∈ c₂.support) ∧
        (∀ z ∈ A_ev.support, z ≠ M a → z ≠ M b → z ∉ A_od.support) ∧
        min A_ev.length A_od.length = d
    have hex_dist : ∃ d : ℕ, ∃ a b : V, edgeDist a b d := by
      -- Pick any edge of c₁
      cases hc1_eq : c₁ with
      | nil => simp [hc1_eq] at hL7
      | @cons _ w _ hv1w r =>
        have he : s(v₁, w) ∈ c₁.edges := by rw [hc1_eq]; simp
        have hv1C1 : v₁ ∈ C1 := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₁)
        have hwC1 : w ∈ C1 := List.mem_toFinset.mpr (SimpleGraph.Walk.snd_mem_support_of_mem_edges c₁ he)
        have hne : M v₁ ≠ M w := fun h => G.ne_of_adj hv1w (hM_inj h)
        obtain ⟨A₁, A₂, hA₁, hA₂, hAlen, hAsupp, hAdisj, _, _, _⟩ :=
          cycle_arcs_edges_subset c₂ hc₂ (List.mem_toFinset.mp (hM_C1 v₁ hv1C1).1) (List.mem_toFinset.mp (hM_C1 w hwC1).1) hne
        by_cases h1 : Even A₁.length
        · have h2 : Odd A₂.length := by rcases hodd₂ with ⟨a, ha⟩; rcases h1 with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
          exact ⟨min A₁.length A₂.length, v₁, w, he, A₁, A₂, hA₁, hA₂, hAlen, h1, h2, hAsupp, hAdisj, rfl⟩
        · rw [Nat.not_even_iff_odd] at h1
          have h2 : Even A₂.length := by rcases hodd₂ with ⟨a, ha⟩; rcases h1 with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
          exact ⟨min A₂.length A₁.length, v₁, w, he, A₂, A₁, hA₂, hA₁, by omega, h2, h1,
            fun z => by rw [or_comm]; exact hAsupp z, fun z hz h1' h2' hm => hAdisj z hm h1' h2' hz, rfl⟩
    obtain ⟨u₁, u₂, hu12_e, A_ev, A_od, hAev, hAod, hA_sum, hAev_ev, hAod_od, hAsupp, hAdisj, hd_min_eq⟩ := Nat.find_spec hex_dist
    have hd_min : ∀ a b d, edgeDist a b d → min A_ev.length A_od.length ≤ d := by
      intro a b d habd; rw [hd_min_eq]; exact Nat.find_min' hex_dist ⟨a, b, habd⟩
    have hu1C : u₁ ∈ c₁.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c₁ hu12_e
    have hu2C : u₂ ∈ c₁.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges c₁ hu12_e
    have hu12_adj : G.Adj u₁ u₂ := SimpleGraph.Walk.adj_of_mem_edges c₁ hu12_e
    have hu12_ne : u₁ ≠ u₂ := G.ne_of_adj hu12_adj
    have hu1C1 : u₁ ∈ C1 := List.mem_toFinset.mpr hu1C
    have hu2C1 : u₂ ∈ C1 := List.mem_toFinset.mpr hu2C
    have hMu1_nadj : ¬ G.Adj (M u₁) (M u₂) := hno_quad u₁ u₂ hu12_e
    -- A_od.length ≥ 3 (since A_od is odd and ≠ 1 as ¬ G.Adj (M u₁) (M u₂))
    have hAod_ge3 : 3 ≤ A_od.length := by
      have h1 : A_od.length ≠ 1 := by
        intro h; cases A_od with
        | nil => simp at h
        | cons hadj r => cases r with | nil => exact hMu1_nadj hadj | cons _ _ => simp at h
      rcases hAod_od with ⟨k, hk⟩; omega
    -- Extract internal edge y₁' - y₂' on A_od: A_od = M u₁ - y₁' - y₂' -(r_od)- M u₂
    obtain ⟨y₁', hMu1y1', q_od, hAod_eq1, hqod_path, hy1'1, hy1'2, _, hqod_len, hMu1_nqod⟩ :=
      path_split_first A_od hAod (by omega)
    obtain ⟨y₂', hy12', r_od, hqod_eq, hrod_path, hy2'1, hy2'2, _, hrod_len, hy1'_nrod⟩ :=
      path_split_first q_od hqod_path (by omega)
    have hy1'C2 : y₁' ∈ C2 := List.mem_toFinset.mpr ((hAsupp y₁').mp (Or.inr (by rw [hAod_eq1]; simp)))
    have hy2'C2 : y₂' ∈ C2 := List.mem_toFinset.mpr ((hAsupp y₂').mp (Or.inr (by rw [hAod_eq1, hqod_eq]; simp)))
    have hy2'_ne_Mu1 : y₂' ≠ M u₁ := fun h => hMu1_nqod (h ▸ (by rw [hqod_eq]; simp))
    have hy1'_not_Aev : y₁' ∉ A_ev.support := fun hm => hAdisj y₁' hm hy1'1 hy1'2 (by rw [hAod_eq1]; simp)
    have hy2'_not_Aev : y₂' ∉ A_ev.support := fun hm => hAdisj y₂' hm hy2'_ne_Mu1 hy2'2 (by rw [hAod_eq1, hqod_eq]; simp)
    -- Matching partners y₁ = M y₁', y₂ = M y₂' in C1 \ {u₁, u₂}
    let y₁ := M y₁'
    let y₂ := M y₂'
    have hy1C1 : y₁ ∈ C1 := (hM_C2 y₁' hy1'C2).1
    have hy2C1 : y₂ ∈ C1 := (hM_C2 y₂' hy2'C2).1
    have hy12_ne : y₁ ≠ y₂ := fun h => hy2'1 (hM_inj h).symm
    have hy1u1 : y₁ ≠ u₁ := fun h => hy1'1 (by rw [← hM_inv y₁', h])
    have hy1u2 : y₁ ≠ u₂ := fun h => hy1'2 (by rw [← hM_inv y₁', h])
    have hy2u1 : y₂ ≠ u₁ := fun h => hy2'_ne_Mu1 (by rw [← hM_inv y₂', h])
    have hy2u2 : y₂ ≠ u₂ := fun h => hy2'2 (by rw [← hM_inv y₂', h])
    -- Complementary path P₁ = C₁ - u₁u₂, and its subpath P between y₁ and y₂ (disjoint from {u₁, u₂}!)
    obtain ⟨P₁, hP₁, hP1_len, hP1_supp, _⟩ := hcomp_path c₁ hc₁ hc1_chordless hu1C hu2C hu12_adj
    have hy1P1 : y₁ ∈ P₁.support := (hP1_supp y₁).mpr (List.mem_toFinset.mp hy1C1)
    have hy2P1 : y₂ ∈ P₁.support := (hP1_supp y₂).mpr (List.mem_toFinset.mp hy2C1)
    -- Extract subpath P : G.Walk y₁ y₂ of P₁ avoiding u₁ and u₂
    have hex_P : ∃ P : G.Walk y₁ y₂, P.IsPath ∧ (∀ z ∈ P.support, z ∈ C1 ∧ z ≠ u₁ ∧ z ≠ u₂) ∧
        (P.length = c₁.length - 3 → (G.Adj u₁ y₁ ∨ G.Adj u₁ y₂)) := by
      -- Either y₁ precedes y₂ on P₁ or y₂ precedes y₁ on P₁!
      have horder : y₁ ∈ (P₁.takeUntil y₂ hy2P1).support ∨ y₂ ∈ (P₁.takeUntil y₁ hy1P1).support := by
        -- Standard induction on P₁
        have aux : ∀ {a b : V} (p : G.Walk a b) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support),
            x ∈ (p.takeUntil y hy).support ∨ y ∈ (p.takeUntil x hx).support := by
          intro a b p
          induction p with
          | nil => intro x y hx hy; simp at hx hy; subst hx; subst hy; left; simp
          | @cons u v w huv r ih =>
            intro x y hx hy
            by_cases hux : u = x
            · subst hux; left; exact SimpleGraph.Walk.start_mem_support _
            · by_cases huy : u = y
              · subst huy; right; exact SimpleGraph.Walk.start_mem_support _
              · have hx' : x ∈ r.support := by rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx; exact hx.resolve_left (Ne.symm hux)
                have hy' : y ∈ r.support := by rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy; exact hy.resolve_left (Ne.symm huy)
                rcases ih hx' hy' with h1 | h2
                · left; simp [SimpleGraph.Walk.takeUntil, huy, h1]
                · right; simp [SimpleGraph.Walk.takeUntil, hux, h2]
        exact aux P₁ hy1P1 hy2P1
      -- Helper: if a precedes b on P₁ (a, b ∉ {u₁, u₂}), P := (P₁.takeUntil b).dropUntil a avoids {u₁, u₂}
      -- and if P.length = c₁.length - 3 then G.Adj u₁ a!
      have hsub_of_ord : ∀ (a b : V) (ha : a ∈ P₁.support) (hb : b ∈ P₁.support)
          (hau1 : a ≠ u₁) (hau2 : a ≠ u₂) (hbu1 : b ≠ u₁) (hbu2 : b ≠ u₂) (hab : a ≠ b)
          (hprec : a ∈ (P₁.takeUntil b hb).support),
          ∃ P : G.Walk a b, P.IsPath ∧ (∀ z ∈ P.support, z ∈ C1 ∧ z ≠ u₁ ∧ z ≠ u₂) ∧
            (P.length = c₁.length - 3 → G.Adj u₁ a) := by
        intro a b ha hb hau1 hau2 hbu1 hbu2 hab hprec
        let Q_ub := P₁.takeUntil b hb
        let Q_bu2 := P₁.dropUntil b hb
        let Q_ua := Q_ub.takeUntil a hprec
        let P := Q_ub.dropUntil a hprec
        have hspec1 := SimpleGraph.Walk.take_spec P₁ hb
        have hspec2 := SimpleGraph.Walk.take_spec Q_ub hprec
        have hlen1 : Q_ub.length + Q_bu2.length = P₁.length := by rw [← SimpleGraph.Walk.length_append, hspec1]
        have hlen2 : Q_ua.length + P.length = Q_ub.length := by rw [← SimpleGraph.Walk.length_append, hspec2]
        have hQua_pos : 1 ≤ Q_ua.length := by cases Q_ua with | nil => exact absurd rfl hau1.symm | cons _ _ => simp
        have hQbu2_pos : 1 ≤ Q_bu2.length := by cases Q_bu2 with | nil => exact absurd rfl hbu2 | cons _ _ => simp
        refine ⟨P, (hP₁.takeUntil hb).dropUntil hprec, ?_, ?_⟩
        · intro z hz
          have hzQub := SimpleGraph.Walk.support_dropUntil_subset Q_ub hprec hz
          have hzP1 := SimpleGraph.Walk.support_takeUntil_subset P₁ hb hzQub
          refine ⟨List.mem_toFinset.mpr ((hP1_supp z).mp hzP1), ?_, ?_⟩
          · intro h; rw [h] at hz
            have hnd := (hP₁.takeUntil hb).support_nodup
            rw [← hspec2, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdc : P.support = a :: P.support.tail := by cases P <;> simp
            rw [hdc, List.mem_cons] at hz
            exact hnd.2.2 u₁ (SimpleGraph.Walk.start_mem_support Q_ua) u₁ (hz.resolve_left hau1.symm) rfl
          · intro h; rw [h] at hzQub
            have hnd := hP₁.support_nodup
            rw [← hspec1, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdc : Q_bu2.support = b :: Q_bu2.support.tail := by cases Q_bu2 <;> simp
            have hu2_in : u₂ ∈ Q_bu2.support := SimpleGraph.Walk.end_mem_support Q_bu2
            rw [hdc, List.mem_cons] at hu2_in
            exact hnd.2.2 u₂ hzQub u₂ (hu2_in.resolve_left hbu2.symm) rfl
        · intro hPlen_eq
          have h1 : Q_ua.length = 1 := by omega
          cases Q_ua with
          | nil => simp at h1
          | cons hadj r => cases r with | nil => exact hadj | cons _ _ => simp at h1
      rcases horder with h1 | h2
      · obtain ⟨P, hP, hPint, hPadj⟩ := hsub_of_ord y₁ y₂ hy1P1 hy2P1 hy1u1 hy1u2 hy2u1 hy2u2 hy12_ne h1
        exact ⟨P, hP, hPint, fun h => Or.inl (hPadj h)⟩
      · obtain ⟨P, hP, hPint, hPadj⟩ := hsub_of_ord y₂ y₁ hy2P1 hy1P1 hy2u1 hy2u2 hy1u1 hy1u2 hy12_ne.symm h2
        exact ⟨P.reverse, hP.reverse, fun z hz => hPint z (by simpa [SimpleGraph.Walk.support_reverse] using hz),
          fun h => Or.inr (hPadj (by simpa [SimpleGraph.Walk.length_reverse] using h))⟩
    rcases hex_P with ⟨P, hP, hP_int, hP_end_adj⟩
    -- Build disjoint cycles C₁' = u₁ - M u₁ -(A_ev)- M u₂ - u₂ - u₁ (odd!)
    -- and C₂' = y₁ -(P)- y₂ - y₂' - y₁' - y₁ (disjoint from C₁'!)
    have hAev_C2 : ∀ z ∈ A_ev.support, z ∈ C2 := fun z hz => List.mem_toFinset.mpr ((hAsupp z).mp (Or.inl hz))
    let q1 : G.Walk u₁ u₂ := SimpleGraph.Walk.cons hMu1_adj (A_ev.append (SimpleGraph.Walk.cons hMu2_adj.symm .nil))
    have hq1_sub : (A_ev.append (SimpleGraph.Walk.cons hMu2_adj.symm .nil)).IsPath := by
      apply isPath_append_of_disjoint_pc A_ev _ hAev (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj hMu2_adj.symm]))
      intro z hz1 hz2
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hz2
      rcases hz2 with rfl | rfl
      · rfl
      · exact False.elim (Finset.disjoint_left.mp hdisj hu2C1 (hAev_C2 u₂ hz1))
    have hq1 : q1.IsPath := SimpleGraph.Walk.IsPath.cons hq1_sub (fun hm => by
      rw [SimpleGraph.Walk.mem_support_append_iff] at hm
      rcases hm with h1 | h2
      · exact Finset.disjoint_left.mp hdisj hu1C1 (hAev_C2 u₁ h1)
      · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h2
        rcases h2 with h | h
        · exact Finset.disjoint_left.mp hdisj hu1C1 (h ▸ hMu2C2)
        · exact hu12_ne h)
    let e1 : G.Walk u₁ u₂ := SimpleGraph.Walk.cons hu12_adj .nil
    have he1 : e1.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e1, hu12_ne])
    let C₁' : G.Walk u₁ u₁ := q1.append e1.reverse
    have hC1' : C₁'.IsCycle := by
      apply isCycle_append_reverse_of_disjoint e1 q1 he1 hq1 _ (by simp [q1, e1, SimpleGraph.Walk.length_append]; omega)
      intro z _ hz1 hz2 hze; simp [e1] at hze; rcases hze with rfl | rfl <;> contradiction
    have hC1'_odd : Odd C₁'.length := by
      rcases hAev_ev with ⟨k, hk⟩
      exact ⟨k + 1, by simp [C₁', q1, e1, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
    let q2 : G.Walk y₁ y₂ := SimpleGraph.Walk.cons (hM_C2 y₁' hy1'C2).2.symm
      (SimpleGraph.Walk.cons hy12' (SimpleGraph.Walk.cons (hM_C2 y₂' hy2'C2).2 .nil))
    have hq2 : q2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      have h1 : y₁ ≠ y₁' := fun h => Finset.disjoint_left.mp hdisj hy1C1 (h ▸ hy1'C2)
      have h2 : y₁ ≠ y₂' := fun h => Finset.disjoint_left.mp hdisj hy1C1 (h ▸ hy2'C2)
      have h3' : y₁' ≠ y₂ := fun h => Finset.disjoint_left.mp hdisj hy2C1 (h ▸ hy1'C2)
      have h4 : y₂' ≠ y₂ := fun h => Finset.disjoint_left.mp hdisj hy2C1 (h ▸ hy2'C2)
      simp [q2, h1, h2, hy12_ne, hy2'1.symm, h3', h4])
    let C₂' : G.Walk y₁ y₁ := P.append q2.reverse
    have hP_pos : 1 ≤ P.length := by cases P with | nil => exact absurd rfl hy12_ne | cons _ _ => simp
    have hC2' : C₂'.IsCycle := by
      apply isCycle_append_reverse_of_disjoint q2 P hq2 hP _ (by simp [q2]; omega)
      intro z hzP hzy1 hzy2 hzq2
      simp only [q2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hzq2
      rcases hzq2 with rfl | rfl | rfl | rfl
      · exact absurd rfl hzy1
      · exact Finset.disjoint_left.mp hdisj (hP_int y₁' hzP).1 hy1'C2
      · exact Finset.disjoint_left.mp hdisj (hP_int y₂' hzP).1 hy2'C2
      · exact absurd rfl hzy2
    have hC12'_disj : Disjoint C₁'.support.toFinset C₂'.support.toFinset := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have hz1' := List.mem_toFinset.mp hz1
      have hz2' := List.mem_toFinset.mp hz2
      have hz1_cases : z = u₁ ∨ z = u₂ ∨ z ∈ A_ev.support := by
        dsimp only [C₁', q1, e1] at hz1'
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz1'
        rcases hz1' with h | h
        · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h
          rcases h with rfl | h'
          · exact Or.inl rfl
          · rw [SimpleGraph.Walk.mem_support_append_iff] at h'
            rcases h' with hA | he
            · exact Or.inr (Or.inr hA)
            · simp at he; rcases he with rfl | rfl
              · exact Or.inr (Or.inr (SimpleGraph.Walk.end_mem_support A_ev))
              · exact Or.inr (Or.inl rfl)
        · simp at h; rcases h with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
      have hz2_cases : z ∈ P.support ∨ z = y₁' ∨ z = y₂' := by
        dsimp only [C₂', q2] at hz2'
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz2'
        rcases hz2' with h | h
        · exact Or.inl h
        · simp at h; rcases h with rfl | rfl | rfl | rfl
          · exact Or.inl (SimpleGraph.Walk.start_mem_support P)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl (SimpleGraph.Walk.end_mem_support P)
      rcases hz1_cases with rfl | rfl | hzA <;> rcases hz2_cases with hzP | rfl | rfl
      · exact (hP_int u₁ hzP).2.1 rfl
      · exact Finset.disjoint_left.mp hdisj hu1C1 hy1'C2
      · exact Finset.disjoint_left.mp hdisj hu1C1 hy2'C2
      · exact (hP_int u₂ hzP).2.2 rfl
      · exact Finset.disjoint_left.mp hdisj hu2C1 hy1'C2
      · exact Finset.disjoint_left.mp hdisj hu2C1 hy2'C2
      · exact Finset.disjoint_left.mp hdisj (hP_int z hzP).1 (hAev_C2 z hzA)
      · exact hy1'_not_Aev hzA
      · exact hy2'_not_Aev hzA
    -- C₂' cannot be even (Lemma 3.4(1)), so C₂' is odd!
    have hC2'_odd : Odd C₂'.length := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      exact cycle_pair_obstructions_disjoint_even_odd S hconn h3 hnoc C₂' C₁' hC2' hC1' hev hC1'_odd hC12'_disj.symm
    -- By minimality of c₁.length + c₂.length, |C₁'| + |C₂'| ≥ c₁.length + c₂.length = Fintype.card V!
    have hsum_ge := hmin_sum C₁' C₂' hC1' hC2' hC1'_odd hC2'_odd hC12'_disj
    have hC1'_len : C₁'.length = A_ev.length + 3 := by
      simp [C₁', q1, e1, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    have hC2'_len : C₂'.length = P.length + 3 := by
      simp [C₂', q2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    -- Also P.length + 1 ≤ c₁.length - 2 (since P ⊆ C1 \ {u₁, u₂}), so P.length ≤ c₁.length - 3!
    have hP_le : P.length ≤ c₁.length - 3 := by
      have hsub : P.support.toFinset ⊆ (C1.erase u₁).erase u₂ := by
        intro z hz
        have ⟨hzC1, h1, h2⟩ := hP_int z (List.mem_toFinset.mp hz)
        exact Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hzC1⟩⟩
      have hle := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hP.support_nodup, SimpleGraph.Walk.length_support,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hu12_ne.symm, hu2C1⟩),
        Finset.card_erase_of_mem hu1C1, hC1_card] at hle
      omega
    -- Therefore A_od.length = 3 AND P.length = c₁.length - 3!
    have hAod_eq3 : A_od.length = 3 := by omega
    have hP_eq : P.length = c₁.length - 3 := by omega
    have hAev_ge4 : 4 ≤ A_ev.length := by omega
    have hd_eq3 : min A_ev.length A_od.length = 3 := by omega
    -- By hP_end_adj, either G.Adj u₁ y₁ or G.Adj u₁ y₂!
    rcases hP_end_adj hP_eq with hu1y1 | hu1y2
    · -- G.Adj u₁ y₁ → edge u₁y₁ of C₁ has M u₁ adjacent to M y₁ = y₁', contradicting hno_quad!
      have he : s(u₁, y₁) ∈ c₁.edges := hc1_chordless u₁ hu1C y₁ (List.mem_toFinset.mp hy1C1) hu1y1
      have hMy1 : M y₁ = y₁' := hM_inv y₁'
      exact hno_quad u₁ y₁ he (hMy1 ▸ hMu1y1')
    · -- G.Adj u₁ y₂ → edge u₁y₂ of C₁ has d_{C₂}(M u₁, y₂') ≤ 2 < 3, contradicting hd_min!
      have he : s(u₁, y₂) ∈ c₁.edges := hc1_chordless u₁ hu1C y₂ (List.mem_toFinset.mp hy2C1) hu1y2
      have hMy2 : M y₂ = y₂' := hM_inv y₂'
      -- Build the 2-path M u₁ - y₁' - y₂' on C₂ and its complementary odd path of length L - 2!
      obtain ⟨B₁, B₂, hB₁, hB₂, hBlen, hBsupp, hBdisj, _, _, _⟩ :=
        cycle_arcs_edges_subset c₂ hc₂ (List.mem_toFinset.mp hMu1C2) (List.mem_toFinset.mp hy2'C2) hy2'_ne_Mu1.symm
      -- Show min B₁.length B₂.length ≤ 2!
      -- Since M u₁ - y₁' - y₂' is a 2-path on c₂ (edges of A_od ⊆ c₂), one of B₁, B₂ has length 2!
      -- Specifically, y₁' lies on B₁ or B₂; in fact M u₁ ~ y₁' ~ y₂' with c₂ chordless, so if both B₁, B₂ had length ≥ 3,
      -- y₁' would be adjacent to both M u₁ and y₂' without both edges in c₂? Even simpler:
      -- Just construct the explicit even/odd arcs of c₂ from M u₁ to y₂' directly from A_ev and A_od!
      let P_2 : G.Walk (M u₁) (M y₂) := SimpleGraph.Walk.cons hMu1y1' (SimpleGraph.Walk.cons (hMy2 ▸ hy12') .nil)
      have hP2_path : P_2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
        simp [P_2, hMy2, hy1'1.symm, hy2'_ne_Mu1.symm, hy2'1.symm])
      -- Complementary odd path: A_ev ++ (M u₂ - y₂')!
      have hrod_len1 : r_od.length = 1 := by omega
      have hy2'Mu2 : G.Adj y₂' (M u₂) := by
        cases r_od with | nil => simp at hrod_len1 | cons h r => cases r with | nil => exact h | cons _ _ => simp at hrod_len1
      let P_odd : G.Walk (M u₁) (M y₂) := A_ev.append (SimpleGraph.Walk.cons (hMy2 ▸ hy2'Mu2.symm) .nil)
      have hPodd_path : P_odd.IsPath := by
        apply isPath_append_of_disjoint_pc A_ev _ hAev (SimpleGraph.Walk.IsPath.mk' (by simp [hMy2, hy2'2.symm]))
        intro z hz1 hz2
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz2
        rcases hz2 with rfl | rfl
        · rfl
        · exact False.elim (hy2'_not_Aev (hMy2 ▸ hz1))
      have hPodd_len : P_odd.length = A_ev.length + 1 := by simp [P_odd, SimpleGraph.Walk.length_append]
      have hP2_len : P_2.length = 2 := by simp [P_2]
      have hsupp_2 : ∀ z, z ∈ P_2.support ∨ z ∈ P_odd.support ↔ z ∈ c₂.support := by
        intro z; constructor
        · rintro (h | h)
          · simp only [P_2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl
            · exact List.mem_toFinset.mp hMu1C2
            · exact List.mem_toFinset.mp hy1'C2
            · rw [hMy2]; exact List.mem_toFinset.mp hy2'C2
          · dsimp only [P_odd] at h; rw [SimpleGraph.Walk.mem_support_append_iff] at h
            rcases h with hA | he
            · exact (hAsupp z).mp (Or.inl hA)
            · simp at he; rcases he with rfl | rfl
              · exact List.mem_toFinset.mp hMu2C2
              · rw [hMy2]; exact List.mem_toFinset.mp hy2'C2
        · intro hz
          rcases (hAsupp z).mpr hz with hA | hO
          · right; dsimp only [P_odd]; rw [SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hA
          · rw [hAod_eq1, hqod_eq] at hO
            cases r_od with
            | nil => simp at hrod_len1
            | cons _ r' => cases r' with
              | nil =>
                simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at hO
                rcases hO with rfl | rfl | rfl | rfl
                · left; simp [P_2]
                · left; simp [P_2]
                · left; simp [P_2, hMy2]
                · right; dsimp only [P_odd]; rw [SimpleGraph.Walk.mem_support_append_iff]; right; simp
              | cons _ _ => simp at hrod_len1
      have hdisj_2 : ∀ z ∈ P_2.support, z ≠ M u₁ → z ≠ M y₂ → z ∉ P_odd.support := by
        intro z hz h1 h2 hm
        simp only [P_2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact h1 rfl
        · dsimp only [P_odd] at hm; rw [SimpleGraph.Walk.mem_support_append_iff] at hm
          rcases hm with hA | he
          · exact hy1'_not_Aev hA
          · simp at he; rcases he with h | h; exact hy1'2 h; exact h2 h
        · exact h2 rfl
      have hle := hd_min u₁ y₂ (min P_2.length P_odd.length)
        ⟨he, P_2, P_odd, hP2_path, hPodd_path, by omega, ⟨1, by omega⟩,
          by rcases hAev_ev with ⟨k, hk⟩; exact ⟨k, by omega⟩, hsupp_2, hdisj_2, rfl⟩
      omega

end SignedGraphs
