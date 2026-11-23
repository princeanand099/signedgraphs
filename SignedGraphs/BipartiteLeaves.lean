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

/-- Every finite nonempty simple graph with minimum degree at least `2` contains a simple cycle. -/
private lemma exists_cycle_of_min_deg_two {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] [Nonempty W]
    (hdeg : ∀ w : W, 2 ≤ G.degree w) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle := by
  classical
  have hex : ∃ n : ℕ, ∃ (a b : W) (p : G.Walk a b), p.IsPath ∧ Fintype.card W - p.length = n := by
    obtain ⟨w₀⟩ := ‹Nonempty W›
    exact ⟨Fintype.card W, w₀, w₀, .nil, .nil, by simp⟩
  obtain ⟨a, b, p, hp, hmin_eq⟩ := Nat.find_spec hex
  have hmax : ∀ (a' b' : W) (q : G.Walk a' b'), q.IsPath → q.length ≤ p.length := by
    intro a' b' q hq
    have hle := Nat.find_min' hex ⟨a', b', q, hq, rfl⟩
    have hlen_p : p.length ≤ Fintype.card W := by
      have h1 : p.support.toFinset.card ≤ Fintype.card W := Finset.card_le_univ _
      rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support] at h1
      omega
    have hlen_q : q.length ≤ Fintype.card W := by
      have h1 : q.support.toFinset.card ≤ Fintype.card W := Finset.card_le_univ _
      rw [List.toFinset_card_of_nodup hq.support_nodup, SimpleGraph.Walk.length_support] at h1
      omega
    omega
  -- Every neighbor of `a` must lie in `p.support` (otherwise we can extend `p` by 1)
  have hnbr_in : ∀ w : W, G.Adj a w → w ∈ p.support := by
    intro w haw
    by_contra hnot
    have hq : (SimpleGraph.Walk.cons haw.symm p).IsPath := SimpleGraph.Walk.IsPath.cons hp hnot
    have hle := hmax w b (SimpleGraph.Walk.cons haw.symm p) hq
    simp at hle
  -- `a` has degree ≥ 2, so `a` has a neighbor `w` distinct from the second vertex of `p`
  cases hp_eq : p with
  | nil =>
    have hpos : 0 < (G.neighborFinset a).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := hdeg a; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have haw : G.Adj a w := (G.mem_neighborFinset a w).mp hw
    have hw_in : w ∈ p.support := hnbr_in w haw
    rw [hp_eq] at hw_in; simp at hw_in
    exact False.elim (G.ne_of_adj haw hw_in.symm)
  | @cons _ u _ hau r =>
    have hcard_er : 0 < ((G.neighborFinset a).erase u).card := by
      have h1 : (G.neighborFinset a).card = G.degree a := SimpleGraph.card_neighborFinset_eq_degree G a
      have h2 := hdeg a
      have h3 : ((G.neighborFinset a).erase u).card ≥ (G.neighborFinset a).card - 1 :=
        Finset.pred_card_le_card_erase
      omega
    obtain ⟨w, hw_er⟩ := Finset.card_pos.mp hcard_er
    have hwu : w ≠ u := (Finset.mem_erase.mp hw_er).1
    have haw : G.Adj a w := (G.mem_neighborFinset a w).mp (Finset.mem_of_mem_erase hw_er)
    have hwa : w ≠ a := (G.ne_of_adj haw).symm
    have hw_in : w ∈ p.support := hnbr_in w haw
    rw [hp_eq, SimpleGraph.Walk.support_cons, List.mem_cons] at hw_in
    have hw_r : w ∈ r.support := hw_in.resolve_left hwa
    let q : G.Walk a w := SimpleGraph.Walk.cons hau (r.takeUntil w hw_r)
    have hq_path : q.IsPath := by
      have hp_nd := hp.support_nodup
      rw [hp_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hp_nd
      have hr_path : r.IsPath := SimpleGraph.Walk.IsPath.mk' hp_nd.2
      exact SimpleGraph.Walk.IsPath.cons (hr_path.takeUntil hw_r)
        (fun hm => hp_nd.1 (SimpleGraph.Walk.support_takeUntil_subset r hw_r hm))
    have hq_ge2 : 2 ≤ q.length := by
      dsimp only [q]
      rw [SimpleGraph.Walk.length_cons]
      cases ht : r.takeUntil w hw_r with
      | nil => exact absurd rfl hwu.symm
      | cons _ _ => simp
    let e_aw : G.Walk a w := SimpleGraph.Walk.cons haw .nil
    have he_aw : e_aw.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [e_aw, hwa.symm])
    refine ⟨a, q.append e_aw.reverse, ?_⟩
    apply isCycle_append_reverse_of_disjoint e_aw q he_aw hq_path _ (by simp [e_aw]; omega)
    intro z _ hza hzw hze
    simp [e_aw] at hze; rcases hze with rfl | rfl <;> contradiction

/-- Deleting any single edge from `petersenGraph` still leaves a 5-cycle. -/
private lemma petersen_delete_edge_has_odd_cycle :
    ∀ u v : Fin 10, petersenGraph.Adj u v →
      ∃ (a b c d e : Fin 10),
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
        petersenGraph.Adj a b ∧ s(a, b) ≠ s(u, v) ∧
        petersenGraph.Adj b c ∧ s(b, c) ≠ s(u, v) ∧
        petersenGraph.Adj c d ∧ s(c, d) ≠ s(u, v) ∧
        petersenGraph.Adj d e ∧ s(d, e) ≠ s(u, v) ∧
        petersenGraph.Adj e a ∧ s(e, a) ≠ s(u, v) := by
  -- Use two edge-disjoint 5-cycles in petersenGraph: outer 0-1-2-3-4-0 and inner 5-7-9-6-8-5!
  intro u v huv
  by_cases hout : s(u, v) = s(0, 1) ∨ s(u, v) = s(1, 2) ∨ s(u, v) = s(2, 3) ∨
      s(u, v) = s(3, 4) ∨ s(u, v) = s(4, 0)
  · have hne : ∀ (a b : Fin 10),
        (s(a, b) ≠ s(0, 1) ∧ s(a, b) ≠ s(1, 2) ∧ s(a, b) ≠ s(2, 3) ∧
         s(a, b) ≠ s(3, 4) ∧ s(a, b) ≠ s(4, 0)) → s(a, b) ≠ s(u, v) := by
      intro a b h
      rcases hout with h' | h' | h' | h' | h' <;> rw [h']
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2
    refine ⟨5, 7, 9, 6, 8, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide,
      ?_, hne 5 7 (by decide), ?_, hne 7 9 (by decide), ?_, hne 9 6 (by decide),
      ?_, hne 6 8 (by decide), ?_, hne 8 5 (by decide)⟩
    all_goals (unfold petersenGraph; simp [SimpleGraph.fromRel])
  · push Not at hout
    refine ⟨0, 1, 2, 3, 4, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide,
      ?_, Ne.symm hout.1, ?_, Ne.symm hout.2.1, ?_, Ne.symm hout.2.2.1,
      ?_, Ne.symm hout.2.2.2.1, ?_, Ne.symm hout.2.2.2.2⟩
    all_goals (unfold petersenGraph; simp [SimpleGraph.fromRel])

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
  classical
  subst hH
  have hxy_ne : x ≠ y := T.ne_of_adj hxy
  -- First, H contains at least one simple (x, y)-path p₀
  have hex_p₀ : ∃ p₀ : (T.deleteEdges {s(x, y)}).Walk x y, p₀.IsPath := by
    have hdeg_x : 3 ≤ T.degree x := min_deg_three_of_three_conn hcard h3 x
    have hcard_er : 0 < ((T.neighborFinset x).erase y).card := by
      have h1 := SimpleGraph.card_neighborFinset_eq_degree T x
      have h2 : ((T.neighborFinset x).erase y).card ≥ (T.neighborFinset x).card - 1 :=
        Finset.pred_card_le_card_erase
      omega
    obtain ⟨w, hw_er⟩ := Finset.card_pos.mp hcard_er
    have hwy : w ≠ y := (Finset.mem_erase.mp hw_er).1
    have hxw : T.Adj x w := (T.mem_neighborFinset x w).mp (Finset.mem_of_mem_erase hw_er)
    have hwx : w ≠ x := (T.ne_of_adj hxw).symm
    obtain ⟨r⟩ := h3 {x} (by simp) ⟨w, by simp [hwx]⟩ ⟨y, by simp [hxy_ne.symm]⟩
    let f : T.induce (({x} : Finset V)ᶜ : Set V) →g T.deleteEdges {s(x, y)} :=
      { toFun := Subtype.val
        map_rel' := fun {a b} hab => by
          refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, fun h => ?_⟩
          have heq := Set.mem_singleton_iff.mp h
          rcases Sym2.eq_iff.mp heq with ⟨ha, _⟩ | ⟨_, hb⟩
          · exact a.2 (by simp [ha])
          · exact b.2 (by simp [hb]) }
    have hxw' : (T.deleteEdges {s(x, y)}).Adj x w := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hxw, fun h => ?_⟩
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hwy h2
      · exact hxy_ne h1
    let p_raw := SimpleGraph.Walk.cons hxw' (r.map f)
    exact ⟨p_raw.toPath.1, p_raw.toPath.2⟩
  rcases hex_p₀ with ⟨p₀, hp₀⟩
  by_contra hno_div
  push Not at hno_div
  -- Because H is bipartite, all (x, y)-paths in H have the same length parity, hence same mod-4 weight!
  have hconst : ∀ p : (T.deleteEdges {s(x, y)}).Walk x y, p.IsPath →
      walkModFourWeight σ p = walkModFourWeight σ p₀ := by
    intro p hp
    have hev_loop : Even (p.append p₀.reverse).length := even_length_of_isBipartite hbip (p.append p₀.reverse)
    have h2diff : 2 * (walkModFourWeight σ p - walkModFourWeight σ p₀) = 0 := by
      rw [mul_sub, two_mul_walkModFourWeight, two_mul_walkModFourWeight]
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hev_loop
      rcases hev_loop with ⟨k, hk⟩
      have h1 : 2 * (p.length : ZMod 4) + 2 * (p₀.length : ZMod 4) = 0 := by
        have : 2 * (p.length : ZMod 4) + 2 * (p₀.length : ZMod 4) =
            (4 : ZMod 4) * (k : ZMod 4) := by
          have hk' : ((p.length + p₀.length : ℕ) : ZMod 4) = ((k + k : ℕ) : ZMod 4) := by rw [hk]
          push_cast at hk' ⊢; linear_combination 2 * hk'
        have h4 : (4 : ZMod 4) = 0 := rfl
        rw [this, h4, zero_mul]
      have h4 : (4 : ZMod 4) = 0 := rfl
      linear_combination h1 - h4 * (p₀.length : ZMod 4)
    have hne2 := hno_div p p₀ hp hp₀
    generalize hd : walkModFourWeight σ p - walkModFourWeight σ p₀ = d
    rw [hd] at h2diff hne2
    fin_cases d
    · exact sub_eq_zero.mp hd
    · exact absurd h2diff (by decide)
    · exact absurd rfl hne2
    · exact absurd h2diff (by decide)
  rcases hbip with ⟨fH⟩
  have hfH_par : ∀ {a b : V} (q : (T.deleteEdges {s(x, y)}).Walk a b),
      ((fH b).val + (fH a).val + q.length) % 2 = 0 := by
    intro a b q
    induction q with
    | nil => simp; omega
    | @cons u v z huv r ih =>
      have hne : (fH u).val ≠ (fH v).val := fun h => fH.valid huv (Fin.ext h)
      have hu2 := (fH u).isLt; have hv2 := (fH v).isLt
      simp only [SimpleGraph.Walk.length_cons]; omega
  -- Case split on whether x and y are in the same bipartition class of H
  by_cases hsame : fH x = fH y
  · -- CASE 1: x and y lie in the same bipartition class of H → T is 3-connected non-bipartite NOC!
    have hp₀_ev : Even p₀.length := by
      have h1 := hfH_par p₀
      rw [hsame] at h1
      exact ⟨p₀.length / 2, by omega⟩
    let r : ZMod 4 := walkModFourWeight σ p₀
    have hr02 : r = 0 ∨ r = 2 := walkModFourWeight_even_of_even_length σ p₀ hp₀_ev
    let σT : Sym2 V → ℤ := fun e => if e = s(x, y) then (if r = 0 then -1 else 1) else σ e
    have hσT_pm : ∀ e ∈ T.edgeSet, σT e = 1 ∨ σT e = -1 := by
      intro e he
      dsimp only [σT]
      split_ifs with h1 h2
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact hσ e (by rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨he, fun hm => h1 (Set.mem_singleton_iff.mp hm)⟩)
    let ST : SignedGraph V := ⟨T, σT, hσT_pm⟩
    have hT_nonbip : ¬ T.IsBipartite := by
      intro hTbip
      let φ : T.deleteEdges {s(x, y)} →g T := SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _)
      let cyc : T.Walk x x := (p₀.map φ).append (SimpleGraph.Walk.cons hxy.symm .nil)
      have hev_c := even_length_of_isBipartite hTbip cyc
      simp only [cyc, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_map,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hev_c
      rcases hp₀_ev with ⟨a, ha⟩; rcases hev_c with ⟨b, hb⟩; omega
    have hST_noc : IsNOC ST := by
      rw [isNOC_iff_isNOCModFour]
      intro v c hc hodd
      -- c must contain s(x, y), otherwise it lives in H which is bipartite!
      have hxy_in : s(x, y) ∈ c.edges := by
        by_contra hnot
        let cH : (T.deleteEdges {s(x, y)}).Walk v v := c.transfer (T.deleteEdges {s(x, y)}) (fun e he => by
          rw [SimpleGraph.edgeSet_deleteEdges]
          exact ⟨c.edges_subset_edgeSet he, fun h => hnot (Set.mem_singleton_iff.mp h ▸ he)⟩)
        have hev_cH := even_length_of_isBipartite ⟨fH⟩ cH
        rw [SimpleGraph.Walk.length_transfer] at hev_cH
        rcases hev_cH with ⟨a, ha⟩; rcases hodd with ⟨b, hb⟩; omega
      -- Split c at edge s(x, y) into a simple (x, y)-path q in H
      have hx_in : x ∈ c.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c hxy_in
      have hy_in : y ∈ c.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges c hxy_in
      obtain ⟨arc1, arc2, harc1, harc2, harc_len, _, _, harc_e1, harc_e2, harc_w⟩ :=
        cycle_arcs_edges_subset c hc hx_in hy_in hxy_ne
      -- One of arc1, arc2 is the single edge s(x, y), and the other avoids s(x, y)!
      have hone : (arc1.length = 1 ∧ s(x, y) ∉ arc2.edges) ∨ (arc2.length = 1 ∧ s(x, y) ∉ arc1.edges) := by
        have hlen_ge3 : 3 ≤ arc1.length + arc2.length := by rw [harc_len]; exact hc.three_le_length
        -- Check whether s(x, y) ∈ arc1.edges
        by_cases h1 : s(x, y) ∈ arc1.edges
        · left
          have hlen1 : arc1.length = 1 := by
            cases arc1 with
            | nil => simp at h1
            | @cons _ w _ hxw' q =>
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h1
              rcases h1 with heq | hq
              · rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, h2⟩
                · cases q with
                  | nil => rfl
                  | cons _ q' =>
                    have hnd := harc1.support_nodup
                    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                    exact absurd (by simp [SimpleGraph.Walk.end_mem_support q']) hnd.2.1
                · exact absurd h2.symm hxy_ne
              · have hnd := harc1.support_nodup
                rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges q hq) hnd.1
          refine ⟨hlen1, fun h2 => ?_⟩
          have hlen2 : arc2.length = 1 := by
            cases arc2 with
            | nil => simp at h2
            | @cons _ w _ hxw' q =>
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h2
              rcases h2 with heq | hq
              · rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, h2'⟩
                · cases q with
                  | nil => rfl
                  | cons _ q' =>
                    have hnd := harc2.support_nodup
                    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                    exact absurd (by simp [SimpleGraph.Walk.end_mem_support q']) hnd.2.1
                · exact absurd h2'.symm hxy_ne
              · have hnd := harc2.support_nodup
                rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges q hq) hnd.1
          omega
        · right
          have h2 : s(x, y) ∈ arc2.edges := by
            by_contra h2
            let q1 : (T.deleteEdges {s(x, y)}).Walk x y := arc1.transfer _ (fun e he => by
              rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨arc1.edges_subset_edgeSet he, fun h => h1 (Set.mem_singleton_iff.mp h ▸ he)⟩)
            let q2 : (T.deleteEdges {s(x, y)}).Walk x y := arc2.transfer _ (fun e he => by
              rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨arc2.edges_subset_edgeSet he, fun h => h2 (Set.mem_singleton_iff.mp h ▸ he)⟩)
            have hev_cH := even_length_of_isBipartite ⟨fH⟩ (q1.append q2.reverse)
            dsimp only [q1, q2] at hev_cH
            simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
              SimpleGraph.Walk.length_transfer] at hev_cH
            rw [harc_len] at hev_cH
            rcases hev_cH with ⟨a, ha⟩; rcases hodd with ⟨b, hb⟩; omega
          have hlen2 : arc2.length = 1 := by
            cases arc2 with
            | nil => simp at h2
            | @cons _ w _ hxw' q =>
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h2
              rcases h2 with heq | hq
              · rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, h2'⟩
                · cases q with
                  | nil => rfl
                  | cons _ q' =>
                    have hnd := harc2.support_nodup
                    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                    exact absurd (by simp [SimpleGraph.Walk.end_mem_support q']) hnd.2.1
                · exact absurd h2'.symm hxy_ne
              · have hnd := harc2.support_nodup
                rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges q hq) hnd.1
          exact ⟨hlen2, h1⟩
      have hcalc : ∀ (e_arc p_arc : T.Walk x y), e_arc.length = 1 → p_arc.IsPath → s(x, y) ∉ p_arc.edges →
          walkModFourWeight ST.sign e_arc + walkModFourWeight ST.sign p_arc = walkModFourWeight ST.sign c →
          walkModFourWeight ST.sign c = 3 := by
        intro e_arc p_arc he1 hp_arc hnot_xy hsum
        have he_w : walkModFourWeight ST.sign e_arc = modFourWeight σT s(x, y) := by
          cases e_arc with
          | nil => simp at he1
          | @cons _ w _ hxw' q =>
            cases q with
            | nil => simp [walkModFourWeight, ST]
            | cons _ _ => simp at he1
        let pH : (T.deleteEdges {s(x, y)}).Walk x y := p_arc.transfer _ (fun e he => by
          rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨p_arc.edges_subset_edgeSet he, fun h => hnot_xy (Set.mem_singleton_iff.mp h ▸ he)⟩)
        have hpH_path : pH.IsPath := SimpleGraph.Walk.IsPath.mk' (by
          rw [SimpleGraph.Walk.support_transfer]; exact hp_arc.support_nodup)
        have hp_w : walkModFourWeight ST.sign p_arc = walkModFourWeight σ pH := by
          unfold walkModFourWeight
          rw [SimpleGraph.Walk.edges_transfer]
          congr 1
          apply List.map_congr_left
          intro e he
          have hne : e ≠ s(x, y) := fun h => hnot_xy (h ▸ he)
          simp [ST, σT, modFourWeight, hne]
        rw [← hsum, he_w, hp_w, hconst pH hpH_path]
        rcases hr02 with hr0 | hr2
        · simp [σT, modFourWeight, r, hr0]
        · simp [σT, modFourWeight, r, hr2]; decide
      rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hcalc arc1 arc2 h1 harc2 h2 (harc_w ST.sign)
      · exact hcalc arc2 arc1 h1 harc1 h2 (by rw [add_comm]; exact harc_w ST.sign)
    -- Apply Theorem 3.1 to ST!
    rcases three_connected_non_bipartite_noc_classification ST hcard hconn h3 hT_nonbip hST_noc with
      ⟨e, _, _⟩ | ⟨e, _, _⟩
    · -- T ≅ K₄: pick 2 vertices a, b ∈ Fin 4 distinct from e x, e y; {x, e.symm a, e.symm b} is a triangle in H!
      have hex_a : ∃ a : Fin 4, a ≠ e x ∧ a ≠ e y := by
        generalize hx' : e x = ex; generalize hy' : e y = ey; fin_cases ex <;> fin_cases ey <;> decide
      rcases hex_a with ⟨a, hax, hay⟩
      have hex_b : ∃ b : Fin 4, b ≠ e x ∧ b ≠ e y ∧ b ≠ a := by
        have hcard3 : 3 < Fintype.card (Fin 4) := by decide
        have hlt : ({e x, e y, a} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
          have h1 : ({e x, e y, a} : Finset (Fin 4)).card ≤ 3 := by
            calc ({e x, e y, a} : Finset (Fin 4)).card
                ≤ ({e y, a} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
              _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
          rw [Finset.card_univ, Fintype.card_fin]; omega
        obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
        exact ⟨b, hb.1, hb.2.1, hb.2.2⟩
      rcases hex_b with ⟨b, hbx, hby, hba⟩
      let u := e.symm a
      let w := e.symm b
      have hux : u ≠ x := fun h => hax (by rw [← h]; simp [u])
      have huy : u ≠ y := fun h => hay (by rw [← h]; simp [u])
      have hwx : w ≠ x := fun h => hbx (by rw [← h]; simp [w])
      have hwy : w ≠ y := fun h => hby (by rw [← h]; simp [w])
      have huw : u ≠ w := fun h => hba (by have := congrArg e h; simpa [u, w] using this.symm)
      have hadj_xu : (T.deleteEdges {s(x, y)}).Adj x u := SimpleGraph.deleteEdges_adj.mpr
        ⟨e.map_rel_iff.mp (show (⊤ : SimpleGraph (Fin 4)).Adj (e x) (e u) from by simp [u, hax.symm]),
         fun h => by rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨_, h2⟩ | ⟨h1, _⟩; exact huy h2; exact hxy_ne h1⟩
      have hadj_uw : (T.deleteEdges {s(x, y)}).Adj u w := SimpleGraph.deleteEdges_adj.mpr
        ⟨e.map_rel_iff.mp (show (⊤ : SimpleGraph (Fin 4)).Adj (e u) (e w) from by simp [u, w, hba.symm]),
         fun h => by rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨h1, _⟩ | ⟨h1, _⟩; exact hux h1; exact huy h1⟩
      have hadj_wx : (T.deleteEdges {s(x, y)}).Adj w x := SimpleGraph.deleteEdges_adj.mpr
        ⟨e.map_rel_iff.mp (show (⊤ : SimpleGraph (Fin 4)).Adj (e w) (e x) from by simp [w, hbx]),
         fun h => by rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨h1, _⟩ | ⟨h1, _⟩; exact hwx h1; exact hwy h1⟩
      let tri : (T.deleteEdges {s(x, y)}).Walk x x :=
        SimpleGraph.Walk.cons hadj_xu (SimpleGraph.Walk.cons hadj_uw (SimpleGraph.Walk.cons hadj_wx .nil))
      have hev := even_length_of_isBipartite ⟨fH⟩ tri
      simp [tri] at hev
      exact absurd hev (by decide)
    · -- T ≅ Petersen: petersenGraph - s(e x, e y) still has a 5-cycle!
      have hexy : petersenGraph.Adj (e x) (e y) := e.map_rel_iff.mpr hxy
      obtain ⟨a, b, c, d, g, _, _, _, _, _, _, _, _, _, _, hab, h1, hbc, h2, hcd, h3', hdg, h4', hga, h5⟩ :=
        petersen_delete_edge_has_odd_cycle (e x) (e y) hexy
      have hlift_e : ∀ {p q : Fin 10}, petersenGraph.Adj p q → s(p, q) ≠ s(e x, e y) →
          (T.deleteEdges {s(x, y)}).Adj (e.symm p) (e.symm q) := by
        intro p q hpq hne
        refine SimpleGraph.deleteEdges_adj.mpr ⟨e.map_rel_iff.mp (by simpa [petersenSignedGraph] using hpq), fun h => hne ?_⟩
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · have hp : p = e x := by rw [← h1']; simp
          have hq : q = e y := by rw [← h2']; simp
          rw [hp, hq]
        · have hp : p = e y := by rw [← h1']; simp
          have hq : q = e x := by rw [← h2']; simp
          rw [hp, hq, Sym2.eq_swap]
      let c5 : (T.deleteEdges {s(x, y)}).Walk (e.symm a) (e.symm a) :=
        SimpleGraph.Walk.cons (hlift_e hab h1) (SimpleGraph.Walk.cons (hlift_e hbc h2)
          (SimpleGraph.Walk.cons (hlift_e hcd h3') (SimpleGraph.Walk.cons (hlift_e hdg h4')
            (SimpleGraph.Walk.cons (hlift_e hga h5) .nil))))
      have hev := even_length_of_isBipartite ⟨fH⟩ c5
      simp [c5] at hev
      exact absurd hev (by decide)
  · -- CASE 2: fH x ≠ fH y → T itself is bipartite!
    have hT_bip : T.IsBipartite := by
      refine ⟨SimpleGraph.Coloring.mk fH ?_⟩
      intro u v huv
      by_cases he : s(u, v) = s(x, y)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hsame
        · exact Ne.symm hsame
      · exact fH.valid (SimpleGraph.deleteEdges_adj.mpr ⟨huv, fun h => he (Set.mem_singleton_iff.mp h)⟩)
    -- Every vertex in V \ {x, y} has degree ≥ 2 in T - {x, y}
    let D_xy : Finset V := {x, y}
    let Rest := {w : V // w ∉ D_xy}
    have hRest_ne : Nonempty Rest := by
      have hlt : D_xy.card < Fintype.card V := by
        have := Finset.card_le_two (a := x) (b := y); dsimp only [D_xy]; omega
      obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card (by simpa [Finset.card_univ] using hlt : D_xy.card < (Finset.univ : Finset V).card)
      exact ⟨⟨w, hw⟩⟩
    have hRest_deg2 : ∀ w : Rest, 2 ≤ (T.induce ((D_xy : Set V)ᶜ)).degree w := by
      intro w
      have hdeg3 : 3 ≤ T.degree w.1 := min_deg_three_of_three_conn hcard h3 w.1
      -- w can be adjacent to at most ONE of {x, y} since fH x ≠ fH y and fH is a coloring of T!
      have hatmost1 : (T.neighborFinset w.1 ∩ D_xy).card ≤ 1 := by
        by_contra hgt
        have hx_in : x ∈ T.neighborFinset w.1 := by
          by_contra hx_n
          have hsub : T.neighborFinset w.1 ∩ D_xy ⊆ {y} := by
            intro z hz; rw [Finset.mem_inter] at hz
            simp only [D_xy, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz.2 with rfl | rfl
            · exact absurd hz.1 hx_n
            · simp
          have := (Finset.card_le_card hsub).trans (by simp : ({y} : Finset V).card ≤ 1)
          omega
        have hy_in : y ∈ T.neighborFinset w.1 := by
          by_contra hy_n
          have hsub : T.neighborFinset w.1 ∩ D_xy ⊆ {x} := by
            intro z hz; rw [Finset.mem_inter] at hz
            simp only [D_xy, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz.2 with rfl | rfl
            · simp
            · exact absurd hz.1 hy_n
          have := (Finset.card_le_card hsub).trans (by simp : ({x} : Finset V).card ≤ 1)
          omega
        have hwx : T.Adj w.1 x := (T.mem_neighborFinset w.1 x).mp hx_in
        have hwy : T.Adj w.1 y := (T.mem_neighborFinset w.1 y).mp hy_in
        rcases hT_bip with ⟨fT⟩
        have h1 : fT w.1 ≠ fT x := fT.valid hwx
        have h2 : fT w.1 ≠ fT y := fT.valid hwy
        have h3' : fT x ≠ fT y := fT.valid hxy
        generalize hfw : fT w.1 = fw; generalize hfx : fT x = fx; generalize hfy : fT y = fy
        rw [hfw, hfx] at h1; rw [hfw, hfy] at h2; rw [hfx, hfy] at h3'
        fin_cases fw <;> fin_cases fx <;> fin_cases fy <;> simp_all
      have hdiff_ge2 : 2 ≤ (T.neighborFinset w.1 \ D_xy).card := by
        have := Finset.card_sdiff_add_card_inter (T.neighborFinset w.1) D_xy
        rw [SimpleGraph.card_neighborFinset_eq_degree] at this
        omega
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let emb : V → Rest := fun z => if hz : z ∉ D_xy then ⟨z, hz⟩ else w
      calc 2 ≤ (T.neighborFinset w.1 \ D_xy).card := hdiff_ge2
        _ = ((T.neighborFinset w.1 \ D_xy).image emb).card := by
            rw [Finset.card_image_of_injOn]
            intro a ha b hb hab
            have ha' : a ∉ D_xy := (Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)).2
            have hb' : b ∉ D_xy := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hb)).2
            exact congrArg Subtype.val (by simpa [emb, dif_pos ha', dif_pos hb'] using hab)
        _ ≤ ((T.induce ((D_xy : Set V)ᶜ)).neighborFinset w).card := by
            apply Finset.card_le_card
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
            rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at ha
            simp only [emb, dif_pos ha.2, SimpleGraph.mem_neighborFinset]
            exact ha.1
    haveI : Nonempty ((D_xy : Set V)ᶜ : Set V) := hRest_ne
    obtain ⟨v₀_sub, c₀_sub, hc₀_sub⟩ := exists_cycle_of_min_deg_two (T.induce ((D_xy : Set V)ᶜ)) hRest_deg2
    let fR : T.induce ((D_xy : Set V)ᶜ) →g T := (SimpleGraph.Embedding.induce ((D_xy : Set V)ᶜ)).toHom
    let c₀ : T.Walk v₀_sub.1 v₀_sub.1 := c₀_sub.map fR
    have hc₀ : c₀.IsCycle := by
      refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
      · rw [SimpleGraph.Walk.edges_map]
        exact hc₀_sub.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
      · intro hnil; cases c₀_sub with | nil => exact hc₀_sub.ne_nil rfl | cons _ _ => simp [c₀] at hnil
      · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
        exact hc₀_sub.support_nodup.map Subtype.val_injective
    have hev₀ : Even c₀.length := even_length_of_isBipartite hT_bip c₀
    have hdisj₀ : Disjoint c₀.support.toFinset D_xy := by
      rw [Finset.disjoint_left]; intro z hz
      have hz' := List.mem_toFinset.mp hz
      dsimp only [c₀] at hz'
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz'
      rcases hz' with ⟨z', _, rfl⟩; exact z'.2
    have hD_conn : ∀ (a : V) (ha : a ∈ D_xy) (b : V) (hb : b ∈ D_xy), (T.induce (D_xy : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a ha b hb
      simp only [D_xy, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable hxy
      · exact SimpleGraph.Adj.reachable hxy.symm
      · exact SimpleGraph.Reachable.refl _
    obtain ⟨v, c, hc, hev, hdisj_c, hK_conn, hchord_ev, _⟩ :=
      maximal_even_cycle_lemma T h3 D_xy x (by simp [D_xy]) hD_conn c₀ hc₀ hev₀ hdisj₀
    -- Because T is bipartite, c is CHORDLESS!
    have hchordless : ∀ a ∈ c.support, ∀ b ∈ c.support, T.Adj a b → s(a, b) ∈ c.edges := by
      intro a ha b hb hab
      by_contra hch
      have hne : a ≠ b := T.ne_of_adj hab
      obtain ⟨arc1, arc2, harc1, harc2, harc_len, _, _, harc_e1, harc_e2, _⟩ :=
        cycle_arcs_edges_subset c hc ha hb hne
      have ⟨hev1, _⟩ := hchord_ev a b ha hb hne hab hch arc1 arc2 harc1 harc2 harc_len harc_e1 harc_e2
      have hcl := even_length_of_isBipartite hT_bip (arc1.append (SimpleGraph.Walk.cons hab.symm .nil))
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hcl
      rcases hev1 with ⟨k1, hk1⟩; rcases hcl with ⟨k2, hk2⟩; omega
    have hall_nbr : ∀ a ∈ c.support.toFinset, ∃ w ∉ c.support.toFinset, T.Adj a w := fun a ha =>
      exists_neighbor_outside_even h3 c hc hev (List.mem_toFinset.mp ha)
        (fun b hb hab => hchordless a (List.mem_toFinset.mp ha) b hb hab)
    -- Helper: two disjoint paths in T from {x, y} to {u₁, u₂} ⊆ c internally disjoint from C ∪ {x, y}
    -- force w(C) + 2 * d_C(u₁, u₂) ≠ 2!
    have hlink_contra : ∀ (u₁ u₂ : V), u₁ ∈ c.support → u₂ ∈ c.support → u₁ ≠ u₂ →
        ∀ (L₁ : T.Walk x u₁) (L₂ : T.Walk y u₂), L₁.IsPath → L₂.IsPath →
        (∀ z ∈ L₁.support, z ∉ L₂.support) →
        (∀ z ∈ L₁.support, z ≠ x → z ≠ u₁ → z ∉ c.support) →
        (∀ z ∈ L₂.support, z ≠ y → z ≠ u₂ → z ∉ c.support) →
        ∀ (arc1 arc2 : T.Walk u₁ u₂), arc1.IsPath → arc2.IsPath →
        (∀ z, z ∈ arc1.support ∨ z ∈ arc2.support ↔ z ∈ c.support) →
        (walkModFourWeight σ arc1 + walkModFourWeight σ arc2) + 2 * (arc2.length : ZMod 4) = 2 →
        False := by
      intro u₁ u₂ hu₁ hu₂ hu12 L₁ L₂ hL₁ hL₂ hLdisj hL₁_int hL₂_int arc1 arc2 harc1 harc2 harc_supp hw2
      have hbuild : ∀ (arc : T.Walk u₁ u₂), arc.IsPath → (∀ z ∈ arc.support, z ∈ c.support) →
          ∃ P : (T.deleteEdges {s(x, y)}).Walk x y, P.IsPath ∧
            walkModFourWeight σ P = walkModFourWeight σ L₁ + walkModFourWeight σ arc + walkModFourWeight σ L₂ := by
        intro arc harc harcC
        have h1 : (L₁.append arc).IsPath := by
          apply isPath_append_of_disjoint_pc L₁ arc hL₁ harc
          intro z hz1 hza
          by_contra hzu1
          have hzx : z ≠ x := fun h => Finset.disjoint_left.mp hdisj_c (List.mem_toFinset.mpr (harcC z hza)) (by simp [D_xy, h])
          exact hL₁_int z hz1 hzx hzu1 (harcC z hza)
        have h2 : ((L₁.append arc).append L₂.reverse).IsPath := by
          apply isPath_append_of_disjoint_pc (L₁.append arc) L₂.reverse h1 hL₂.reverse
          intro z hz1 hz2
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz2
          rw [SimpleGraph.Walk.mem_support_append_iff] at hz1
          rcases hz1 with hzL1 | hza
          · exact False.elim (hLdisj z hzL1 hz2)
          · by_contra hzu2
            have hzy : z ≠ y := fun h => Finset.disjoint_left.mp hdisj_c (List.mem_toFinset.mpr (harcC z hza)) (by simp [D_xy, h])
            exact hL₂_int z hz2 hzy hzu2 (harcC z hza)
        let PT := (L₁.append arc).append L₂.reverse
        have hnot_xy : s(x, y) ∉ PT.edges := by
          intro hmem
          dsimp only [PT] at hmem
          rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_append,
            List.mem_append, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hmem
          rcases hmem with (hm | hm) | hm
          · exact hLdisj y (SimpleGraph.Walk.snd_mem_support_of_mem_edges L₁ hm) (SimpleGraph.Walk.start_mem_support L₂)
          · exact Finset.disjoint_left.mp hdisj_c (List.mem_toFinset.mpr (harcC x (SimpleGraph.Walk.fst_mem_support_of_mem_edges arc hm))) (by simp [D_xy])
          · exact hLdisj x (SimpleGraph.Walk.start_mem_support L₁) (SimpleGraph.Walk.fst_mem_support_of_mem_edges L₂ hm)
        let PH : (T.deleteEdges {s(x, y)}).Walk x y := PT.transfer _ (fun e he => by
          rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨PT.edges_subset_edgeSet he, fun h => hnot_xy (Set.mem_singleton_iff.mp h ▸ he)⟩)
        refine ⟨PH, SimpleGraph.Walk.IsPath.mk' (by rw [SimpleGraph.Walk.support_transfer]; exact h2.support_nodup), ?_⟩
        have htr : walkModFourWeight σ PH = walkModFourWeight σ PT := by
          simp [PH, walkModFourWeight, SimpleGraph.Walk.edges_transfer]
        rw [htr]
        simp [PT, walkModFourWeight_append, walkModFourWeight_reverse]
      obtain ⟨P₁, hP₁, hwP₁⟩ := hbuild arc1 harc1 (fun z hz => (harc_supp z).mp (Or.inl hz))
      obtain ⟨P₂, hP₂, hwP₂⟩ := hbuild arc2 harc2 (fun z hz => (harc_supp z).mp (Or.inr hz))
      have heq : walkModFourWeight σ P₁ = walkModFourWeight σ P₂ := by
        rw [hconst P₁ hP₁, hconst P₂ hP₂]
      rw [hwP₁, hwP₂] at heq
      have hdiff0 : walkModFourWeight σ arc1 - walkModFourWeight σ arc2 = 0 := by linear_combination heq
      have h31 := even_cycle_arc_weight_diff σ arc1 arc2
      rw [hdiff0, hw2] at h31
      exact absurd h31 (by decide)
    obtain ⟨col, hcol2, _, hcol_walk⟩ := even_cycle_bipartition c hc hev
    let X : Finset V := c.support.toFinset.filter fun u => col u = 0
    let Y : Finset V := c.support.toFinset.filter fun u => col u = 1
    have ⟨hX_ge2, hY_ge2⟩ := even_cycle_part_card_ge_two c hc hev col hcol2 hcol_walk
    have hXY_disj : Disjoint X Y := by
      rw [Finset.disjoint_left]; intro z h1 h2; simp only [X, Y, Finset.mem_filter] at h1 h2; omega
    rcases walkModFourWeight_even_of_even_length σ c hev with hw0 | hw2
    · -- Subcase 2a: w(c) = 0 → G_plus Menger gives two disjoint paths from {X, Y} to {x, y}
      let K_type := {z : V // z ∈ ((c.support.toFinset : Set V)ᶜ)}
      let G_plus : SimpleGraph (Fin 2 ⊕ K_type) :=
        { Adj := fun a b => match a, b with
            | Sum.inr u, Sum.inr w => T.Adj u.1 w.1
            | Sum.inl 0, Sum.inr w => ∃ u ∈ X, T.Adj u w.1
            | Sum.inr w, Sum.inl 0 => ∃ u ∈ X, T.Adj u w.1
            | Sum.inl 1, Sum.inr w => ∃ u ∈ Y, T.Adj u w.1
            | Sum.inr w, Sum.inl 1 => ∃ u ∈ Y, T.Adj u w.1
            | _, _ => False
          symm := ⟨fun a b h => by
            cases a with
            | inl i => fin_cases i <;> cases b <;> simpa using h
            | inr u => cases b with
              | inl j => fin_cases j <;> simpa using h
              | inr w => exact h.symm⟩
          loopless := ⟨fun a h => by
            cases a with
            | inl i => fin_cases i <;> exact h
            | inr u => exact T.ne_of_adj h rfl⟩ }
      let xK : K_type := ⟨x, Finset.disjoint_right.mp hdisj_c (by simp [D_xy])⟩
      let yK : K_type := ⟨y, Finset.disjoint_right.mp hdisj_c (by simp [D_xy])⟩
      let A_p : Finset (Fin 2 ⊕ K_type) := {Sum.inl 0, Sum.inl 1}
      let B_p : Finset (Fin 2 ⊕ K_type) := {Sum.inr xK, Sum.inr yK}
      have hAp_card : 2 ≤ A_p.card := by
        rw [Finset.card_pair]; intro h; exact absurd (Sum.inl.inj h) (by decide)
      have hBp_card : 2 ≤ B_p.card := by
        rw [Finset.card_pair]; intro h; exact hxy_ne (congrArg Subtype.val (Sum.inr.inj h))
      have hGp_no_cut : ∀ z : Fin 2 ⊕ K_type, ∃ a ∈ A_p, ∃ b ∈ B_p,
          ∃ p : G_plus.Walk a b, z ∉ p.support := by
        intro z
        cases z with
        | inl i =>
          fin_cases i
          · obtain ⟨u, huY⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
            obtain ⟨w, hwC, huw⟩ := hall_nbr u (Finset.mem_filter.mp huY).1
            obtain ⟨r⟩ := hK_conn ⟨w, hwC⟩ xK
            let φK : T.induce ((c.support.toFinset : Set V)ᶜ) →g G_plus :=
              { toFun := Sum.inr, map_rel' := fun h => h }
            refine ⟨Sum.inl 1, by simp [A_p], Sum.inr xK, by simp [B_p],
              SimpleGraph.Walk.cons (Exists.intro u ⟨huY, huw⟩) (r.map φK), ?_⟩
            intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h1 | h2
            · exact absurd (Sum.inl.inj h1) (by decide)
            · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2; rcases h2 with ⟨_, _, h⟩; exact (by cases h)
          · obtain ⟨u, huX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
            obtain ⟨w, hwC, huw⟩ := hall_nbr u (Finset.mem_filter.mp huX).1
            obtain ⟨r⟩ := hK_conn ⟨w, hwC⟩ xK
            let φK : T.induce ((c.support.toFinset : Set V)ᶜ) →g G_plus :=
              { toFun := Sum.inr, map_rel' := fun h => h }
            refine ⟨Sum.inl 0, by simp [A_p], Sum.inr xK, by simp [B_p],
              SimpleGraph.Walk.cons (Exists.intro u ⟨huX, huw⟩) (r.map φK), ?_⟩
            intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h1 | h2
            · exact absurd (Sum.inl.inj h1) (by decide)
            · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2; rcases h2 with ⟨_, _, h⟩; exact (by cases h)
        | inr z₀ =>
          have hb_ex : ∃ b₀ ∈ D_xy, b₀ ≠ z₀.1 := by
            by_cases hxz : x = z₀.1
            · exact ⟨y, by simp [D_xy], fun h => hxy_ne (hxz.trans h.symm)⟩
            · exact ⟨x, by simp [D_xy], hxz⟩
          rcases hb_ex with ⟨b₀, hb₀D, hb₀z⟩
          have hvz : v ≠ z₀.1 := fun h => z₀.2 (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c))
          obtain ⟨r⟩ := h3 {z₀.1} (by simp) ⟨v, by simp [hvz]⟩ ⟨b₀, by simp [hb₀z]⟩
          let f : T.induce (({z₀.1} : Finset V)ᶜ : Set V) →g T :=
            (SimpleGraph.Embedding.induce (({z₀.1} : Finset V)ᶜ : Set V)).toHom
          have hr_not_z : z₀.1 ∉ (r.map f).support := by
            intro hm; rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
            rcases hm with ⟨a, _, hax⟩; exact a.2 (by simpa [f] using hax)
          obtain ⟨u, huC, qrev, hq_path, hq_sub, hq_int⟩ :=
            walk_first_hit_pc c.support.toFinset (r.map f).reverse
              ⟨v, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c),
                by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_map, List.mem_map]; exact ⟨⟨v, by simp [hvz]⟩, SimpleGraph.Walk.start_mem_support r, rfl⟩⟩
          let q := qrev.reverse
          have hq_not_z : z₀.1 ∉ q.support := fun hm => by
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm
            have h1 := hq_sub z₀.1 hm; rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
            exact hr_not_z h1
          have hq_tail : ∀ w ∈ q.support.tail, w ∉ c.support.toFinset := by
            intro w hw
            have hcons : q.support = u :: q.support.tail := by cases q <;> simp
            have hnd := hq_path.reverse.support_nodup; rw [hcons, List.nodup_cons] at hnd
            have hwu : w ≠ u := fun h => hnd.1 (h ▸ hw)
            have hw_qrev : w ∈ qrev.support := by
              have : w ∈ q.support := by rw [hcons]; exact List.mem_cons_of_mem _ hw
              rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
            exact hq_int w hw_qrev hwu
          cases hq_eq : q with
          | nil => exact False.elim (Finset.disjoint_left.mp hdisj_c huC hb₀D)
          | @cons _ w₁ _ huw₁ q' =>
            have hq'_K : ∀ w ∈ q'.support, w ∉ c.support.toFinset := fun w hw => hq_tail w (by simp [hq_eq, hw])
            have hlift_q' : ∀ {a₁ b₁ : V} (s : T.Walk a₁ b₁) (hsK : ∀ w ∈ s.support, w ∉ c.support.toFinset),
                ∃ s' : G_plus.Walk (Sum.inr ⟨a₁, hsK a₁ (SimpleGraph.Walk.start_mem_support s)⟩)
                    (Sum.inr ⟨b₁, hsK b₁ (SimpleGraph.Walk.end_mem_support s)⟩),
                  ∀ z' ∈ s'.support, ∃ w ∈ s.support, ∃ hwK, z' = Sum.inr ⟨w, hwK⟩ := by
              intro a₁ b₁ s
              induction s with
              | @nil u₀ => intro hsK; exact ⟨.nil, fun z' hz' => by rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz'; exact ⟨u₀, SimpleGraph.Walk.start_mem_support (SimpleGraph.Walk.nil : T.Walk u₀ u₀), hsK u₀ (SimpleGraph.Walk.start_mem_support _), hz'⟩⟩
              | @cons x₁ y₁ d₁ hxy₁ r₁ ihr₁ =>
                intro hsK
                obtain ⟨s', hs'⟩ := ihr₁ (fun w hw => hsK w (List.mem_cons_of_mem _ hw))
                refine ⟨SimpleGraph.Walk.cons hxy₁ s', fun z' hz' => ?_⟩
                rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz'
                rcases hz' with rfl | hz''
                · exact ⟨x₁, List.mem_cons_self .., _, rfl⟩
                · rcases hs' z' hz'' with ⟨w, hw, hwK, rfl⟩; exact ⟨w, List.mem_cons_of_mem _ hw, hwK, rfl⟩
            obtain ⟨s', hs'⟩ := hlift_q' q' hq'_K
            have hz₀_not_s' : Sum.inr z₀ ∉ s'.support := by
              intro hm; rcases hs' (Sum.inr z₀) hm with ⟨w, hw, _, heq⟩
              have hwz : z₀.1 = w := congrArg Subtype.val (Sum.inr.inj heq)
              exact hq_not_z (by rw [hq_eq, SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ (hwz ▸ hw))
            have hb₀_in_Bp : (Sum.inr ⟨f ⟨b₀, by simp [hb₀z]⟩, hq'_K _ (SimpleGraph.Walk.end_mem_support q')⟩ : Fin 2 ⊕ K_type) ∈ B_p := by
              simp only [D_xy, Finset.mem_insert, Finset.mem_singleton] at hb₀D
              rcases hb₀D with rfl | rfl <;> simp [B_p, f, xK, yK]
            have hcol_u := hcol2 u
            by_cases hcu0 : col u = 0
            · refine ⟨Sum.inl 0, by simp [A_p], _, hb₀_in_Bp,
                SimpleGraph.Walk.cons (Exists.intro u ⟨Finset.mem_filter.mpr ⟨huC, hcu0⟩, huw₁⟩) s', ?_⟩
              intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
              rcases hm with h1 | h2; exact (by cases h1); exact hz₀_not_s' h2
            · refine ⟨Sum.inl 1, by simp [A_p], _, hb₀_in_Bp,
                SimpleGraph.Walk.cons (Exists.intro u ⟨Finset.mem_filter.mpr ⟨huC, by omega⟩, huw₁⟩) s', ?_⟩
              intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
              rcases hm with h1 | h2; exact (by cases h1); exact hz₀_not_s' h2
      obtain ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, ha12, hb12, hp₁, hp₂, hp_disj, hp₁_int, hp₂_int⟩ :=
        two_disjoint_paths_between_sets _ G_plus A_p B_p rfl hAp_card hBp_card hGp_no_cut
      -- Project p₁, p₂ to disjoint T-paths from {x, y} to {uX, uY}
      have hproj : ∀ (i : Fin 2) (b : Fin 2 ⊕ K_type) (p : G_plus.Walk (Sum.inl i) b),
          b ∈ B_p → p.IsPath → (∀ z ∈ p.support, z ≠ Sum.inl i → z ≠ b → z ∉ A_p ∧ z ∉ B_p) →
          ∃ (u : V) (wb : K_type) (P : T.Walk wb.1 u),
            (i = 0 → u ∈ X) ∧ (i = 1 → u ∈ Y) ∧ Sum.inr wb = b ∧ P.IsPath ∧
            (∀ z ∈ P.support, z ≠ u → ∃ hK : z ∉ c.support.toFinset, Sum.inr ⟨z, hK⟩ ∈ p.support) ∧
            (∀ z ∈ P.support, z ≠ wb.1 → z ≠ u → z ∉ c.support) := by
        intro i b p hb hp hp_int
        cases hp_eq : p with
        | nil => simp [B_p] at hb
        | @cons _ z₁ _ hadj1 q =>
          have hz₁_inr : ∃ w₁ : K_type, z₁ = Sum.inr w₁ := by
            cases z₁ with
            | inl j => fin_cases i <;> fin_cases j <;> exact False.elim hadj1
            | inr w₁ => exact ⟨w₁, rfl⟩
          rcases hz₁_inr with ⟨w₁, rfl⟩
          have hu_ex : ∃ u : V, (i = 0 → u ∈ X) ∧ (i = 1 → u ∈ Y) ∧ T.Adj u w₁.1 := by
            fin_cases i
            · rcases hadj1 with ⟨u, huX, huw⟩; exact ⟨u, fun _ => huX, fun h => absurd h (by decide), huw⟩
            · rcases hadj1 with ⟨u, huY, huw⟩; exact ⟨u, fun h => absurd h (by decide), fun _ => huY, huw⟩
          rcases hu_ex with ⟨u, hu0, hu1, huw₁⟩
          have hq_inr : ∀ z ∈ q.support, ∃ w : K_type, z = Sum.inr w := by
            intro z hz
            cases z with
            | inl j =>
              exfalso
              have hnd := hp.support_nodup; rw [hp_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
              have hzj : Sum.inl j ≠ Sum.inl i := fun h => hnd.1 (h ▸ hz)
              have hzb : Sum.inl j ≠ b := fun h => by subst h; simp [B_p] at hb
              exact (hp_int (Sum.inl j) (by rw [hp_eq, SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz) hzj hzb).1
                (by fin_cases j <;> simp [A_p])
            | inr w => exact ⟨w, rfl⟩
          have hproj_q : ∀ {zs ze : Fin 2 ⊕ K_type} (r : G_plus.Walk zs ze),
              (∀ z ∈ r.support, ∃ w : K_type, z = Sum.inr w) →
              ∀ (ws we : K_type), zs = Sum.inr ws → ze = Sum.inr we →
              ∃ R : T.Walk ws.1 we.1,
                (∀ z ∈ R.support, ∃ hK : z ∉ c.support.toFinset, Sum.inr ⟨z, hK⟩ ∈ r.support) ∧
                (r.IsPath → R.IsPath) := by
            intro zs ze r
            induction r with
            | nil =>
              intro _ ws we h1 h2; have heq := Sum.inr.inj (h1.symm.trans h2); subst heq
              exact ⟨.nil, fun z hz => by simp at hz; subst hz; exact ⟨ws.2, by rw [← h1]; simp⟩, fun _ => .nil⟩
            | @cons za zb zc hab' r' ihr' =>
              intro hall ws we h1 h2; subst h1
              obtain ⟨wb, hzb⟩ := hall zb (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support r'))
              subst hzb
              obtain ⟨R', hR'_sub, hR'_path⟩ := ihr' (fun z hz => hall z (List.mem_cons_of_mem _ hz)) wb we rfl h2
              refine ⟨SimpleGraph.Walk.cons hab' R', ?_, ?_⟩
              · intro z hz; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
                rcases hz with rfl | hz'
                · exact ⟨ws.2, List.mem_cons_self ..⟩
                · rcases hR'_sub z hz' with ⟨hK, hm⟩; exact ⟨hK, List.mem_cons_of_mem _ hm⟩
              · intro hpath; have hnd := hpath.support_nodup; rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                refine SimpleGraph.Walk.IsPath.cons (hR'_path (SimpleGraph.Walk.IsPath.mk' hnd.2)) ?_
                intro hm; rcases hR'_sub ws.1 hm with ⟨hK, hmem⟩
                have heq_sub : (⟨ws.1, hK⟩ : K_type) = ws := Subtype.ext rfl
                rw [heq_sub] at hmem; exact hnd.1 hmem
          obtain ⟨wb, hwb⟩ := hq_inr b (SimpleGraph.Walk.end_mem_support q)
          have hq_path : q.IsPath := by
            have hnd := hp.support_nodup; rw [hp_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
            exact SimpleGraph.Walk.IsPath.mk' hnd.2
          obtain ⟨Q, hQ_sub, hQ_path⟩ := hproj_q q hq_inr w₁ wb rfl hwb
          have huC : u ∈ c.support.toFinset := by
            fin_cases i
            · exact (Finset.mem_filter.mp (hu0 rfl)).1
            · exact (Finset.mem_filter.mp (hu1 rfl)).1
          have hP_path : (SimpleGraph.Walk.cons huw₁ Q).IsPath :=
            SimpleGraph.Walk.IsPath.cons (hQ_path hq_path) (fun hm => by rcases hQ_sub u hm with ⟨hK, _⟩; exact hK huC)
          refine ⟨u, wb, (SimpleGraph.Walk.cons huw₁ Q).reverse, hu0, hu1, hwb.symm, hP_path.reverse, ?_, ?_⟩
          · intro z hz hzu
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hQ_sub z (hz.resolve_left hzu) with ⟨hK, hm⟩
            exact ⟨hK, List.mem_cons_of_mem _ hm⟩
          · intro z hz _ hzu
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hQ_sub z (hz.resolve_left hzu) with ⟨hK, _⟩
            exact fun hm => hK (List.mem_toFinset.mpr hm)
      have hex_ord : ∃ (bX bY : Fin 2 ⊕ K_type) (pX : G_plus.Walk (Sum.inl 0) bX) (pY : G_plus.Walk (Sum.inl 1) bY),
          bX ∈ B_p ∧ bY ∈ B_p ∧ bX ≠ bY ∧ pX.IsPath ∧ pY.IsPath ∧
          Disjoint pX.support.toFinset pY.support.toFinset ∧
          (∀ z ∈ pX.support, z ≠ Sum.inl 0 → z ≠ bX → z ∉ A_p ∧ z ∉ B_p) ∧
          (∀ z ∈ pY.support, z ≠ Sum.inl 1 → z ≠ bY → z ∉ A_p ∧ z ∉ B_p) := by
        simp only [A_p, Finset.mem_insert, Finset.mem_singleton] at ha₁ ha₂
        rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl
        · exact absurd rfl ha12
        · exact ⟨b₁, b₂, p₁, p₂, hb₁, hb₂, hb12, hp₁, hp₂, hp_disj, hp₁_int, hp₂_int⟩
        · exact ⟨b₂, b₁, p₂, p₁, hb₂, hb₁, hb12.symm, hp₂, hp₁, hp_disj.symm, hp₂_int, hp₁_int⟩
        · exact absurd rfl ha12
      rcases hex_ord with ⟨bX, bY, pX, pY, hbX, hbY, hbXY, hpX, hpY, hdisjXY, hpX_int, hpY_int⟩
      obtain ⟨uX, wbX, PX, huX0, _, hwbX, hPX, hPX_sub, hPX_int⟩ := hproj 0 bX pX hbX hpX hpX_int
      obtain ⟨uY, wbY, PY, _, huY1, hwbY, hPY, hPY_sub, hPY_int⟩ := hproj 1 bY pY hbY hpY hpY_int
      have huX : uX ∈ X := huX0 rfl
      have huY : uY ∈ Y := huY1 rfl
      have huXY : uX ≠ uY := fun h => Finset.disjoint_left.mp hXY_disj huX (h ▸ huY)
      have hPXY_disj : ∀ z ∈ PX.support, z ∉ PY.support := by
        intro z hz1 hz2
        by_cases hzX : z = uX
        · subst hzX; by_cases hzY : z = uY; exact huXY hzY
          rcases hPY_sub z hz2 hzY with ⟨hK, _⟩; exact hK (Finset.mem_filter.mp huX).1
        · by_cases hzY : z = uY
          · subst hzY; rcases hPX_sub z hz1 hzX with ⟨hK, _⟩; exact hK (Finset.mem_filter.mp huY).1
          · rcases hPX_sub z hz1 hzX with ⟨hK1, hm1⟩
            rcases hPY_sub z hz2 hzY with ⟨hK2, hm2⟩
            have heq : (⟨z, hK1⟩ : K_type) = ⟨z, hK2⟩ := Subtype.ext rfl
            rw [heq] at hm1
            exact Finset.disjoint_left.mp hdisjXY (List.mem_toFinset.mpr hm1) (List.mem_toFinset.mpr hm2)
      have huXC : uX ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp huX).1
      have huYC : uY ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp huY).1
      obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, _, harc_e2, harc_w⟩ :=
        cycle_arcs_edges_subset c hc huXC huYC huXY
      have hpar2 := hcol_walk arc2 harc_e2
      have hcolX : col uX = 0 := (Finset.mem_filter.mp huX).2
      have hcolY : col uY = 1 := (Finset.mem_filter.mp huY).2
      have harc2_odd : Odd arc2.length := ⟨arc2.length / 2, by omega⟩
      have hw_eq : (walkModFourWeight σ arc1 + walkModFourWeight σ arc2) + 2 * (arc2.length : ZMod 4) = 2 := by
        rw [harc_w σ, hw0, (two_mul_nat_mod_four arc2.length).2 harc2_odd, zero_add]
      rw [← hwbX] at hbX; rw [← hwbY] at hbY
      simp only [B_p, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq] at hbX hbY
      rcases hbX with hX1 | hX2 <;> rcases hbY with hY1 | hY2
      · exact hbXY (by rw [← hwbX, ← hwbY, hX1, hY1])
      · have hx1 : wbX.1 = x := congrArg Subtype.val hX1
        have hy1 : wbY.1 = y := congrArg Subtype.val hY2
        subst hx1; subst hy1
        exact hlink_contra uX uY huXC huYC huXY PX PY hPX hPY hPXY_disj hPX_int hPY_int arc1 arc2 harc1 harc2 harc_supp hw_eq
      · have hx1 : wbY.1 = x := congrArg Subtype.val hY1
        have hy1 : wbX.1 = y := congrArg Subtype.val hX2
        subst hx1; subst hy1
        have hw_eq' : (walkModFourWeight σ arc1.reverse + walkModFourWeight σ arc2.reverse) +
            2 * (arc2.reverse.length : ZMod 4) = 2 := by
          simpa [walkModFourWeight_reverse, SimpleGraph.Walk.length_reverse] using hw_eq
        exact hlink_contra uY uX huYC huXC huXY.symm PY PX hPY hPX (fun z h1 h2 => hPXY_disj z h2 h1)
          hPY_int hPX_int arc1.reverse arc2.reverse harc1.reverse harc2.reverse
          (fun z => by simpa [SimpleGraph.Walk.support_reverse] using harc_supp z) hw_eq'
      · exact hbXY (by rw [← hwbX, ← hwbY, hX2, hY2])
    · -- Subcase 2b: w(c) = 2 → G_X and G_Y each have a 1-vertex separator v₁, v₂ ∈ K,
      -- forcing {v₁, v₂} = {x, y}, then 4-path alternating sum gives contradiction!
      have hex_sep_part : ∀ (P : Finset V), P ⊆ c.support.toFinset → 2 ≤ P.card →
          (∀ u₁ ∈ P, ∀ u₂ ∈ P, col u₁ = col u₂) →
          ∃ vP ∉ c.support.toFinset,
            ∀ a ∈ P, ∀ b ∈ D_xy, ∀ q : T.Walk a b,
              (∀ z ∈ q.support.tail, z ∉ c.support.toFinset) → vP ∈ q.support := by
        intro P hPC hP2 hPcol
        let G_P : SimpleGraph V :=
          { Adj := fun a b => T.Adj a b ∧
              ((a ∉ c.support.toFinset ∧ b ∉ c.support.toFinset) ∨
               (a ∈ P ∧ b ∉ c.support.toFinset) ∨
               (b ∈ P ∧ a ∉ c.support.toFinset))
            symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, by tauto⟩⟩
            loopless := ⟨fun z ⟨h1, _⟩ => T.ne_of_adj h1 rfl⟩ }
        have hGP_le : G_P ≤ T := fun _ _ h => h.1
        have hex_cut : ∃ vP : V, ∀ a ∈ P, ∀ b ∈ D_xy, ∀ p : G_P.Walk a b, vP ∈ p.support := by
          by_contra hno_cut; push Not at hno_cut
          have hD_card : 2 ≤ D_xy.card := by rw [Finset.card_pair hxy_ne]
          obtain ⟨u₁, u₂, w₁, w₂, p₁, p₂, hu₁, hu₂, hw₁, hw₂, hu12, hw12, hp₁, hp₂, hp_disj, hp₁_int, hp₂_int⟩ :=
            two_disjoint_paths_between_sets _ G_P P D_xy rfl hP2 hD_card hno_cut
          let φ : G_P →g T := SimpleGraph.Hom.ofLE hGP_le
          have hP_int_C : ∀ {u w : V} (p : G_P.Walk u w),
              (∀ z ∈ p.support, z ≠ u → z ≠ w → z ∉ P ∧ z ∉ D_xy) →
              ∀ z ∈ p.support, z ≠ w → z ≠ u → z ∉ c.support := by
            intro u w p hpint z hz hzw hzu hzC
            have hinc : ∃ t, G_P.Adj z t := by
              have aux : ∀ {a b c₀ : V} (r : G_P.Walk b c₀), G_P.Adj a b → z ∈ r.support → ∃ t, G_P.Adj z t := by
                intro a b c₀ r
                induction r generalizing a with
                | nil => intro hab hr; simp at hr; subst hr; exact ⟨a, hab.symm⟩
                | @cons a₂ b₂ _ hab₂ r₂ ihr₂ =>
                  intro _ hr; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hr
                  rcases hr with rfl | hr₂
                  · exact ⟨b₂, hab₂⟩
                  · exact ihr₂ hab₂ hr₂
              cases p with
              | nil => simp at hz; exact absurd hz hzu
              | @cons _ b₁ _ hab₁ r₁ =>
                rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
                exact aux r₁ hab₁ (hz.resolve_left hzu)
            rcases hinc with ⟨t, hzt⟩
            have hzC' : z ∈ c.support.toFinset := List.mem_toFinset.mpr hzC
            rcases hzt.2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
            · exact h hzC'
            · exact (hpint z hz hzu hzw).1 h
            · exact h hzC'
          have hu₁C : u₁ ∈ c.support := List.mem_toFinset.mp (hPC hu₁)
          have hu₂C : u₂ ∈ c.support := List.mem_toFinset.mp (hPC hu₂)
          obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, _, harc_e2, harc_w⟩ :=
            cycle_arcs_edges_subset c hc hu₁C hu₂C hu12
          have hpar2 := hcol_walk arc2 harc_e2
          have hcol_eq := hPcol u₁ hu₁ u₂ hu₂
          have harc2_ev : Even arc2.length := ⟨arc2.length / 2, by omega⟩
          have hw_eq : (walkModFourWeight σ arc1 + walkModFourWeight σ arc2) + 2 * (arc2.length : ZMod 4) = 2 := by
            rw [harc_w σ, hw2, (two_mul_nat_mod_four arc2.length).1 harc2_ev, add_zero]
          simp only [D_xy, Finset.mem_insert, Finset.mem_singleton] at hw₁ hw₂
          rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl
          · exact hw12 rfl
          · exact hlink_contra u₁ u₂ hu₁C hu₂C hu12 (p₁.map φ).reverse (p₂.map φ).reverse
              (hp₁.map (f := φ) fun _ _ h => h).reverse (hp₂.map (f := φ) fun _ _ h => h).reverse
              (fun z hz1 hz2 => Finset.disjoint_left.mp hp_disj
                (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz1))
                (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz2)))
              (fun z hz => hP_int_C p₁ hp₁_int z (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz))
              (fun z hz => hP_int_C p₂ hp₂_int z (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz))
              arc1 arc2 harc1 harc2 harc_supp hw_eq
          · have hw_eq' : (walkModFourWeight σ arc1.reverse + walkModFourWeight σ arc2.reverse) +
                2 * (arc2.reverse.length : ZMod 4) = 2 := by
              simpa [walkModFourWeight_reverse, SimpleGraph.Walk.length_reverse] using hw_eq
            exact hlink_contra u₂ u₁ hu₂C hu₁C hu12.symm (p₂.map φ).reverse (p₁.map φ).reverse
              (hp₂.map (f := φ) fun _ _ h => h).reverse (hp₁.map (f := φ) fun _ _ h => h).reverse
              (fun z hz1 hz2 => Finset.disjoint_left.mp hp_disj
                (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz2))
                (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz1)))
              (fun z hz => hP_int_C p₂ hp₂_int z (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz))
              (fun z hz => hP_int_C p₁ hp₁_int z (by simpa [φ, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map] using hz))
              arc1.reverse arc2.reverse harc1.reverse harc2.reverse
              (fun z => by simpa [SimpleGraph.Walk.support_reverse] using harc_supp z) hw_eq'
          · exact hw12 rfl
        rcases hex_cut with ⟨vP, hvP⟩
        have hvP_notC : vP ∉ c.support.toFinset := by
          intro hvPC
          obtain ⟨a, haP, havP⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) vP
          obtain ⟨w, hwC, haw⟩ := hall_nbr a (hPC haP)
          obtain ⟨r⟩ := hK_conn ⟨w, hwC⟩ ⟨x, Finset.disjoint_right.mp hdisj_c (by simp [D_xy])⟩
          let φK : T.induce ((c.support.toFinset : Set V)ᶜ) →g G_P :=
            { toFun := Subtype.val, map_rel' := fun {u₁ u₂} h => ⟨h, Or.inl ⟨u₁.2, u₂.2⟩⟩ }
          have hmem := hvP a haP x (by simp [D_xy])
            (SimpleGraph.Walk.cons ⟨haw, Or.inr (Or.inl ⟨haP, hwC⟩)⟩ (r.map φK))
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hmem
          rcases hmem with rfl | h2
          · exact havP rfl
          · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2; rcases h2 with ⟨z, _, rfl⟩; exact z.2 hvPC
        refine ⟨vP, hvP_notC, fun a ha b hb q hq_tail => ?_⟩
        cases hq_eq : q with
        | nil => exact False.elim (Finset.disjoint_left.mp hdisj_c (hPC ha) hb)
        | @cons _ w₁ _ haw₁ q' =>
          have hw₁C : w₁ ∉ c.support.toFinset := hq_tail w₁ (by simp [hq_eq])
          have hq'_C : ∀ z ∈ q'.support, z ∉ c.support.toFinset := fun z hz => hq_tail z (by simp [hq_eq, hz])
          have hlift : ∀ {s t : V} (r : T.Walk s t), (∀ z ∈ r.support, z ∉ c.support.toFinset) →
              ∃ r' : G_P.Walk s t, r'.support = r.support := by
            intro s t r; induction r with
            | nil => intro _; exact ⟨.nil, rfl⟩
            | @cons x₁ y₁ d₁ hxy₁ r₁ ihr₁ =>
              intro hrK; obtain ⟨r₁', hr₁'⟩ := ihr₁ (fun z hz => hrK z (List.mem_cons_of_mem _ hz))
              exact ⟨SimpleGraph.Walk.cons ⟨hxy₁, Or.inl ⟨hrK x₁ (List.mem_cons_self ..),
                hrK y₁ (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support r₁))⟩⟩ r₁', by simp [hr₁']⟩
          obtain ⟨q'P, hq'P⟩ := hlift q' hq'_C
          have hmem := hvP a ha b hb (SimpleGraph.Walk.cons ⟨haw₁, Or.inr (Or.inl ⟨ha, hw₁C⟩)⟩ q'P)
          rw [SimpleGraph.Walk.support_cons, hq'P] at hmem; simpa [hq_eq] using hmem
      obtain ⟨v₁P, hv₁C, hv₁_sep⟩ := hex_sep_part X
        (fun z hz => (Finset.mem_filter.mp hz).1) hX_ge2
        (fun u₁ h1 u₂ h2 => by rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
      obtain ⟨v₂P, hv₂C, hv₂_sep⟩ := hex_sep_part Y
        (fun z hz => (Finset.mem_filter.mp hz).1) hY_ge2
        (fun u₁ h1 u₂ h2 => by rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
      -- Prove D_xy ⊆ {v₁P, v₂P}
      let S_cut : Finset V := {v₁P, v₂P}
      have hD_sub_S : ∀ b₀ ∈ D_xy, b₀ ∈ S_cut := by
        intro b₀ hb₀D
        by_contra hb₀S
        have hv_notS : v ∉ S_cut := by
          simp only [S_cut, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hv₁C (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c)),
                 fun h => hv₂C (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c))⟩
        obtain ⟨r⟩ := h3 S_cut Finset.card_le_two ⟨v, hv_notS⟩ ⟨b₀, hb₀S⟩
        let f : T.induce ((S_cut : Set V)ᶜ) →g T := (SimpleGraph.Embedding.induce ((S_cut : Set V)ᶜ)).toHom
        have hr_notS : ∀ z ∈ (r.map f).support, z ∉ S_cut := by
          intro z hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz; rcases hz with ⟨a, _, rfl⟩; exact a.2
        obtain ⟨u, huC, qrev, hq_path, hq_sub, hq_int⟩ :=
          walk_first_hit_pc c.support.toFinset (r.map f).reverse
            ⟨v, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c),
              by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_map, List.mem_map]; exact ⟨⟨v, hv_notS⟩, SimpleGraph.Walk.start_mem_support r, rfl⟩⟩
        let q := qrev.reverse
        have hq_notS : ∀ z ∈ q.support, z ∉ S_cut := fun z hz => by
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
          have h1 := hq_sub z hz; rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1; exact hr_notS z h1
        have hq_tail : ∀ z ∈ q.support.tail, z ∉ c.support.toFinset := by
          intro z hz
          have hcons : q.support = u :: q.support.tail := by cases q <;> simp
          have hnd := hq_path.reverse.support_nodup; rw [hcons, List.nodup_cons] at hnd
          have hzu : z ≠ u := fun h => hnd.1 (h ▸ hz)
          have hz_qrev : z ∈ qrev.support := by
            have : z ∈ q.support := by rw [hcons]; exact List.mem_cons_of_mem _ hz
            rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
          exact hq_int z hz_qrev hzu
        have hcol_u := hcol2 u
        by_cases hcu0 : col u = 0
        · exact hq_notS v₁P (hv₁_sep u (Finset.mem_filter.mpr ⟨huC, hcu0⟩) b₀ hb₀D q hq_tail) (by simp [S_cut])
        · exact hq_notS v₂P (hv₂_sep u (Finset.mem_filter.mpr ⟨huC, by omega⟩) b₀ hb₀D q hq_tail) (by simp [S_cut])
      have hxS : x ∈ S_cut := hD_sub_S x (by simp [D_xy])
      have hyS : y ∈ S_cut := hD_sub_S y (by simp [D_xy])
      -- Helper: given a color cX ∈ {0, 1} separated by x and cY ≠ cX separated by y, build 4-path contradiction!
      have hfour_paths : ∀ (cX cY : ℕ), cX < 2 → cY < 2 → cX ≠ cY →
          (∀ a ∈ c.support.toFinset, col a = cX → ∀ b ∈ D_xy, ∀ q : T.Walk a b,
            (∀ z ∈ q.support.tail, z ∉ c.support.toFinset) → x ∈ q.support) →
          (∀ a ∈ c.support.toFinset, col a = cY → ∀ b ∈ D_xy, ∀ q : T.Walk a b,
            (∀ z ∈ q.support.tail, z ∉ c.support.toFinset) → y ∈ q.support) →
          False := by
        intro cX cY hcX hcY hcXY hx_sep hy_sep
        -- For any a ∈ C with col a = cX, get simple path L : x → a internally in K avoiding y
        have hex_L : ∀ a ∈ c.support.toFinset, col a = cX →
            ∃ L : T.Walk x a, L.IsPath ∧ y ∉ L.support ∧ (∀ z ∈ L.support, z ≠ a → z ∉ c.support.toFinset) := by
          intro a haC hca
          obtain ⟨w, hwC, haw⟩ := hall_nbr a haC
          obtain ⟨r⟩ := hK_conn ⟨w, hwC⟩ ⟨x, Finset.disjoint_right.mp hdisj_c (by simp [D_xy])⟩
          let φK : T.induce ((c.support.toFinset : Set V)ᶜ) →g T :=
            (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
          let rp := (r.map φK).toPath
          have hrp_notC : ∀ z ∈ rp.1.support, z ∉ c.support.toFinset := by
            intro z hz
            have h1 := SimpleGraph.Walk.support_toPath_subset (r.map φK) hz
            rw [SimpleGraph.Walk.support_map, List.mem_map] at h1; rcases h1 with ⟨u, _, rfl⟩; exact u.2
          have ha_not_rp : a ∉ rp.1.support := fun hm => hrp_notC a hm haC
          let q : T.Walk a x := SimpleGraph.Walk.cons haw rp.1
          have hq_path : q.IsPath := SimpleGraph.Walk.IsPath.cons rp.2 ha_not_rp
          have hy_not_q : y ∉ q.support := by
            intro hyq
            have hy_rp : y ∈ rp.1.support := by
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hyq
              exact hyq.resolve_left (fun h => Finset.disjoint_left.mp hdisj_c haC (by simp [D_xy, h]))
            let qy : T.Walk a y := SimpleGraph.Walk.cons haw (rp.1.takeUntil y hy_rp)
            have hx_in_qy : x ∈ qy.support := hx_sep a haC hca y (by simp [D_xy]) qy (fun z hz => by
              simp only [qy, SimpleGraph.Walk.support_cons, List.tail_cons] at hz
              exact hrp_notC z (SimpleGraph.Walk.support_takeUntil_subset rp.1 hy_rp hz))
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx_in_qy
            have hx_in_take : x ∈ (rp.1.takeUntil y hy_rp).support :=
              hx_in_qy.resolve_left (fun h => Finset.disjoint_left.mp hdisj_c haC (by simp [D_xy, h]))
            have hspec := SimpleGraph.Walk.take_spec rp.1 hy_rp
            have hnd := rp.2.support_nodup
            rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdrop_cons : (rp.1.dropUntil y hy_rp).support = y :: (rp.1.dropUntil y hy_rp).support.tail := by
              cases rp.1.dropUntil y hy_rp <;> simp
            have hx_drop : x ∈ (rp.1.dropUntil y hy_rp).support := SimpleGraph.Walk.end_mem_support _
            rw [hdrop_cons, List.mem_cons] at hx_drop
            exact hnd.2.2 x hx_in_take x (hx_drop.resolve_left hxy_ne) rfl
          refine ⟨q.reverse, hq_path.reverse, fun hm => hy_not_q (by simpa [SimpleGraph.Walk.support_reverse] using hm), ?_⟩
          intro z hz hza
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          exact hrp_notC z (hz.resolve_left hza)
        have hex_R : ∀ b ∈ c.support.toFinset, col b = cY →
            ∃ R : T.Walk b y, R.IsPath ∧ x ∉ R.support ∧ (∀ z ∈ R.support, z ≠ b → z ∉ c.support.toFinset) := by
          intro b hbC hcb
          obtain ⟨w, hwC, hbw⟩ := hall_nbr b hbC
          obtain ⟨r⟩ := hK_conn ⟨w, hwC⟩ ⟨y, Finset.disjoint_right.mp hdisj_c (by simp [D_xy])⟩
          let φK : T.induce ((c.support.toFinset : Set V)ᶜ) →g T :=
            (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
          let rp := (r.map φK).toPath
          have hrp_notC : ∀ z ∈ rp.1.support, z ∉ c.support.toFinset := by
            intro z hz
            have h1 := SimpleGraph.Walk.support_toPath_subset (r.map φK) hz
            rw [SimpleGraph.Walk.support_map, List.mem_map] at h1; rcases h1 with ⟨u, _, rfl⟩; exact u.2
          have hb_not_rp : b ∉ rp.1.support := fun hm => hrp_notC b hm hbC
          let q : T.Walk b y := SimpleGraph.Walk.cons hbw rp.1
          have hq_path : q.IsPath := SimpleGraph.Walk.IsPath.cons rp.2 hb_not_rp
          have hx_not_q : x ∉ q.support := by
            intro hxq
            have hx_rp : x ∈ rp.1.support := by
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hxq
              exact hxq.resolve_left (fun h => Finset.disjoint_left.mp hdisj_c hbC (by simp [D_xy, h]))
            let qx : T.Walk b x := SimpleGraph.Walk.cons hbw (rp.1.takeUntil x hx_rp)
            have hy_in_qx : y ∈ qx.support := hy_sep b hbC hcb x (by simp [D_xy]) qx (fun z hz => by
              simp only [qx, SimpleGraph.Walk.support_cons, List.tail_cons] at hz
              exact hrp_notC z (SimpleGraph.Walk.support_takeUntil_subset rp.1 hx_rp hz))
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy_in_qx
            have hy_in_take : y ∈ (rp.1.takeUntil x hx_rp).support :=
              hy_in_qx.resolve_left (fun h => Finset.disjoint_left.mp hdisj_c hbC (by simp [D_xy, h]))
            have hspec := SimpleGraph.Walk.take_spec rp.1 hx_rp
            have hnd := rp.2.support_nodup
            rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdrop_cons : (rp.1.dropUntil x hx_rp).support = x :: (rp.1.dropUntil x hx_rp).support.tail := by
              cases rp.1.dropUntil x hx_rp <;> simp
            have hy_drop : y ∈ (rp.1.dropUntil x hx_rp).support := SimpleGraph.Walk.end_mem_support _
            rw [hdrop_cons, List.mem_cons] at hy_drop
            exact hnd.2.2 y hy_in_take y (hy_drop.resolve_left hxy_ne.symm) rfl
          refine ⟨q, hq_path, hx_not_q, ?_⟩
          intro z hz hzb
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          exact hrp_notC z (hz.resolve_left hzb)
        -- Any L (x → a) and R (b → y) are automatically vertex-disjoint!
        have hLR_disj : ∀ {a b : V} (haC : a ∈ c.support.toFinset) (hca : col a = cX)
            (hbC : b ∈ c.support.toFinset) (hcb : col b = cY)
            (L : T.Walk x a) (R : T.Walk b y), L.IsPath → R.IsPath →
            y ∉ L.support → x ∉ R.support →
            (∀ z ∈ L.support, z ≠ a → z ∉ c.support.toFinset) →
            (∀ z ∈ R.support, z ≠ b → z ∉ c.support.toFinset) →
            ∀ z ∈ L.support, z ∉ R.support := by
          intro a b haC hca hbC hcb L R hL hR hyL hxR hL_K hR_K z hzL hzR
          have hza : z ≠ a := by
            intro h; subst h
            have hzb : z ≠ b := fun h' => hcXY (hca.symm.trans (h' ▸ hcb))
            exact hR_K z hzR hzb haC
          have hzb : z ≠ b := by
            intro h; subst h
            exact hL_K z hzL hza hbC
          have hzx : z ≠ x := fun h => hxR (h ▸ hzR)
          have hzLr : z ∈ L.reverse.support := by simpa [SimpleGraph.Walk.support_reverse] using hzL
          let q : T.Walk a y := (L.reverse.takeUntil z hzLr).append (R.dropUntil z hzR)
          have hx_in_q : x ∈ q.support := hx_sep a haC hca y (by simp [D_xy]) q (fun w hw => by
            -- Every element of q.support.tail is either in (L.reverse.takeUntil z).support.tail or in (R.dropUntil z).support
            dsimp only [q] at hw
            rw [SimpleGraph.Walk.support_append] at hw
            have hcons1 : (L.reverse.takeUntil z hzLr).support = a :: (L.reverse.takeUntil z hzLr).support.tail := by
              cases L.reverse.takeUntil z hzLr <;> simp
            rw [hcons1, List.cons_append, List.tail_cons, List.mem_append] at hw
            rcases hw with hw1 | hw2
            · have hnd := (hL.reverse.takeUntil hzLr).support_nodup
              rw [hcons1, List.nodup_cons] at hnd
              have hwa' : w ≠ a := fun h => hnd.1 (h ▸ hw1)
              have hwL : w ∈ L.support := by
                have := SimpleGraph.Walk.support_takeUntil_subset L.reverse hzLr (by rw [hcons1]; exact List.mem_cons_of_mem _ hw1)
                rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
              exact hL_K w hwL hwa'
            · have hwR : w ∈ R.support := SimpleGraph.Walk.support_dropUntil_subset R hzR (by
                have hcons2 : (R.dropUntil z hzR).support = z :: (R.dropUntil z hzR).support.tail := by
                  cases R.dropUntil z hzR <;> simp
                rw [hcons2]; exact List.mem_cons_of_mem _ hw2)
              have hwb' : w ≠ b := by
                intro h; subst h
                have hspec := SimpleGraph.Walk.take_spec R hzR
                have hnd := hR.support_nodup
                rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                exact hnd.2.2 b (SimpleGraph.Walk.start_mem_support _) b hw2 rfl
              exact hR_K w hwR hwb')
          dsimp only [q] at hx_in_q
          rw [SimpleGraph.Walk.mem_support_append_iff] at hx_in_q
          rcases hx_in_q with hx1 | hx2
          · have hspec := SimpleGraph.Walk.take_spec L.reverse hzLr
            have hnd := hL.reverse.support_nodup
            rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdrop_cons : (L.reverse.dropUntil z hzLr).support = z :: (L.reverse.dropUntil z hzLr).support.tail := by
              cases L.reverse.dropUntil z hzLr <;> simp
            have hx_drop : x ∈ (L.reverse.dropUntil z hzLr).support := SimpleGraph.Walk.end_mem_support _
            rw [hdrop_cons, List.mem_cons] at hx_drop
            exact hnd.2.2 x hx1 x (hx_drop.resolve_left hzx.symm) rfl
          · exact hxR (SimpleGraph.Walk.support_dropUntil_subset R hzR hx2)
        -- Helper: build a simple (x, y)-path in H from L (x → a), arc A (a → b) on C, R (b → y)
        have hglue : ∀ {a b : V} (haC : a ∈ c.support.toFinset) (hca : col a = cX)
            (hbC : b ∈ c.support.toFinset) (hcb : col b = cY)
            (L : T.Walk x a) (A : T.Walk a b) (R : T.Walk b y),
            L.IsPath → A.IsPath → R.IsPath →
            y ∉ L.support → x ∉ R.support →
            (∀ z ∈ L.support, z ≠ a → z ∉ c.support.toFinset) →
            (∀ z ∈ R.support, z ≠ b → z ∉ c.support.toFinset) →
            (∀ z ∈ A.support, z ∈ c.support.toFinset) →
            walkModFourWeight σ L + walkModFourWeight σ A + walkModFourWeight σ R = walkModFourWeight σ p₀ := by
          intro a b haC hca hbC hcb L A R hL hA hR hyL hxR hL_K hR_K hAC
          have hdisj := hLR_disj haC hca hbC hcb L R hL hR hyL hxR hL_K hR_K
          have h1 : (L.append A).IsPath := by
            apply isPath_append_of_disjoint_pc L A hL hA
            intro z hzL hzA; by_contra hza; exact hL_K z hzL hza (hAC z hzA)
          have h2 : ((L.append A).append R).IsPath := by
            apply isPath_append_of_disjoint_pc (L.append A) R h1 hR
            intro z hz1 hzR; rw [SimpleGraph.Walk.mem_support_append_iff] at hz1
            rcases hz1 with hzL | hzA
            · exact False.elim (hdisj z hzL hzR)
            · by_contra hzb; exact hR_K z hzR hzb (hAC z hzA)
          let PT := (L.append A).append R
          have hnot_xy : s(x, y) ∉ PT.edges := by
            intro hm; dsimp only [PT] at hm
            rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_append, List.mem_append] at hm
            rcases hm with (h | h) | h
            · exact hyL (SimpleGraph.Walk.snd_mem_support_of_mem_edges L h)
            · exact Finset.disjoint_left.mp hdisj_c (hAC x (SimpleGraph.Walk.fst_mem_support_of_mem_edges A h)) (by simp [D_xy])
            · exact hxR (SimpleGraph.Walk.fst_mem_support_of_mem_edges R h)
          let PH : (T.deleteEdges {s(x, y)}).Walk x y := PT.transfer _ (fun e he => by
            rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨PT.edges_subset_edgeSet he, fun h => hnot_xy (Set.mem_singleton_iff.mp h ▸ he)⟩)
          have hPH_path : PH.IsPath := SimpleGraph.Walk.IsPath.mk' (by
            rw [SimpleGraph.Walk.support_transfer]; exact h2.support_nodup)
          have htr : walkModFourWeight σ PH = walkModFourWeight σ PT := by
            simp [PH, walkModFourWeight, SimpleGraph.Walk.edges_transfer]
          have hres := hconst PH hPH_path
          rw [htr] at hres
          simpa [PT, walkModFourWeight_append] using hres
        -- Unfold 3 edges of c (length ≥ 4) to get 4 consecutive vertices v - u₁ - u₂ - u₃ - ... - v!
        have hge4 : 4 ≤ c.length := even_cycle_length_ge_four c hc hev
        cases hc_eq : c with
        | nil => simp [hc_eq] at hge4
        | @cons _ u₁ _ h01 p₁ =>
          cases p₁ with
          | nil => simp [hc_eq] at hge4
          | @cons _ u₂ _ h12 p₂ =>
            cases p₂ with
            | nil => simp [hc_eq] at hge4
            | @cons _ u₃ _ h23 r =>
              have hnd := hc.support_nodup
              rw [hc_eq, SimpleGraph.Walk.support_cons, List.tail_cons,
                SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons] at hnd
              have hr_path : r.IsPath := by
                rw [List.nodup_cons, List.nodup_cons] at hnd
                exact SimpleGraph.Walk.IsPath.mk' hnd.2.2
              have hvC : v ∈ c.support.toFinset := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c)
              have hu1C : u₁ ∈ c.support.toFinset := List.mem_toFinset.mpr (by rw [hc_eq]; simp)
              have hu2C : u₂ ∈ c.support.toFinset := List.mem_toFinset.mpr (by rw [hc_eq]; simp)
              have hu3C : u₃ ∈ c.support.toFinset := List.mem_toFinset.mpr (by rw [hc_eq]; simp)
              have hrC : ∀ z ∈ r.support, z ∈ c.support.toFinset := fun z hz =>
                List.mem_toFinset.mpr (by rw [hc_eq]; simp [hz])
              have he01 : s(v, u₁) ∈ c.edges := by rw [hc_eq]; simp
              have he12 : s(u₁, u₂) ∈ c.edges := by rw [hc_eq]; simp
              have he23 : s(u₂, u₃) ∈ c.edges := by rw [hc_eq]; simp
              have hp01 := hcol_walk (SimpleGraph.Walk.cons h01 .nil) (fun e he => by simp at he; rwa [he])
              have hp12 := hcol_walk (SimpleGraph.Walk.cons h12 .nil) (fun e he => by simp at he; rwa [he])
              have hp23 := hcol_walk (SimpleGraph.Walk.cons h23 .nil) (fun e he => by simp at he; rwa [he])
              simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp01 hp12 hp23
              have hcv := hcol2 v; have hcu1 := hcol2 u₁; have hcu2 := hcol2 u₂; have hcu3 := hcol2 u₃
              have hw_c_split : modFourWeight σ s(v, u₁) + modFourWeight σ s(u₁, u₂) +
                  modFourWeight σ s(u₂, u₃) + walkModFourWeight σ r = 2 := by
                have h1 := hw2; rw [hc_eq] at h1
                simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons] at h1
                linear_combination h1
              have hr_odd : Odd r.length := by
                rw [hc_eq] at hev; simp only [SimpleGraph.Walk.length_cons] at hev
                rcases hev with ⟨k, hk⟩; exact ⟨k - 2, by omega⟩
              let A₁ : T.Walk v u₁ := SimpleGraph.Walk.cons h01 .nil
              let A₂ : T.Walk u₁ u₂ := SimpleGraph.Walk.cons h12 .nil
              let A₃ : T.Walk u₂ u₃ := SimpleGraph.Walk.cons h23 .nil
              have hA₁ : A₁.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [A₁, T.ne_of_adj h01])
              have hA₂ : A₂.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [A₂, T.ne_of_adj h12])
              have hA₃ : A₃.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [A₃, T.ne_of_adj h23])
              have hA₁C : ∀ z ∈ A₁.support, z ∈ c.support.toFinset := fun z hz => by
                simp [A₁] at hz; rcases hz with rfl | rfl; exact hvC; exact hu1C
              have hA₂C : ∀ z ∈ A₂.support, z ∈ c.support.toFinset := fun z hz => by
                simp [A₂] at hz; rcases hz with rfl | rfl; exact hu1C; exact hu2C
              have hA₃C : ∀ z ∈ A₃.support, z ∈ c.support.toFinset := fun z hz => by
                simp [A₃] at hz; rcases hz with rfl | rfl; exact hu2C; exact hu3C
              by_cases hcvX : col v = cX
              · have hcu2X : col u₂ = cX := by omega
                have hcu1Y : col u₁ = cY := by omega
                have hcu3Y : col u₃ = cY := by omega
                obtain ⟨L₁, hL₁, hyL₁, hL₁K⟩ := hex_L v hvC hcvX
                obtain ⟨L₂, hL₂, hyL₂, hL₂K⟩ := hex_L u₂ hu2C hcu2X
                obtain ⟨R₁, hR₁, hxR₁, hR₁K⟩ := hex_R u₁ hu1C hcu1Y
                obtain ⟨R₂, hR₂, hxR₂, hR₂K⟩ := hex_R u₃ hu3C hcu3Y
                have hP1 := hglue hvC hcvX hu1C hcu1Y L₁ A₁ R₁ hL₁ hA₁ hR₁ hyL₁ hxR₁ hL₁K hR₁K hA₁C
                have hP2 := hglue hu2C hcu2X hu1C hcu1Y L₂ A₂.reverse R₁ hL₂ hA₂.reverse hR₁ hyL₂ hxR₁ hL₂K hR₁K
                  (fun z hz => hA₂C z (by simpa [SimpleGraph.Walk.support_reverse] using hz))
                have hP3 := hglue hu2C hcu2X hu3C hcu3Y L₂ A₃ R₂ hL₂ hA₃ hR₂ hyL₂ hxR₂ hL₂K hR₂K hA₃C
                have hP4 := hglue hvC hcvX hu3C hcu3Y L₁ r.reverse R₂ hL₁ hr_path.reverse hR₂ hyL₁ hxR₂ hL₁K hR₂K
                  (fun z hz => hrC z (by simpa [SimpleGraph.Walk.support_reverse] using hz))
                rw [walkModFourWeight_reverse] at hP2 hP4
                have h2A2 : 2 * walkModFourWeight σ A₂ = 2 := by
                  rw [two_mul_walkModFourWeight]; simp [A₂]
                have h2r : 2 * walkModFourWeight σ r = 2 := by
                  rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four r.length).2 hr_odd]
                have h4z : (4 : ZMod 4) = 0 := rfl
                have hcontra : (2 : ZMod 4) = 0 := by
                  have hwA1 : walkModFourWeight σ A₁ = modFourWeight σ s(v, u₁) := by simp [A₁, walkModFourWeight]
                  have hwA2 : walkModFourWeight σ A₂ = modFourWeight σ s(u₁, u₂) := by simp [A₂, walkModFourWeight]
                  have hwA3 : walkModFourWeight σ A₃ = modFourWeight σ s(u₂, u₃) := by simp [A₃, walkModFourWeight]
                  linear_combination -hw_c_split + hwA1 + hwA2 + hwA3 + hP1 + hP3 - hP2 - hP4 + h2A2 + h2r - h4z
                exact absurd hcontra (by decide)
              · have hcvY : col v = cY := by omega
                have hcu2Y : col u₂ = cY := by omega
                have hcu1X : col u₁ = cX := by omega
                have hcu3X : col u₃ = cX := by omega
                obtain ⟨L₁, hL₁, hyL₁, hL₁K⟩ := hex_L u₁ hu1C hcu1X
                obtain ⟨L₂, hL₂, hyL₂, hL₂K⟩ := hex_L u₃ hu3C hcu3X
                obtain ⟨R₁, hR₁, hxR₁, hR₁K⟩ := hex_R v hvC hcvY
                obtain ⟨R₂, hR₂, hxR₂, hR₂K⟩ := hex_R u₂ hu2C hcu2Y
                have hP1 := hglue hu1C hcu1X hvC hcvY L₁ A₁.reverse R₁ hL₁ hA₁.reverse hR₁ hyL₁ hxR₁ hL₁K hR₁K
                  (fun z hz => hA₁C z (by simpa [SimpleGraph.Walk.support_reverse] using hz))
                have hP2 := hglue hu1C hcu1X hu2C hcu2Y L₁ A₂ R₂ hL₁ hA₂ hR₂ hyL₁ hxR₂ hL₁K hR₂K hA₂C
                have hP3 := hglue hu3C hcu3X hu2C hcu2Y L₂ A₃.reverse R₂ hL₂ hA₃.reverse hR₂ hyL₂ hxR₂ hL₂K hR₂K
                  (fun z hz => hA₃C z (by simpa [SimpleGraph.Walk.support_reverse] using hz))
                have hP4 := hglue hu3C hcu3X hvC hcvY L₂ r R₁ hL₂ hr_path hR₁ hyL₂ hxR₁ hL₂K hR₁K hrC
                rw [walkModFourWeight_reverse] at hP1 hP3
                have h2A2 : 2 * walkModFourWeight σ A₂ = 2 := by
                  rw [two_mul_walkModFourWeight]; simp [A₂]
                have h2r : 2 * walkModFourWeight σ r = 2 := by
                  rw [two_mul_walkModFourWeight, (two_mul_nat_mod_four r.length).2 hr_odd]
                have h4z : (4 : ZMod 4) = 0 := rfl
                have hcontra : (2 : ZMod 4) = 0 := by
                  have hwA1 : walkModFourWeight σ A₁ = modFourWeight σ s(v, u₁) := by simp [A₁, walkModFourWeight]
                  have hwA2 : walkModFourWeight σ A₂ = modFourWeight σ s(u₁, u₂) := by simp [A₂, walkModFourWeight]
                  have hwA3 : walkModFourWeight σ A₃ = modFourWeight σ s(u₂, u₃) := by simp [A₃, walkModFourWeight]
                  linear_combination -hw_c_split + hwA1 + hwA2 + hwA3 + hP1 + hP3 - hP2 - hP4 + h2A2 + h2r - h4z
                exact absurd hcontra (by decide)
      simp only [S_cut, Finset.mem_insert, Finset.mem_singleton] at hxS hyS
      rcases hxS with rfl | rfl <;> rcases hyS with h | h
      · exact hxy_ne h.symm
      · subst h
        exact hfour_paths 0 1 (by decide) (by decide) (by decide)
          (fun a ha hca => hv₁_sep a (Finset.mem_filter.mpr ⟨ha, hca⟩))
          (fun a ha hca => hv₂_sep a (Finset.mem_filter.mpr ⟨ha, hca⟩))
      · subst h
        exact hfour_paths 1 0 (by decide) (by decide) (by decide)
          (fun a ha hca => hv₂_sep a (Finset.mem_filter.mpr ⟨ha, hca⟩))
          (fun a ha hca => hv₁_sep a (Finset.mem_filter.mpr ⟨ha, hca⟩))
      · exact hxy_ne h.symm

end SignedGraphs
