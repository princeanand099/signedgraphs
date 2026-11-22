import SignedGraphs.Basic
import SignedGraphs.GraphTools
import SignedGraphs.ParityCore
import SignedGraphs.MaximalEvenCycle

/-!
# Cycle-Pair Obstructions (Lemma 3.4)

Formalization of Lemma 3.4(1), (2), and (3) in a 3-connected NOC signed graph.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 3.4(1)**: In a 3-connected NOC signed graph, no even cycle and odd cycle can be
vertex-disjoint. -/
theorem cycle_pair_obstructions_disjoint_even_odd (S : SignedGraph V)
    (hconn : S.graph.Preconnected) (h3 : ∀ A : Finset V, A.card ≤ 2 →
      (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {v₁ v₂ : V} (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hdisj : Disjoint c₁.support.toFinset c₂.support.toFinset) :
    False := by
  classical
  have hD_conn := cycle_induce_preconnected c₂ hc₂
  obtain ⟨v, c, hc, hev, hdisj_c, hH_conn, hchord_ev, hchord_struct⟩ :=
    maximal_even_cycle_lemma S.graph h3 c₂.support.toFinset v₂
      (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))
      hD_conn c₁ hc₁ heven hdisj
  have hdisjC : ∀ x ∈ c.support, x ∉ c₂.support := fun x hx h2 =>
    Finset.disjoint_left.mp hdisj_c (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr h2)
  have hC_card_ge4 : 4 ≤ c.support.toFinset.card := by rw [cycle_support_card c hc]; exact even_cycle_length_ge_four c hc hev
  have hC₂_card_ge3 : 3 ≤ c₂.support.toFinset.card := by
    rw [cycle_support_card c₂ hc₂]; exact hc₂.three_le_length
  -- Case A: G[V(C)] ≅ K₄
  rcases hchord_struct with ⟨hc4, hK4⟩ | hle1_chord
  · -- By 3-connectivity, there are 2 disjoint paths from V(C) to V(C₂)
    have hno_cut : ∀ z : V, ∃ a ∈ c.support.toFinset, ∃ b ∈ c₂.support.toFinset,
        ∃ p : S.graph.Walk a b, z ∉ p.support := by
      intro z
      obtain ⟨a, ha, haz⟩ := Finset.exists_mem_ne (by omega : 1 < c.support.toFinset.card) z
      obtain ⟨b, hb, hbz⟩ := Finset.exists_mem_ne (by omega : 1 < c₂.support.toFinset.card) z
      have hconn1 := h3 {z} (by simp)
      obtain ⟨p⟩ := hconn1 ⟨a, by simp [haz]⟩ ⟨b, by simp [hbz]⟩
      let f : S.graph.induce (({z} : Finset V)ᶜ : Set V) →g S.graph :=
        (SimpleGraph.Embedding.induce (({z} : Finset V)ᶜ : Set V)).toHom
      refine ⟨a, ha, b, hb, p.map f, fun hz => ?_⟩
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
      rcases hz with ⟨x, _, hxz⟩
      exact x.2 (by simp [hxz])
    obtain ⟨u₁, u₂, w₁, w₂, P₁, P₂, hu₁, hu₂, hw₁, hw₂, hu12, hw12, hP₁, hP₂, hPdisj, hP₁_int, hP₂_int⟩ :=
      two_disjoint_paths_between_sets _ S.graph c.support.toFinset c₂.support.toFinset rfl
        (by omega) (by omega) hno_cut
    obtain ⟨p₁, p₂, hp₁, hp₂, hp_len, hp_supp, hw_eq⟩ :=
      k4_pair_paths S hnoc c hc hc4 hK4 (List.mem_toFinset.mp hu₁) (List.mem_toFinset.mp hu₂) hu12
    exact even_odd_cycle_linkage_disjoint S c c₂ hc hc₂ hev hodd hdisjC
      (List.mem_toFinset.mp hu₁) (List.mem_toFinset.mp hu₂) hu12
      (List.mem_toFinset.mp hw₁) (List.mem_toFinset.mp hw₂) hw12
      P₁ P₂ hP₁ hP₂
      (fun x hx1 hx2 => Finset.disjoint_left.mp hPdisj (List.mem_toFinset.mpr hx1) (List.mem_toFinset.mpr hx2))
      (fun x hx h1 h2 => ⟨fun hm => (hP₁_int x hx h1 h2).1 (List.mem_toFinset.mpr hm),
        fun hm => (hP₁_int x hx h1 h2).2 (List.mem_toFinset.mpr hm)⟩)
      (fun x hx h1 h2 => ⟨fun hm => (hP₂_int x hx h1 h2).1 (List.mem_toFinset.mpr hm),
        fun hm => (hP₂_int x hx h1 h2).2 (List.mem_toFinset.mpr hm)⟩)
      p₁ p₂ hp₁ hp₂ (by omega) hp_supp hw_eq hnoc
  · -- Case B: C has at most one chord (of even distance)
    obtain ⟨col, hcol2, hcol_walk⟩ := even_cycle_bipartition c hc hev
    let X : Finset V := c.support.toFinset.filter fun u => col u = 0
    let Y : Finset V := c.support.toFinset.filter fun u => col u = 1
    have ⟨hX_ge2, hY_ge2⟩ := even_cycle_part_card_ge_two c hc hev col hcol2 hcol_walk
    have hXY_disj : Disjoint X Y := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [X, Y, Finset.mem_filter] at hz1 hz2; omega
    have hXY_union : X ∪ Y = c.support.toFinset := by
      ext z; simp only [X, Y, Finset.mem_union, Finset.mem_filter]
      have := hcol2 z; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; omega
    -- Subcase B1 vs B2: w(C) = 0 or w(C) = 2
    rcases walkModFourWeight_even_of_even_length S.sign c hev with hw0 | hw2
    · -- Subcase B1: w(C) = 0
      -- Build auxiliary graph G_plus on Fin 2 ⊕ {z : V // z ∉ c.support.toFinset}
      let H_type := {z : V // z ∈ ((c.support.toFinset : Set V)ᶜ)}
      let G_plus : SimpleGraph (Fin 2 ⊕ H_type) :=
        { Adj := fun a b => match a, b with
            | Sum.inr u, Sum.inr w => S.graph.Adj u.1 w.1
            | Sum.inl 0, Sum.inr w => ∃ x ∈ X, S.graph.Adj x w.1
            | Sum.inr w, Sum.inl 0 => ∃ x ∈ X, S.graph.Adj x w.1
            | Sum.inl 1, Sum.inr w => ∃ y ∈ Y, S.graph.Adj y w.1
            | Sum.inr w, Sum.inl 1 => ∃ y ∈ Y, S.graph.Adj y w.1
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
            | inr u => exact S.graph.ne_of_adj h rfl⟩ }
      let A_p : Finset (Fin 2 ⊕ H_type) := {Sum.inl 0, Sum.inl 1}
      let B_p : Finset (Fin 2 ⊕ H_type) := Finset.univ.filter fun z =>
        match z with
        | Sum.inr w => w.1 ∈ c₂.support.toFinset
        | Sum.inl _ => False
      have hAp_card : 2 ≤ A_p.card := by
        rw [Finset.card_pair]; intro h; exact absurd (Sum.inl.inj h) (by decide)
      have hBp_card : 2 ≤ B_p.card := by
        have hinj : c₂.support.toFinset.card ≤ B_p.card := by
          let f : V → Fin 2 ⊕ H_type := fun z =>
            if hz : z ∈ c₂.support.toFinset then
              Sum.inr ⟨z, Finset.disjoint_right.mp hdisj_c hz⟩
            else Sum.inl 0
          calc c₂.support.toFinset.card
              = (c₂.support.toFinset.image f).card := by
                rw [Finset.card_image_of_injOn]
                intro a ha b hb hab
                simp only [f, dif_pos ha, dif_pos hb, Sum.inr.injEq, Subtype.mk.injEq] at hab
                exact hab
            _ ≤ B_p.card := Finset.card_le_card (by
                intro z hz
                rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
                simp [B_p, f, dif_pos ha, ha])
        omega
      -- Let's prove |X| = |Y| cleanly first!
      have hX_eq_Y : X.card = Y.card := by
        -- Apply directly to c
        have htail_toFinset : c.support.tail.toFinset = c.support.toFinset := by
          ext u
          rw [List.mem_toFinset, List.mem_toFinset]
          have hcons : c.support = v :: c.support.tail := by cases c <;> simp
          rw [hcons, List.mem_cons]
          constructor
          · exact Or.inr
          · rintro (rfl | hu)
            · cases hc_eq : c with
              | nil => exact absurd hc_eq hc.ne_nil
              | cons _ r => simp [SimpleGraph.Walk.end_mem_support r]
            · exact hu
        have hX_len : X.card = (c.support.tail.filter (fun u => col u = 0)).length := by
          have hnd := hc.support_nodup.filter (fun u => decide (col u = 0))
          rw [← List.toFinset_card_of_nodup hnd]
          congr 1; ext u; simp [X, ← htail_toFinset]
        have hY_len : Y.card = (c.support.tail.filter (fun u => col u = 1)).length := by
          have hnd := hc.support_nodup.filter (fun u => decide (col u = 1))
          rw [← List.toFinset_card_of_nodup hnd]
          congr 1; ext u; simp [Y, ← htail_toFinset]
        -- Directly invoke hwalk_bal on c
        have hwalk_bal : ∀ {a b : V} (p : S.graph.Walk a b),
            (∀ e ∈ p.edges, e ∈ c.edges) →
            (Even p.length → (p.support.tail.filter (fun u => col u = 0)).length =
              (p.support.tail.filter (fun u => col u = 1)).length) ∧
            (Odd p.length →
              (col b = 0 → (p.support.tail.filter (fun u => col u = 0)).length =
                (p.support.tail.filter (fun u => col u = 1)).length + 1) ∧
              (col b = 1 → (p.support.tail.filter (fun u => col u = 1)).length =
                (p.support.tail.filter (fun u => col u = 0)).length + 1)) := by
          intro a b p
          induction p with
          | nil =>
            intro _
            refine ⟨fun _ => by simp, fun h => by rcases h with ⟨k, hk⟩; simp at hk⟩
          | @cons x y z hxy r ihr =>
            intro hr
            have hxy_e : s(x, y) ∈ c.edges := hr s(x, y) (by simp)
            have hr_e : ∀ e ∈ r.edges, e ∈ c.edges := fun e he => hr e (List.mem_cons_of_mem _ he)
            have ih := ihr hr_e
            have hpar_xy := hcol_walk (SimpleGraph.Walk.cons hxy .nil) (fun e he => by simp at he; rwa [he])
            have hpar_r := hcol_walk r hr_e
            simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hpar_xy
            have hcx := hcol2 x; have hcy := hcol2 y; have hcz := hcol2 z
            have hsupp_tail : (SimpleGraph.Walk.cons hxy r).support.tail = y :: r.support.tail := by
              cases r <;> simp
            rw [hsupp_tail]
            constructor
            · intro hev_cons
              have hodd_r : Odd r.length := by
                rcases hev_cons with ⟨k, hk⟩; simp only [SimpleGraph.Walk.length_cons] at hk
                exact ⟨k - 1, by omega⟩
              have hcy_ne_cz : col y ≠ col z := by rcases hodd_r with ⟨m, hm⟩; omega
              by_cases hcy0 : col y = 0
              · have hcz1 : col z = 1 := by omega
                have h1 := (ih.2 hodd_r).2 hcz1
                simp [List.filter_cons, hcy0]; omega
              · have hcy1 : col y = 1 := by omega
                have hcz0 : col z = 0 := by omega
                have h1 := (ih.2 hodd_r).1 hcz0
                simp [List.filter_cons, hcy1]; omega
            · intro hodd_cons
              have hev_r : Even r.length := by
                rcases hodd_cons with ⟨k, hk⟩; simp only [SimpleGraph.Walk.length_cons] at hk
                exact ⟨k, by omega⟩
              have hcy_eq_cz : col y = col z := by rcases hev_r with ⟨m, hm⟩; omega
              have h1 := ih.1 hev_r
              constructor
              · intro hcz0; have hcy0 : col y = 0 := by omega
                simp [List.filter_cons, hcy0]; omega
              · intro hcz1; have hcy1 : col y = 1 := by omega
                simp [List.filter_cons, hcy1]; omega
        rw [hX_len, hY_len]
        exact (hwalk_bal c (fun _ h => h)).1 hev
      -- Now prove both X and Y have a neighbor in H_type!
      have hpart_has_nbr : ∀ (P Q : Finset V), P ∪ Q = c.support.toFinset → Disjoint P Q →
          P.card = Q.card → 2 ≤ P.card →
          ∃ x ∈ P, ∃ w : H_type, S.graph.Adj x w.1 := by
        intro P Q hPQ hPQ_disj hPeq hP2
        by_contra hno
        push Not at hno
        -- Every x ∈ P has NO neighbor outside C, so by min_deg ≥ 3 it must be incident to a chord!
        have hall_chord : ∀ x ∈ P, ∃ y ∈ c.support, S.graph.Adj x y ∧ s(x, y) ∉ c.edges := by
          intro x hx
          by_contra hnc
          push Not at hnc
          have hxC : x ∈ c.support := List.mem_toFinset.mp (hPQ ▸ Finset.mem_union_left Q hx)
          obtain ⟨w, hwC, hxw⟩ := exists_neighbor_outside_even h3 c hc hev hxC hnc
          exact hno x hx ⟨w, hwC⟩ hxw
        by_cases hP_eq2 : P.card = 2
        · -- Q.card = 2 as well, so Q separates P from c₂!
          have hQ_le2 : Q.card ≤ 2 := by omega
          obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
          have hx₀Q : x₀ ∉ Q := Finset.disjoint_left.mp hPQ_disj hx₀
          have hv₂Q : v₂ ∉ Q := fun h => Finset.disjoint_right.mp hdisj_c
            (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))
            (hPQ ▸ Finset.mem_union_right P h)
          obtain ⟨r⟩ := h3 Q hQ_le2 ⟨x₀, hx₀Q⟩ ⟨v₂, hv₂Q⟩
          let f : S.graph.induce ((Q : Set V)ᶜ) →g S.graph := (SimpleGraph.Embedding.induce ((Q : Set V)ᶜ)).toHom
          have hv₂P : v₂ ∉ P := fun h => Finset.disjoint_right.mp hdisj_c
            (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))
            (hPQ ▸ Finset.mem_union_left Q h)
          obtain ⟨a, haP, b, hbP, hab, _, hbp⟩ := walk_exits_finset_pc P (r.map f) hx₀ hv₂P
          have hbQ : b ∉ Q := by
            rw [SimpleGraph.Walk.support_map, List.mem_map] at hbp
            rcases hbp with ⟨z, _, rfl⟩; exact z.2
          have hbC : b ∉ c.support.toFinset := by
            rw [← hPQ, Finset.mem_union]; push Not; exact ⟨hbP, hbQ⟩
          exact hno a haP ⟨b, hbC⟩ hab
        · -- P.card ≥ 3: pick 3 distinct vertices x₁, x₂, x₃ ∈ P; each is incident to a chord of C,
          -- impossible since C has at most 1 chord (which has only 2 endpoints)!
          have hP3 : 3 ≤ P.card := by omega
          obtain ⟨x₁, hx₁⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
          obtain ⟨x₂, hx₂, hx₂₁⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) x₁
          have hcard_er : 1 ≤ ((P.erase x₁).erase x₂).card := by
            have hx₂' : x₂ ∈ P.erase x₁ := Finset.mem_erase.mpr ⟨hx₂₁, hx₂⟩
            rw [Finset.card_erase_of_mem hx₂', Finset.card_erase_of_mem hx₁]; omega
          obtain ⟨x₃, hx₃_er⟩ := Finset.card_pos.mp hcard_er
          have hx₃ : x₃ ∈ P := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx₃_er)
          have hx₃₂ : x₃ ≠ x₂ := (Finset.mem_erase.mp hx₃_er).1
          have hx₃₁ : x₃ ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx₃_er)).1
          obtain ⟨y₁, hy₁C, hxy₁, hch₁⟩ := hall_chord x₁ hx₁
          obtain ⟨y₂, hy₂C, hxy₂, hch₂⟩ := hall_chord x₂ hx₂
          obtain ⟨y₃, hy₃C, hxy₃, hch₃⟩ := hall_chord x₃ hx₃
          have hx₁C : x₁ ∈ c.support := List.mem_toFinset.mp (hPQ ▸ Finset.mem_union_left Q hx₁)
          have hx₂C : x₂ ∈ c.support := List.mem_toFinset.mp (hPQ ▸ Finset.mem_union_left Q hx₂)
          have hx₃C : x₃ ∈ c.support := List.mem_toFinset.mp (hPQ ▸ Finset.mem_union_left Q hx₃)
          have he12 : s(x₁, y₁) = s(x₂, y₂) := hle1_chord _ _
            ⟨x₁, y₁, rfl, hx₁C, hy₁C, hxy₁, hch₁⟩ ⟨x₂, y₂, rfl, hx₂C, hy₂C, hxy₂, hch₂⟩
          have he13 : s(x₁, y₁) = s(x₃, y₃) := hle1_chord _ _
            ⟨x₁, y₁, rfl, hx₁C, hy₁C, hxy₁, hch₁⟩ ⟨x₃, y₃, rfl, hx₃C, hy₃C, hxy₃, hch₃⟩
          rcases Sym2.eq_iff.mp he12 with ⟨h, _⟩ | ⟨_, h⟩
          · exact hx₂₁ h.symm
          · rcases Sym2.eq_iff.mp he13 with ⟨h', _⟩ | ⟨_, h'⟩
            · exact hx₃₁ h'.symm
            · exact hx₃₂ (h'.symm.trans h)
      have hX_nbr : ∃ x ∈ X, ∃ w : H_type, S.graph.Adj x w.1 :=
        hpart_has_nbr X Y hXY_union hXY_disj hX_eq_Y hX_ge2
      have hY_nbr : ∃ y ∈ Y, ∃ w : H_type, S.graph.Adj y w.1 :=
        hpart_has_nbr Y X (by rw [Finset.union_comm]; exact hXY_union) hXY_disj.symm hX_eq_Y.symm hY_ge2
      -- Prove G_plus has NO 1-vertex separator between A_p and B_p!
      have hGp_no_cut : ∀ z : Fin 2 ⊕ H_type, ∃ a ∈ A_p, ∃ b ∈ B_p,
          ∃ p : G_plus.Walk a b, z ∉ p.support := by
        intro z
        cases z with
        | inl i =>
          fin_cases i
          · -- z = Sum.inl 0: start from Sum.inl 1 via hY_nbr and walk inside H to v₂!
            rcases hY_nbr with ⟨y, hyY, w, hyw⟩
            let v₂H : H_type := ⟨v₂, Finset.disjoint_right.mp hdisj_c
              (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))⟩
            obtain ⟨r⟩ := hH_conn w v₂H
            let φH : S.graph.induce ((c.support.toFinset : Set V)ᶜ) →g G_plus :=
              { toFun := Sum.inr, map_rel' := fun h => h }
            have hadj1 : G_plus.Adj (Sum.inl 1) (Sum.inr w) := ⟨y, hyY, hyw⟩
            refine ⟨Sum.inl 1, by simp [A_p], Sum.inr v₂H,
              by simp [B_p, v₂H, SimpleGraph.Walk.start_mem_support c₂],
              SimpleGraph.Walk.cons hadj1 (r.map φH), ?_⟩
            intro hm
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h1 | h2
            · exact absurd (Sum.inl.inj h1) (by decide)
            · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2
              rcases h2 with ⟨_, _, h⟩; exact Sum.noConfusion h
          · -- z = Sum.inl 1: start from Sum.inl 0 via hX_nbr and walk inside H to v₂!
            rcases hX_nbr with ⟨x, hxX, w, hxw⟩
            let v₂H : H_type := ⟨v₂, Finset.disjoint_right.mp hdisj_c
              (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))⟩
            obtain ⟨r⟩ := hH_conn w v₂H
            let φH : S.graph.induce ((c.support.toFinset : Set V)ᶜ) →g G_plus :=
              { toFun := Sum.inr, map_rel' := fun h => h }
            have hadj0 : G_plus.Adj (Sum.inl 0) (Sum.inr w) := ⟨x, hxX, hxw⟩
            refine ⟨Sum.inl 0, by simp [A_p], Sum.inr v₂H,
              by simp [B_p, v₂H, SimpleGraph.Walk.start_mem_support c₂],
              SimpleGraph.Walk.cons hadj0 (r.map φH), ?_⟩
            intro hm
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h1 | h2
            · exact absurd (Sum.inl.inj h1) (by decide)
            · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2
              rcases h2 with ⟨_, _, h⟩; exact Sum.noConfusion h
        | inr z₀ =>
          -- z = Sum.inr z₀: by 3-connectivity, G - {z₀} has a walk from v ∈ C to b ∈ C₂ \ {z₀}
          obtain ⟨b₀, hb₀C₂, hb₀z⟩ := Finset.exists_mem_ne (by omega : 1 < c₂.support.toFinset.card) z₀.1
          have hvz : v ≠ z₀.1 := fun h => z₀.2 (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c))
          obtain ⟨r⟩ := h3 {z₀.1} (by simp) ⟨v, by simp [hvz]⟩ ⟨b₀, by simp [hb₀z]⟩
          let f : S.graph.induce (({z₀.1} : Finset V)ᶜ : Set V) →g S.graph :=
            (SimpleGraph.Embedding.induce (({z₀.1} : Finset V)ᶜ : Set V)).toHom
          have hr_not_z : z₀.1 ∉ (r.map f).support := by
            intro hm; rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
            rcases hm with ⟨x, _, hxz⟩; exact x.2 (by simp [hxz])
          -- Take last hit of C along r.map f (first hit along reverse)
          obtain ⟨u, huC, qrev, hq_path, hq_sub, hq_int⟩ :=
            walk_first_hit_pc c.support.toFinset (r.map f).reverse
              ⟨v, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c),
                by simp [SimpleGraph.Walk.support_reverse]⟩
          let q := qrev.reverse
          have hq_not_z : z₀.1 ∉ q.support := fun hm => by
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm
            have h1 := hq_sub z₀.1 hm
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
            exact hr_not_z h1
          have hq_tail_H : ∀ w ∈ q.support.tail, w ∉ c.support.toFinset := by
            intro w hw
            have hcons : q.support = u :: q.support.tail := by cases q <;> simp
            have hnd : q.support.Nodup := hq_path.reverse.support_nodup
            rw [hcons, List.nodup_cons] at hnd
            have hwu : w ≠ u := fun h => hnd.1 (h ▸ hw)
            have hw_qrev : w ∈ qrev.support := by
              have : w ∈ q.support := by rw [hcons]; exact List.mem_cons_of_mem _ hw
              rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
            exact hq_int w hw_qrev hwu
          cases hq_eq : q with
          | nil => exact False.elim (Finset.disjoint_left.mp hdisj_c huC hb₀C₂)
          | @cons _ w₁ _ huw₁ q' =>
            have hw₁_H : w₁ ∉ c.support.toFinset := hq_tail_H w₁ (by simp [hq_eq])
            have hq'_H : ∀ w ∈ q'.support, w ∉ c.support.toFinset := fun w hw =>
              hq_tail_H w (by simp [hq_eq, hw])
            -- Lift q' to G_plus via Sum.inr
            have hlift_q' : ∀ {a₁ b₁ : V} (s : S.graph.Walk a₁ b₁)
                (hsH : ∀ w ∈ s.support, w ∉ c.support.toFinset),
                ∃ s' : G_plus.Walk (Sum.inr ⟨a₁, hsH a₁ (SimpleGraph.Walk.start_mem_support s)⟩)
                    (Sum.inr ⟨b₁, hsH b₁ (SimpleGraph.Walk.end_mem_support s)⟩),
                  ∀ z' ∈ s'.support, ∃ w ∈ s.support, ∃ hwH, z' = Sum.inr ⟨w, hwH⟩ := by
              intro a₁ b₁ s
              induction s with
              | nil =>
                intro hsH
                exact ⟨.nil, fun z' hz' => by
                  simp at hz'; subst hz'
                  exact ⟨a₁, SimpleGraph.Walk.start_mem_support _, _, rfl⟩⟩
              | @cons x₁ y₁ d₁ hxy₁ r₁ ihr₁ =>
                intro hsH
                have hr₁H : ∀ w ∈ r₁.support, w ∉ c.support.toFinset := fun w hw =>
                  hsH w (List.mem_cons_of_mem _ hw)
                obtain ⟨s', hs'⟩ := ihr₁ hr₁H
                refine ⟨SimpleGraph.Walk.cons hxy₁ s', fun z' hz' => ?_⟩
                rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz'
                rcases hz' with rfl | hz''
                · exact ⟨x₁, List.mem_cons_self .., _, rfl⟩
                · rcases hs' z' hz'' with ⟨w, hw, hwH, rfl⟩
                  exact ⟨w, List.mem_cons_of_mem _ hw, hwH, rfl⟩
            obtain ⟨s', hs'⟩ := hlift_q' q' hq'_H
            have hz₀_not_s' : Sum.inr z₀ ∉ s'.support := by
              intro hm
              rcases hs' (Sum.inr z₀) hm with ⟨w, hw, _, heq⟩
              have hwz : z₀.1 = w := congrArg Subtype.val (Sum.inr.inj heq)
              exact hq_not_z (by rw [hq_eq, SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ (hwz ▸ hw))
            have hcol_u := hcol2 u
            by_cases hcu0 : col u = 0
            · have huX : u ∈ X := Finset.mem_filter.mpr ⟨huC, hcu0⟩
              refine ⟨Sum.inl 0, by simp [A_p], Sum.inr ⟨b₀, hq'_H b₀ (SimpleGraph.Walk.end_mem_support q')⟩,
                by simp [B_p, hb₀C₂], SimpleGraph.Walk.cons ⟨u, huX, huw₁⟩ s', ?_⟩
              intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
              rcases hm with h1 | h2
              · exact Sum.noConfusion h1
              · exact hz₀_not_s' h2
            · have huY : u ∈ Y := Finset.mem_filter.mpr ⟨huC, by omega⟩
              refine ⟨Sum.inl 1, by simp [A_p], Sum.inr ⟨b₀, hq'_H b₀ (SimpleGraph.Walk.end_mem_support q')⟩,
                by simp [B_p, hb₀C₂], SimpleGraph.Walk.cons ⟨u, huY, huw₁⟩ s', ?_⟩
              intro hm; rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
              rcases hm with h1 | h2
              · exact Sum.noConfusion h1
              · exact hz₀_not_s' h2
      -- Apply Menger (k = 2) on G_plus between A_p and B_p!
      obtain ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, ha12, hb12, hp₁, hp₂, hp_disj, hp₁_int, hp₂_int⟩ :=
        two_disjoint_paths_between_sets _ G_plus A_p B_p rfl hAp_card hBp_card hGp_no_cut
      -- Match a₁, a₂ to {Sum.inl 0, Sum.inl 1}
      have hex_ord : ∃ (bX bY : Fin 2 ⊕ H_type)
          (pX : G_plus.Walk (Sum.inl 0) bX) (pY : G_plus.Walk (Sum.inl 1) bY),
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
      -- Helper to project a G_plus path starting at Sum.inl i and ending in B_p to a S.graph path!
      have hproj : ∀ (i : Fin 2) (b : Fin 2 ⊕ H_type) (p : G_plus.Walk (Sum.inl i) b),
          b ∈ B_p → p.IsPath → (∀ z ∈ p.support, z ≠ Sum.inl i → z ≠ b → z ∉ A_p ∧ z ∉ B_p) →
          ∃ (u w : V) (P : S.graph.Walk u w),
            (i = 0 → u ∈ X) ∧ (i = 1 → u ∈ Y) ∧ w ∈ c₂.support ∧ Sum.inr ⟨w, Finset.disjoint_right.mp hdisj_c (List.mem_toFinset.mpr (by assumption))⟩ = b ∧
            P.IsPath ∧
            (∀ z ∈ P.support, z ≠ u → ∃ hH : z ∉ c.support.toFinset, Sum.inr ⟨z, hH⟩ ∈ p.support) ∧
            (∀ z ∈ P.support, z ≠ u → z ≠ w → z ∉ c.support ∧ z ∉ c₂.support) := by
        intro i b p hb hp hp_int
        cases hp_eq : p with
        | nil => simp [B_p] at hb
        | @cons _ z₁ _ hadj1 q =>
          have hz₁_inr : ∃ w₁ : H_type, z₁ = Sum.inr w₁ := by
            cases z₁ with
            | inl j => fin_cases i <;> fin_cases j <;> exact False.elim hadj1
            | inr w₁ => exact ⟨w₁, rfl⟩
          rcases hz₁_inr with ⟨w₁, rfl⟩
          have hu_ex : ∃ u : V, (i = 0 → u ∈ X) ∧ (i = 1 → u ∈ Y) ∧ S.graph.Adj u w₁.1 := by
            fin_cases i
            · rcases hadj1 with ⟨x, hxX, hxw⟩
              exact ⟨x, fun _ => hxX, fun h => absurd h (by decide), hxw⟩
            · rcases hadj1 with ⟨y, hyY, hyw⟩
              exact ⟨y, fun h => absurd h (by decide), fun _ => hyY, hyw⟩
          rcases hu_ex with ⟨u, hu0, hu1, huw₁⟩
          -- All vertices of q are Sum.inr _ because none of them is in A_p!
          have hq_inr : ∀ z ∈ q.support, ∃ w : H_type, z = Sum.inr w := by
            intro z hz
            cases z with
            | inl j =>
              exfalso
              have hnd := hp.support_nodup
              rw [hp_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
              have hzj : Sum.inl j ≠ Sum.inl i := fun h => hnd.1 (h ▸ hz)
              have hzb : Sum.inl j ≠ b := by
                intro h; subst h; simp [B_p] at hb
              have hjA : Sum.inl j ∈ A_p := by fin_cases j <;> simp [A_p]
              exact (hp_int (Sum.inl j) (by rw [hp_eq]; exact List.mem_cons_of_mem _ hz) hzj hzb).1 hjA
            | inr w => exact ⟨w, rfl⟩
          -- Project q to S.graph
          have hproj_q : ∀ {z_s z_e : Fin 2 ⊕ H_type} (r : G_plus.Walk z_s z_e),
              (∀ z ∈ r.support, ∃ w : H_type, z = Sum.inr w) →
              ∀ (ws we : H_type), z_s = Sum.inr ws → z_e = Sum.inr we →
              ∃ R : S.graph.Walk ws.1 we.1,
                R.support.map (fun x => x) = R.support ∧
                (∀ x ∈ R.support, ∃ hH : x ∉ c.support.toFinset, Sum.inr ⟨x, hH⟩ ∈ r.support) ∧
                (r.IsPath → R.IsPath) := by
            intro z_s z_e r
            induction r with
            | nil =>
              intro _ ws we h1 h2
              have heq : ws = we := Sum.inr.inj (h1.symm.trans h2)
              subst heq
              exact ⟨.nil, rfl, fun x hx => by
                simp at hx; subst hx; exact ⟨ws.2, by rw [← h1]; simp⟩, fun _ => SimpleGraph.Walk.IsPath.nil⟩
            | @cons z_a z_b z_c hab' r' ihr' =>
              intro hall ws we h1 h2
              subst h1
              obtain ⟨wb, hzb⟩ := hall z_b (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support r'))
              subst hzb
              have hr'_all : ∀ z ∈ r'.support, ∃ w : H_type, z = Sum.inr w := fun z hz =>
                hall z (List.mem_cons_of_mem _ hz)
              obtain ⟨R', _, hR'_sub, hR'_path⟩ := ihr' hr'_all wb we rfl h2
              refine ⟨SimpleGraph.Walk.cons hab' R', rfl, ?_, ?_⟩
              · intro x hx
                rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
                rcases hx with rfl | hx'
                · exact ⟨ws.2, List.mem_cons_self ..⟩
                · rcases hR'_sub x hx' with ⟨hH, hm⟩
                  exact ⟨hH, List.mem_cons_of_mem _ hm⟩
              · intro hpath
                have hnd := hpath.support_nodup
                rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                refine SimpleGraph.Walk.IsPath.cons (hR'_path (SimpleGraph.Walk.IsPath.mk' hnd.2)) ?_
                intro hm
                rcases hR'_sub ws.1 hm with ⟨hH, hmem⟩
                have heq_sub : (⟨ws.1, hH⟩ : H_type) = ws := Subtype.ext rfl
                rw [heq_sub] at hmem
                exact hnd.1 hmem
          obtain ⟨wb, hwb⟩ := hq_inr b (SimpleGraph.Walk.end_mem_support q)
          have hq_path : q.IsPath := by
            have hnd := hp.support_nodup
            rw [hp_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
            exact SimpleGraph.Walk.IsPath.mk' hnd.2
          obtain ⟨Q, _, hQ_sub, hQ_path⟩ := hproj_q q hq_inr w₁ wb rfl hwb
          have hwbC₂ : wb.1 ∈ c₂.support := by
            rw [hwb] at hb; simp [B_p] at hb; exact List.mem_toFinset.mp hb
          have huC : u ∈ c.support.toFinset := by
            fin_cases i
            · exact (Finset.mem_filter.mp (hu0 rfl)).1
            · exact (Finset.mem_filter.mp (hu1 rfl)).1
          have hP_path : (SimpleGraph.Walk.cons huw₁ Q).IsPath := by
            refine SimpleGraph.Walk.IsPath.cons (hQ_path hq_path) ?_
            intro hm
            rcases hQ_sub u hm with ⟨hH, _⟩
            exact hH huC
          refine ⟨u, wb.1, SimpleGraph.Walk.cons huw₁ Q, hu0, hu1, hwbC₂, hwb.symm, hP_path, ?_, ?_⟩
          · intro z hz hzu
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hQ_sub z (hz.resolve_left hzu) with ⟨hH, hm⟩
            exact ⟨hH, by rw [hp_eq]; exact List.mem_cons_of_mem _ hm⟩
          · intro z hz hzu hzw
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hQ_sub z (hz.resolve_left hzu) with ⟨hH, hm⟩
            refine ⟨fun h => hH (List.mem_toFinset.mpr h), fun h => ?_⟩
            have hz_ne_b : (Sum.inr ⟨z, hH⟩ : Fin 2 ⊕ H_type) ≠ b := by
              rw [hwb]; intro h'; exact hzw (congrArg Subtype.val (Sum.inr.inj h'))
            have hz_in_B : (Sum.inr ⟨z, hH⟩ : Fin 2 ⊕ H_type) ∈ B_p := by
              simp [B_p, List.mem_toFinset.mpr h]
            exact (hp_int (Sum.inr ⟨z, hH⟩) (by rw [hp_eq]; exact List.mem_cons_of_mem _ hm)
              (fun h' => Sum.noConfusion h') hz_ne_b).2 hz_in_B
      obtain ⟨uX, wX, PX, huX0, _, hwXC₂, hwbX, hPX, hPX_sub, hPX_int⟩ :=
        hproj 0 bX pX hbX hpX hpX_int
      obtain ⟨uY, wY, PY, _, huY1, hwYC₂, hwbY, hPY, hPY_sub, hPY_int⟩ :=
        hproj 1 bY pY hbY hpY hpY_int
      have huX : uX ∈ X := huX0 rfl
      have huY : uY ∈ Y := huY1 rfl
      have huXY : uX ≠ uY := fun h => Finset.disjoint_left.mp hXY_disj huX (h ▸ huY)
      have hwXY : wX ≠ wY := by
        intro h; apply hbXY; rw [← hwbX, ← hwbY]; congr 1; exact Subtype.ext h
      have hPXY_disj : ∀ z ∈ PX.support, z ∉ PY.support := by
        intro z hz1 hz2
        by_cases hzX : z = uX
        · subst hzX
          by_cases hzY : z = uY
          · exact huXY hzY
          · rcases hPY_sub z hz2 hzY with ⟨hH, _⟩
            exact hH (Finset.mem_filter.mp huX).1
        · by_cases hzY : z = uY
          · subst hzY
            rcases hPX_sub z hz1 hzX with ⟨hH, _⟩
            exact hH (Finset.mem_filter.mp huY).1
          · rcases hPX_sub z hz1 hzX with ⟨hH1, hm1⟩
            rcases hPY_sub z hz2 hzY with ⟨hH2, hm2⟩
            have heq : (⟨z, hH1⟩ : H_type) = ⟨z, hH2⟩ := Subtype.ext rfl
            rw [heq] at hm1
            exact Finset.disjoint_left.mp hdisjXY (List.mem_toFinset.mpr hm1) (List.mem_toFinset.mpr hm2)
      have huXC : uX ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp huX).1
      have huYC : uY ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp huY).1
      obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, harc_e1, harc_e2, harc_w⟩ :=
        cycle_arcs_edges_subset c hc huXC huYC huXY
      have hpar2 := hcol_walk arc2 harc_e2
      have hcolX : col uX = 0 := (Finset.mem_filter.mp huX).2
      have hcolY : col uY = 1 := (Finset.mem_filter.mp huY).2
      have harc2_odd : Odd arc2.length := ⟨arc2.length / 2, by omega⟩
      have hw_eq : (walkModFourWeight S.sign arc1 + walkModFourWeight S.sign arc2) +
          2 * (arc2.length : ZMod 4) = 2 := by
        rw [harc_w S.sign, hw0, (two_mul_nat_mod_four arc2.length).2 harc2_odd, zero_add]
      exact even_odd_cycle_linkage_disjoint S c c₂ hc hc₂ hev hodd hdisjC
        huXC huYC huXY hwXC₂ hwYC₂ hwXY PX PY hPX hPY hPXY_disj hPX_int hPY_int
        arc1 arc2 harc1 harc2 harc_len harc_supp hw_eq hnoc
    · -- Subcase B2: w(C) = 2
      -- First, C is chordless (since every chord has even distance, forbidden when w(C) = 2)
      have hchordless : ∀ x ∈ c.support, ∀ y ∈ c.support, S.graph.Adj x y → s(x, y) ∈ c.edges := by
        intro x hx y hy hxy
        by_contra hch
        have hne : x ≠ y := S.graph.ne_of_adj hxy
        obtain ⟨arc1, arc2, harc1, harc2, harc_len, _, _, harc_e1, harc_e2, harc_w⟩ :=
          cycle_arcs_edges_subset c hc hx hy hne
        have hev_a := hchord_ev x y hx hy hne hxy hch arc1 arc2 harc1 harc2 harc_len harc_e1 harc_e2
        exact no_even_distance_chord_of_weight_two S hnoc c hc hev hw2 hx hy hne hxy hch
          arc1 arc2 harc1 harc2 harc_len (harc_w S.sign) hev_a.2
      -- Every vertex of C has a neighbor outside C!
      have hall_nbr : ∀ x ∈ c.support.toFinset, ∃ w ∉ c.support.toFinset, S.graph.Adj x w := fun x hx =>
        exists_neighbor_outside_even h3 c hc hev (List.mem_toFinset.mp hx)
          (fun y hy hxy => hchordless x (List.mem_toFinset.mp hx) y hy hxy)
      -- Helper: for any part P ∈ {X, Y}, P has a 1-vertex separator v_P ∉ C from c₂ in G_P
      have hex_sep_part : ∀ (P : Finset V), P ⊆ c.support.toFinset → 2 ≤ P.card →
          (∀ u₁ ∈ P, ∀ u₂ ∈ P, col u₁ = col u₂) →
          ∃ vP ∉ c.support.toFinset,
            ∀ a ∈ P, ∀ b ∈ c₂.support.toFinset, ∀ q : S.graph.Walk a b,
              (∀ z ∈ q.support.tail, z ∉ c.support.toFinset) → vP ∈ q.support := by
        intro P hPC hP2 hPcol
        let G_P : SimpleGraph V :=
          { Adj := fun a b => S.graph.Adj a b ∧
              ((a ∉ c.support.toFinset ∧ b ∉ c.support.toFinset) ∨
               (a ∈ P ∧ b ∉ c.support.toFinset) ∨
               (b ∈ P ∧ a ∉ c.support.toFinset))
            symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, by tauto⟩⟩
            loopless := ⟨fun x ⟨h1, _⟩ => S.graph.ne_of_adj h1 rfl⟩ }
        have hGP_le : G_P ≤ S.graph := fun _ _ h => h.1
        -- G_P MUST have a 1-vertex separator between P and c₂ (else Menger gives 2 disjoint paths → contradiction!)
        have hex_cut : ∃ vP : V, ∀ a ∈ P, ∀ b ∈ c₂.support.toFinset, ∀ p : G_P.Walk a b, vP ∈ p.support := by
          by_contra hno_cut
          push Not at hno_cut
          obtain ⟨u₁, u₂, w₁, w₂, p₁, p₂, hu₁, hu₂, hw₁, hw₂, hu12, hw12, hp₁, hp₂, hp_disj, hp₁_int, hp₂_int⟩ :=
            two_disjoint_paths_between_sets _ G_P P c₂.support.toFinset rfl hP2 (by omega) hno_cut
          let φ : G_P →g S.graph := SimpleGraph.Hom.ofLE hGP_le
          have hP_int_C : ∀ {u w : V} (p : G_P.Walk u w),
              (∀ z ∈ p.support, z ≠ u → z ≠ w → z ∉ P ∧ z ∉ c₂.support.toFinset) →
              ∀ z ∈ p.support, z ≠ u → z ≠ w → z ∉ c.support ∧ z ∉ c₂.support := by
            intro u w p hpint z hz hzu hzw
            refine ⟨?_, fun hm => (hpint z hz hzu hzw).2 (List.mem_toFinset.mpr hm)⟩
            intro hzC
            -- Since z ∈ p.support and z ≠ u, z is incident to some edge of p in G_P
            have hinc : ∃ y, G_P.Adj z y := by
              cases p with
              | nil => simp at hz; exact absurd hz hzu
              | @cons a₁ b₁ _ hab₁ r₁ =>
                rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
                rcases hz with rfl | hzr₁
                · exact absurd rfl hzu
                · clear hzu
                  induction r₁ generalizing a₁ with
                  | nil =>
                    simp at hzr₁; subst hzr₁; exact ⟨a₁, hab₁.symm⟩
                  | @cons a₂ b₂ _ hab₂ r₂ ihr₂ =>
                    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hzr₁
                    rcases hzr₁ with rfl | hzr₂
                    · exact ⟨b₂, hab₂⟩
                    · exact ihr₂ hab₂ hzr₂
            rcases hinc with ⟨y, hzy⟩
            have hz_not_P : z ∉ P := (hpint z hz hzu hzw).1
            have hzC' : z ∈ c.support.toFinset := List.mem_toFinset.mpr hzC
            rcases hzy.2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
            · exact h hzC'
            · exact hz_not_P h
            · exact h hzC'
          have hu₁C : u₁ ∈ c.support := List.mem_toFinset.mp (hPC hu₁)
          have hu₂C : u₂ ∈ c.support := List.mem_toFinset.mp (hPC hu₂)
          obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, _, harc_e2, harc_w⟩ :=
            cycle_arcs_edges_subset c hc hu₁C hu₂C hu12
          have hpar2 := hcol_walk arc2 harc_e2
          have hcol_eq := hPcol u₁ hu₁ u₂ hu₂
          have harc2_ev : Even arc2.length := ⟨arc2.length / 2, by omega⟩
          have hw_eq : (walkModFourWeight S.sign arc1 + walkModFourWeight S.sign arc2) +
              2 * (arc2.length : ZMod 4) = 2 := by
            rw [harc_w S.sign, hw2, (two_mul_nat_mod_four arc2.length).1 harc2_ev, add_zero]
          exact even_odd_cycle_linkage_disjoint S c c₂ hc hc₂ hev hodd hdisjC
            hu₁C hu₂C hu12 (List.mem_toFinset.mp hw₁) (List.mem_toFinset.mp hw₂) hw12
            (p₁.map φ) (p₂.map φ)
            (hp₁.map (f := φ) fun _ _ h => h) (hp₂.map (f := φ) fun _ _ h => h)
            (fun x hx1 hx2 => Finset.disjoint_left.mp hp_disj
              (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_map] using hx1))
              (List.mem_toFinset.mpr (by simpa [φ, SimpleGraph.Walk.support_map] using hx2)))
            (fun x hx => hP_int_C p₁ hp₁_int x (by simpa [φ, SimpleGraph.Walk.support_map] using hx))
            (fun x hx => hP_int_C p₂ hp₂_int x (by simpa [φ, SimpleGraph.Walk.support_map] using hx))
            arc1 arc2 harc1 harc2 harc_len harc_supp hw_eq hnoc
        rcases hex_cut with ⟨vP, hvP⟩
        have hvP_notC : vP ∉ c.support.toFinset := by
          intro hvPC
          obtain ⟨a, haP, havP⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) vP
          obtain ⟨w, hwC, haw⟩ := hall_nbr a (hPC haP)
          let v₂H : {z : V // z ∈ ((c.support.toFinset : Set V)ᶜ)} :=
            ⟨v₂, Finset.disjoint_right.mp hdisj_c (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))⟩
          obtain ⟨r⟩ := hH_conn ⟨w, hwC⟩ v₂H
          let φH : S.graph.induce ((c.support.toFinset : Set V)ᶜ) →g G_P :=
            { toFun := Subtype.val, map_rel' := fun {x y} h => ⟨h, Or.inl ⟨x.2, y.2⟩⟩ }
          have hadj_aw : G_P.Adj a w := ⟨haw, Or.inr (Or.inl ⟨haP, hwC⟩)⟩
          have hmem := hvP a haP v₂ (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c₂))
            (SimpleGraph.Walk.cons hadj_aw (r.map φH))
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hmem
          rcases hmem with rfl | h2
          · exact havP rfl
          · rw [SimpleGraph.Walk.support_map, List.mem_map] at h2
            rcases h2 with ⟨z, _, rfl⟩; exact z.2 hvPC
        refine ⟨vP, hvP_notC, fun a ha b hb q hq_tail => ?_⟩
        -- Lift q to G_P
        cases hq_eq : q with
        | nil => exact False.elim (Finset.disjoint_left.mp hdisj_c (hPC ha) hb)
        | @cons _ w₁ _ haw₁ q' =>
          have hw₁C : w₁ ∉ c.support.toFinset := hq_tail w₁ (by simp [hq_eq])
          have hq'_C : ∀ z ∈ q'.support, z ∉ c.support.toFinset := fun z hz => hq_tail z (by simp [hq_eq, hz])
          have hlift : ∀ {x y : V} (r : S.graph.Walk x y), (∀ z ∈ r.support, z ∉ c.support.toFinset) →
              ∃ r' : G_P.Walk x y, r'.support = r.support := by
            intro x y r
            induction r with
            | nil => intro _; exact ⟨.nil, rfl⟩
            | @cons x₁ y₁ d₁ hxy₁ r₁ ihr₁ =>
              intro hrH
              obtain ⟨r₁', hr₁'⟩ := ihr₁ (fun z hz => hrH z (List.mem_cons_of_mem _ hz))
              exact ⟨SimpleGraph.Walk.cons ⟨hxy₁, Or.inl ⟨hrH x₁ (List.mem_cons_self ..),
                hrH y₁ (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support r₁))⟩⟩ r₁',
                by simp [hr₁']⟩
          obtain ⟨q'P, hq'P⟩ := hlift q' hq'_C
          have hmem := hvP a ha b hb (SimpleGraph.Walk.cons ⟨haw₁, Or.inr (Or.inl ⟨ha, hw₁C⟩)⟩ q'P)
          rw [SimpleGraph.Walk.support_cons, hq'P] at hmem
          simpa [hq_eq] using hmem
      obtain ⟨v₁P, hv₁C, hv₁_sep⟩ := hex_sep_part X
        (fun z hz => (Finset.mem_filter.mp hz).1) hX_ge2
        (fun u₁ h1 u₂ h2 => by rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
      obtain ⟨v₂P, hv₂C, hv₂_sep⟩ := hex_sep_part Y
        (fun z hz => (Finset.mem_filter.mp hz).1) hY_ge2
        (fun u₁ h1 u₂ h2 => by rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
      -- Now {v₁P, v₂P} has card ≤ 2 and separates C from C₂ \ {v₁P, v₂P}!
      let S_cut : Finset V := {v₁P, v₂P}
      have hScard : S_cut.card ≤ 2 := Finset.card_le_two
      have hC₂_diff : (c₂.support.toFinset \ S_cut).Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.card_sdiff_add_card_inter c₂.support.toFinset S_cut
        have hinter_le : (c₂.support.toFinset ∩ S_cut).card ≤ 2 :=
          (Finset.card_le_card Finset.inter_subset_right).trans hScard
        omega
      rcases hC₂_diff with ⟨b₀, hb₀⟩
      rw [Finset.mem_sdiff] at hb₀
      have hv_notS : v ∉ S_cut := by
        simp only [S_cut, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hv₁C (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c)),
               fun h => hv₂C (h ▸ List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c))⟩
      obtain ⟨r⟩ := h3 S_cut hScard ⟨v, hv_notS⟩ ⟨b₀, hb₀.2⟩
      let f : S.graph.induce ((S_cut : Set V)ᶜ) →g S.graph := (SimpleGraph.Embedding.induce ((S_cut : Set V)ᶜ)).toHom
      have hr_notS : ∀ z ∈ (r.map f).support, z ∉ S_cut := by
        intro z hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
        rcases hz with ⟨x, _, rfl⟩; exact x.2
      obtain ⟨u, huC, qrev, hq_path, hq_sub, hq_int⟩ :=
        walk_first_hit_pc c.support.toFinset (r.map f).reverse
          ⟨v, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support c),
            by simp [SimpleGraph.Walk.support_reverse]⟩
      let q := qrev.reverse
      have hq_notS : ∀ z ∈ q.support, z ∉ S_cut := fun z hz => by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have h1 := hq_sub z hz
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
        exact hr_notS z h1
      have hq_tail : ∀ z ∈ q.support.tail, z ∉ c.support.toFinset := by
        intro z hz
        have hcons : q.support = u :: q.support.tail := by cases q <;> simp
        have hnd := hq_path.reverse.support_nodup
        rw [hcons, List.nodup_cons] at hnd
        have hzu : z ≠ u := fun h => hnd.1 (h ▸ hz)
        have hz_qrev : z ∈ qrev.support := by
          have : z ∈ q.support := by rw [hcons]; exact List.mem_cons_of_mem _ hz
          rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
        exact hq_int z hz_qrev hzu
      have hcol_u := hcol2 u
      by_cases hcu0 : col u = 0
      · exact hq_notS v₁P (hv₁_sep u (Finset.mem_filter.mpr ⟨huC, hcu0⟩) b₀ hb₀.1 q hq_tail) (by simp [S_cut])
      · exact hq_notS v₂P (hv₂_sep u (Finset.mem_filter.mpr ⟨huC, by omega⟩) b₀ hb₀.1 q hq_tail) (by simp [S_cut])

/-- **Lemma 3.4(2)**: In a 3-connected NOC signed graph, an even cycle and an odd cycle
cannot intersect in exactly one vertex. -/
theorem cycle_pair_obstructions_one_vertex_even_odd (S : SignedGraph V)
    (hconn : S.graph.Preconnected) (h3 : ∀ A : Finset V, A.card ≤ 2 →
      (S.graph.induce (Aᶜ : Set V)).Preconnected)
    (hnoc : IsNOC S)
    {u v₁ v₂ : V} (c₁ : S.graph.Walk v₁ v₁) (c₂ : S.graph.Walk v₂ v₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (heven : Even c₁.length) (hodd : Odd c₂.length)
    (hinter : c₁.support.toFinset ∩ c₂.support.toFinset = {u}) :
    False := by
  classical
  have hu_mem : u ∈ c₁.support.toFinset ∩ c₂.support.toFinset := by rw [hinter]; simp
  have huC₂ : u ∈ c₂.support := List.mem_toFinset.mp (Finset.mem_inter.mp hu_mem).2
  let D : Finset V := c₂.support.toFinset.erase u
  have hD_card : 2 ≤ D.card := by
    have h3c : 3 ≤ c₂.support.toFinset.card := by rw [cycle_support_card c₂ hc₂]; exact hc₂.three_le_length
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr huC₂)]; omega
  obtain ⟨d₀, hd₀⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  have hdisj₀ : Disjoint c₁.support.toFinset D := by
    rw [Finset.disjoint_left]; intro z hz1 hz2
    have hzu : z ≠ u := (Finset.mem_erase.mp hz2).1
    have hzC₂ : z ∈ c₂.support.toFinset := Finset.mem_of_mem_erase hz2
    have hz_int : z ∈ ({u} : Finset V) := by rw [← hinter]; exact Finset.mem_inter.mpr ⟨hz1, hzC₂⟩
    exact hzu (Finset.mem_singleton.mp hz_int)
  obtain ⟨v, c, hc, hev, hdisj_c, hH_conn, hchord_ev, hchord_struct⟩ :=
    maximal_even_cycle_lemma S.graph h3 D d₀ hd₀ (cycle_erase_preconnected c₂ hc₂ huC₂)
      c₁ hc₁ heven hdisj₀
  -- If u ∉ c.support, then c and c₂ are disjoint, contradicting Lemma 3.4(1)!
  by_cases huC : u ∉ c.support
  · have hdisj_cc2 : Disjoint c.support.toFinset c₂.support.toFinset := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      by_cases hzu : z = u
      · subst hzu; exact huC (List.mem_toFinset.mp hz1)
      · exact Finset.disjoint_left.mp hdisj_c hz1 (Finset.mem_erase.mpr ⟨hzu, hz2⟩)
    exact cycle_pair_obstructions_disjoint_even_odd S hconn h3 hnoc c c₂ hc hc₂ hev hodd hdisj_cc2
  push Not at huC
  have hinter_c : ∀ x, x ∈ c.support → x ∈ c₂.support → x = u := by
    intro x hx1 hx2
    by_contra hxu
    exact Finset.disjoint_left.mp hdisj_c (List.mem_toFinset.mpr hx1)
      (Finset.mem_erase.mpr ⟨hxu, List.mem_toFinset.mpr hx2⟩)
  -- Helper: from any neighbor w ∉ V(c) of u₂ ∈ V(c) \ {u}, get a path u₂ → b ∈ D internally disjoint from c ∪ c₂
  have hpath_from_nbr : ∀ (u₂ : V), u₂ ∈ c.support → u₂ ≠ u →
      (∃ w ∉ c.support.toFinset, S.graph.Adj u₂ w) →
      ∃ b ∈ c₂.support, b ≠ u ∧ ∃ P : S.graph.Walk u₂ b, P.IsPath ∧
        (∀ x ∈ P.support, x ≠ u₂ → x ≠ b → x ∉ c.support ∧ x ∉ c₂.support) := by
    intro u₂ hu₂C hu₂u ⟨w, hwC, hu₂w⟩
    have hd₀C : d₀ ∉ c.support.toFinset := Finset.disjoint_right.mp hdisj_c hd₀
    obtain ⟨r⟩ := hH_conn ⟨w, hwC⟩ ⟨d₀, hd₀C⟩
    let φH : S.graph.induce ((c.support.toFinset : Set V)ᶜ) →g S.graph :=
      (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
    have hr_notC : ∀ x ∈ (r.map φH).support, x ∉ c.support.toFinset := by
      intro x hx; rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
      rcases hx with ⟨z, _, rfl⟩; exact z.2
    obtain ⟨b, hbD, q, hq_path, hq_sub, hq_int⟩ :=
      walk_first_hit_pc D (r.map φH) ⟨d₀, hd₀, by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨⟨d₀, hd₀C⟩, SimpleGraph.Walk.end_mem_support r, rfl⟩⟩
    have hu₂_not_q : u₂ ∉ q.support := fun hm =>
      hr_notC u₂ (hq_sub u₂ hm) (List.mem_toFinset.mpr hu₂C)
    have hu₂w' : S.graph.Adj u₂ (φH ⟨w, hwC⟩) := hu₂w
    refine ⟨b, List.mem_toFinset.mp (Finset.mem_of_mem_erase hbD), (Finset.mem_erase.mp hbD).1,
      SimpleGraph.Walk.cons hu₂w' q, SimpleGraph.Walk.IsPath.cons hq_path hu₂_not_q, ?_⟩
    intro x hx hxu₂ hxb
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    have hxq : x ∈ q.support := hx.resolve_left hxu₂
    refine ⟨fun h => hr_notC x (hq_sub x hxq) (List.mem_toFinset.mpr h), fun h => ?_⟩
    have hxu : x ≠ u := fun h' => hr_notC x (hq_sub x hxq) (h' ▸ List.mem_toFinset.mpr huC)
    exact hq_int x hxq hxb (Finset.mem_erase.mpr ⟨hxu, List.mem_toFinset.mpr h⟩)
  -- Case A: G[V(C)] ≅ K₄
  rcases hchord_struct with ⟨hc4, hK4⟩ | hle1_chord
  · -- Pick a path in G - {u} from C - {u} to D
    obtain ⟨u₂₀, hu₂₀C, hu₂₀u⟩ := Finset.exists_mem_ne (by
      have := even_cycle_length_ge_four c hc hev; rw [cycle_support_card c hc]; omega : 1 < c.support.toFinset.card) u
    have hd₀u : d₀ ≠ u := (Finset.mem_erase.mp hd₀).1
    obtain ⟨r⟩ := h3 {u} (by simp) ⟨u₂₀, by simp [hu₂₀u]⟩ ⟨d₀, by simp [hd₀u]⟩
    let f : S.graph.induce (({u} : Finset V)ᶜ : Set V) →g S.graph :=
      (SimpleGraph.Embedding.induce (({u} : Finset V)ᶜ : Set V)).toHom
    have hr_notu : u ∉ (r.map f).support := by
      intro hm; rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
      rcases hm with ⟨x, _, hxu⟩; exact x.2 (by simpa [f] using hxu)
    obtain ⟨u₂, hu₂C, qrev, hq_path, hq_sub, hq_int⟩ :=
      walk_first_hit_pc c.support.toFinset (r.map f).reverse
        ⟨u₂₀, hu₂₀C, by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_map, List.mem_map]; exact ⟨⟨u₂₀, by simp [hu₂₀u]⟩, SimpleGraph.Walk.start_mem_support r, rfl⟩⟩
    have hu₂u : u₂ ≠ u := fun h => hr_notu (by
      have h1 := hq_sub u₂ (SimpleGraph.Walk.end_mem_support qrev)
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1; exact h ▸ h1)
    let q := qrev.reverse
    cases hq_eq : q with
    | nil => exact False.elim (Finset.disjoint_left.mp hdisj_c hu₂C hd₀)
    | @cons _ w₁ _ hu₂w₁ q' =>
      have hw₁C : w₁ ∉ c.support.toFinset := by
        have hnd : q.support.Nodup := hq_path.reverse.support_nodup
        rw [hq_eq, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
        have hw1_ne : w₁ ≠ u₂ := fun h => hnd.1 (h ▸ SimpleGraph.Walk.start_mem_support q')
        have hw1_qrev : w₁ ∈ qrev.support := by
          have : w₁ ∈ q.support := by rw [hq_eq]; exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q')
          rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
        exact hq_int w₁ hw1_qrev hw1_ne
      obtain ⟨b, hbC₂, hbu, P, hP, hP_int⟩ :=
        hpath_from_nbr u₂ (List.mem_toFinset.mp hu₂C) hu₂u ⟨w₁, hw₁C, hu₂w₁⟩
      obtain ⟨p₁, p₂, hp₁, hp₂, hp_len, hp_supp, hw_eq⟩ :=
        k4_pair_paths S hnoc c hc hc4 hK4 huC (List.mem_toFinset.mp hu₂C) hu₂u.symm
      exact even_odd_cycle_linkage_one_vertex S c c₂ hc hc₂ hev hodd hinter_c
        huC (List.mem_toFinset.mp hu₂C) hu₂u.symm huC₂ hbC₂ hbu P hP hP_int
        p₁ p₂ hp₁ hp₂ (by omega) hp_supp hw_eq hnoc
  · -- Case B: C has at most one chord (of even distance)
    obtain ⟨col, hcol2, hcol_walk⟩ := even_cycle_bipartition c hc hev
    let X : Finset V := c.support.toFinset.filter fun z => col z = 0
    let Y : Finset V := c.support.toFinset.filter fun z => col z = 1
    have ⟨hX_ge2, hY_ge2⟩ := even_cycle_part_card_ge_two c hc hev col hcol2 hcol_walk
    rcases walkModFourWeight_even_of_even_length S.sign c hev with hw0 | hw2
    · -- Subcase B1: w(C) = 0. No vertex at odd distance from u has a neighbor in H!
      let Opp : Finset V := c.support.toFinset.filter fun z => col z ≠ col u
      let Same : Finset V := c.support.toFinset.filter fun z => col z = col u
      have hOpp_ge2 : 2 ≤ Opp.card := by
        have hcu := hcol2 u
        by_cases h0 : col u = 0
        · have : Opp = Y := by ext z; simp [Opp, Y, h0]; have := hcol2 z; omega
          rw [this]; exact hY_ge2
        · have h1 : col u = 1 := by omega
          have : Opp = X := by ext z; simp [Opp, X, h1]; have := hcol2 z; omega
          rw [this]; exact hX_ge2
      have hno_nbr_Opp : ∀ z ∈ Opp, ∀ w ∉ c.support.toFinset, ¬ S.graph.Adj z w := by
        intro z hz w hwC hzw
        have hzC : z ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hz).1
        have hcol_ne : col z ≠ col u := (Finset.mem_filter.mp hz).2
        have hzu : z ≠ u := fun h => hcol_ne (by rw [h])
        obtain ⟨b, hbC₂, hbu, P, hP, hP_int⟩ := hpath_from_nbr z hzC hzu ⟨w, hwC, hzw⟩
        obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, _, harc_e2, harc_w⟩ :=
          cycle_arcs_edges_subset c hc huC hzC hzu.symm
        have hpar2 := hcol_walk arc2 harc_e2
        have hcu2 := hcol2 u; have hcz2 := hcol2 z
        have harc2_odd : Odd arc2.length := ⟨arc2.length / 2, by omega⟩
        have hw_eq : (walkModFourWeight S.sign arc1 + walkModFourWeight S.sign arc2) +
            2 * (arc2.length : ZMod 4) = 2 := by
          rw [harc_w S.sign, hw0, (two_mul_nat_mod_four arc2.length).2 harc2_odd, zero_add]
        exact even_odd_cycle_linkage_one_vertex S c c₂ hc hc₂ hev hodd hinter_c
          huC hzC hzu.symm huC₂ hbC₂ hbu P hP hP_int arc1 arc2 harc1 harc2 harc_len harc_supp hw_eq hnoc
      -- Every vertex in Opp must be incident to a chord of C, so Opp.card = 2!
      have hall_chord_Opp : ∀ z ∈ Opp, ∃ y ∈ c.support, S.graph.Adj z y ∧ s(z, y) ∉ c.edges := by
        intro z hz
        by_contra hnc
        push Not at hnc
        obtain ⟨w, hwC, hzw⟩ := exists_neighbor_outside_even h3 c hc hev
          (List.mem_toFinset.mp (Finset.mem_filter.mp hz).1) hnc
        exact hno_nbr_Opp z hz w hwC hzw
      have hOpp_le2 : Opp.card ≤ 2 := by
        by_contra hgt
        have h3o : 3 ≤ Opp.card := by omega
        obtain ⟨x₁, hx₁⟩ := Finset.card_pos.mp (by omega : 0 < Opp.card)
        obtain ⟨x₂, hx₂, hx₂₁⟩ := Finset.exists_mem_ne (by omega : 1 < Opp.card) x₁
        have hcard_er : 1 ≤ ((Opp.erase x₁).erase x₂).card := by
          have hx₂' : x₂ ∈ Opp.erase x₁ := Finset.mem_erase.mpr ⟨hx₂₁, hx₂⟩
          rw [Finset.card_erase_of_mem hx₂', Finset.card_erase_of_mem hx₁]; omega
        obtain ⟨x₃, hx₃_er⟩ := Finset.card_pos.mp hcard_er
        have hx₃ : x₃ ∈ Opp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx₃_er)
        have hx₃₂ : x₃ ≠ x₂ := (Finset.mem_erase.mp hx₃_er).1
        have hx₃₁ : x₃ ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx₃_er)).1
        obtain ⟨y₁, hy₁C, hxy₁, hch₁⟩ := hall_chord_Opp x₁ hx₁
        obtain ⟨y₂, hy₂C, hxy₂, hch₂⟩ := hall_chord_Opp x₂ hx₂
        obtain ⟨y₃, hy₃C, hxy₃, hch₃⟩ := hall_chord_Opp x₃ hx₃
        have he12 := hle1_chord _ _
          ⟨x₁, y₁, rfl, List.mem_toFinset.mp (Finset.mem_filter.mp hx₁).1, hy₁C, hxy₁, hch₁⟩
          ⟨x₂, y₂, rfl, List.mem_toFinset.mp (Finset.mem_filter.mp hx₂).1, hy₂C, hxy₂, hch₂⟩
        have he13 := hle1_chord _ _
          ⟨x₁, y₁, rfl, List.mem_toFinset.mp (Finset.mem_filter.mp hx₁).1, hy₁C, hxy₁, hch₁⟩
          ⟨x₃, y₃, rfl, List.mem_toFinset.mp (Finset.mem_filter.mp hx₃).1, hy₃C, hxy₃, hch₃⟩
        rcases Sym2.eq_iff.mp he12 with ⟨h, _⟩ | ⟨_, h⟩
        · exact hx₂₁ h.symm
        · rcases Sym2.eq_iff.mp he13 with ⟨h', _⟩ | ⟨_, h'⟩
          · exact hx₃₁ h'.symm
          · exact hx₃₂ (h'.symm.trans h)
      -- Also Same.card = Opp.card = 2 (same walk-balance argument: |Same| ≤ 2)
      -- Wait: let's prove Same.card ≤ 2 via the 4-line walk balance!
      have hSame_eq_Opp : Same.card = Opp.card := by
        have htail_toFinset : c.support.tail.toFinset = c.support.toFinset := by
          ext z; rw [List.mem_toFinset, List.mem_toFinset]
          have hcons : c.support = v :: c.support.tail := by cases c <;> simp
          rw [hcons, List.mem_cons]
          constructor
          · exact Or.inr
          · rintro (rfl | hz)
            · cases hc_eq : c with
              | nil => exact absurd hc_eq hc.ne_nil
              | cons _ r => simp [SimpleGraph.Walk.end_mem_support r]
            · exact hz
        have hwalk_bal : ∀ {a b : V} (p : S.graph.Walk a b),
            (∀ e ∈ p.edges, e ∈ c.edges) →
            (Even p.length → (p.support.tail.filter (fun z => col z = col u)).length =
              (p.support.tail.filter (fun z => col z ≠ col u)).length) ∧
            (Odd p.length →
              (col b = col u → (p.support.tail.filter (fun z => col z = col u)).length =
                (p.support.tail.filter (fun z => col z ≠ col u)).length + 1) ∧
              (col b ≠ col u → (p.support.tail.filter (fun z => col z ≠ col u)).length =
                (p.support.tail.filter (fun z => col z = col u)).length + 1)) := by
          intro a b p
          induction p with
          | nil => intro _; refine ⟨fun _ => by simp, fun h => by rcases h with ⟨k, hk⟩; simp at hk⟩
          | @cons x y z hxy r ihr =>
            intro hr
            have hxy_e : s(x, y) ∈ c.edges := hr s(x, y) (by simp)
            have hr_e : ∀ e ∈ r.edges, e ∈ c.edges := fun e he => hr e (List.mem_cons_of_mem _ he)
            have ih := ihr hr_e
            have hpar_xy := hcol_walk (SimpleGraph.Walk.cons hxy .nil) (fun e he => by simp at he; rwa [he])
            have hpar_r := hcol_walk r hr_e
            simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hpar_xy
            have hcx := hcol2 x; have hcy := hcol2 y; have hcz := hcol2 z; have hcu := hcol2 u
            have hsupp_tail : (SimpleGraph.Walk.cons hxy r).support.tail = y :: r.support.tail := by
              cases r <;> simp
            rw [hsupp_tail]
            constructor
            · intro hev_cons
              have hodd_r : Odd r.length := by
                rcases hev_cons with ⟨k, hk⟩; simp only [SimpleGraph.Walk.length_cons] at hk
                exact ⟨k - 1, by omega⟩
              have hcy_ne_cz : col y ≠ col z := by rcases hodd_r with ⟨m, hm⟩; omega
              by_cases hcyu : col y = col u
              · have hczu : col z ≠ col u := by omega
                have h1 := (ih.2 hodd_r).2 hczu
                have hcyu_ne : ¬ col y ≠ col u := not_not.mpr hcyu
                simp only [List.filter_cons, decide_eq_true hcyu, decide_eq_false hcyu_ne,
                  List.length_cons]; omega
              · have hczu : col z = col u := by omega
                have h1 := (ih.2 hodd_r).1 hczu
                simp only [List.filter_cons, decide_eq_false hcyu, decide_eq_true hcyu,
                  List.length_cons]; omega
            · intro hodd_cons
              have hev_r : Even r.length := by
                rcases hodd_cons with ⟨k, hk⟩; simp only [SimpleGraph.Walk.length_cons] at hk
                exact ⟨k, by omega⟩
              have hcy_eq_cz : col y = col z := by rcases hev_r with ⟨m, hm⟩; omega
              have h1 := ih.1 hev_r
              constructor
              · intro hczu; have hcyu : col y = col u := by omega
                have hcyu_ne : ¬ col y ≠ col u := not_not.mpr hcyu
                simp only [List.filter_cons, decide_eq_true hcyu, decide_eq_false hcyu_ne,
                  List.length_cons]; omega
              · intro hczu; have hcyu : col y ≠ col u := by omega
                have hcyu_eq : ¬ col y = col u := hcyu
                simp only [List.filter_cons, decide_eq_false hcyu_eq, decide_eq_true hcyu,
                  List.length_cons]; omega
        have hS_len : Same.card = (c.support.tail.filter (fun z => col z = col u)).length := by
          have hnd := hc.support_nodup.filter (fun z => decide (col z = col u))
          rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext z; simp [Same, ← htail_toFinset]
        have hO_len : Opp.card = (c.support.tail.filter (fun z => col z ≠ col u)).length := by
          have hnd := hc.support_nodup.filter (fun z => decide (col z ≠ col u))
          rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext z; simp [Opp, ← htail_toFinset]
        rw [hS_len, hO_len]
        exact (hwalk_bal c (fun _ h => h)).1 hev
      -- Now Same has card ≤ 2 and separates Opp from d₀ ∈ D!
      have hSame_le2 : Same.card ≤ 2 := by omega
      obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < Opp.card)
      have hx₀S : x₀ ∉ Same := by simp only [Opp, Same, Finset.mem_filter] at hx₀ ⊢; tauto
      have hd₀S : d₀ ∉ Same := fun h => Finset.disjoint_right.mp hdisj_c hd₀ (Finset.mem_filter.mp h).1
      obtain ⟨r⟩ := h3 Same hSame_le2 ⟨x₀, hx₀S⟩ ⟨d₀, hd₀S⟩
      let f : S.graph.induce ((Same : Set V)ᶜ) →g S.graph := (SimpleGraph.Embedding.induce ((Same : Set V)ᶜ)).toHom
      have hd₀O : d₀ ∉ Opp := fun h => Finset.disjoint_right.mp hdisj_c hd₀ (Finset.mem_filter.mp h).1
      obtain ⟨a, haO, b, hbO, hab, _, hbp⟩ := walk_exits_finset_pc Opp (r.map f) hx₀ hd₀O
      have hbS : b ∉ Same := by
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hbp
        rcases hbp with ⟨z, _, rfl⟩; exact z.2
      have hbC : b ∉ c.support.toFinset := by
        intro hbC'
        by_cases hcb : col b = col u
        · exact hbS (Finset.mem_filter.mpr ⟨hbC', hcb⟩)
        · exact hbO (Finset.mem_filter.mpr ⟨hbC', hcb⟩)
      exact hno_nbr_Opp a haO b hbC hab
    · -- Subcase B2: w(C) = 2. C is chordless, so a vertex z ∈ Same \ {u} has a neighbor in H!
      have hchordless : ∀ x ∈ c.support, ∀ y ∈ c.support, S.graph.Adj x y → s(x, y) ∈ c.edges := by
        intro x hx y hy hxy
        by_contra hch
        have hne : x ≠ y := S.graph.ne_of_adj hxy
        obtain ⟨arc1, arc2, harc1, harc2, harc_len, _, _, harc_e1, harc_e2, harc_w⟩ :=
          cycle_arcs_edges_subset c hc hx hy hne
        have hev_a := hchord_ev x y hx hy hne hxy hch arc1 arc2 harc1 harc2 harc_len harc_e1 harc_e2
        exact no_even_distance_chord_of_weight_two S hnoc c hc hev hw2 hx hy hne hxy hch
          arc1 arc2 harc1 harc2 harc_len (harc_w S.sign) hev_a.2
      let Same : Finset V := c.support.toFinset.filter fun z => col z = col u
      have hSame_ge2 : 2 ≤ Same.card := by
        have hcu := hcol2 u
        by_cases h0 : col u = 0
        · have : Same = X := by ext z; simp [Same, X, h0]
          rw [this]; exact hX_ge2
        · have h1 : col u = 1 := by omega
          have : Same = Y := by ext z; simp [Same, Y, h1]
          rw [this]; exact hY_ge2
      obtain ⟨z, hzSame, hzu⟩ := Finset.exists_mem_ne (by omega : 1 < Same.card) u
      have hzC : z ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hzSame).1
      have hcol_zu : col z = col u := (Finset.mem_filter.mp hzSame).2
      obtain ⟨w, hwC, hzw⟩ := exists_neighbor_outside_even h3 c hc hev hzC
        (fun y hy hzy => hchordless z hzC y hy hzy)
      obtain ⟨b, hbC₂, hbu, P, hP, hP_int⟩ := hpath_from_nbr z hzC hzu ⟨w, hwC, hzw⟩
      obtain ⟨arc1, arc2, harc1, harc2, harc_len, harc_supp, _, _, harc_e2, harc_w⟩ :=
        cycle_arcs_edges_subset c hc huC hzC hzu.symm
      have hpar2 := hcol_walk arc2 harc_e2
      have harc2_ev : Even arc2.length := ⟨arc2.length / 2, by omega⟩
      have hw_eq : (walkModFourWeight S.sign arc1 + walkModFourWeight S.sign arc2) +
          2 * (arc2.length : ZMod 4) = 2 := by
        rw [harc_w S.sign, hw2, (two_mul_nat_mod_four arc2.length).1 harc2_ev, add_zero]
      exact even_odd_cycle_linkage_one_vertex S c c₂ hc hc₂ hev hodd hinter_c
        huC hzC hzu.symm huC₂ hbC₂ hbu P hP hP_int arc1 arc2 harc1 harc2 harc_len harc_supp hw_eq hnoc

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
