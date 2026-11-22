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

section ExtremalSPQR

/-- A 2-separation `(VH, VG₂)` across `{x, y}` with both sides of size at least `4`. -/
private structure TwoSep (G : SimpleGraph V) where
  VH : Finset V
  VG₂ : Finset V
  x : V
  y : V
  hxy : x ≠ y
  hunion : VH ∪ VG₂ = Finset.univ
  hinter : VH ∩ VG₂ = {x, y}
  hcardH : 4 ≤ VH.card
  hcardG₂ : 4 ≤ VG₂.card
  hno_cross : ∀ u ∈ VH, ∀ w ∈ VG₂, u ≠ x → u ≠ y → w ≠ x → w ≠ y → ¬ G.Adj u w

private lemma component_card_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (A C : Finset V) (hA : A.card ≤ 2) (hC_ne : C.Nonempty) (hdisj : Disjoint C A)
    (hclosed : ∀ u ∈ C, ∀ w : V, G.Adj u w → w ∈ C ∪ A) :
    2 ≤ C.card := by
  by_contra hlt
  have hle1 : C.card ≤ 1 := by omega
  rcases hC_ne with ⟨u, hu⟩
  have hCeq : C = {u} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hu, fun w hw => ?_⟩
    by_contra hne
    have h2 : ({u, w} : Finset V).card ≤ C.card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    rw [Finset.card_pair (Ne.symm hne)] at h2
    omega
  have hsub : G.neighborFinset u ⊆ A := by
    intro w hw
    have hadj : G.Adj u w := (G.mem_neighborFinset u w).mp hw
    have hmem := hclosed u hu w hadj
    rw [Finset.mem_union, hCeq, Finset.mem_singleton] at hmem
    rcases hmem with rfl | hA_mem
    · exact absurd hadj (G.loopless.irrefl u)
    · exact hA_mem
  have hd : G.degree u ≤ A.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  have hu3 := hdeg u
  omega

private lemma walk_exits_set {G : SimpleGraph V} (S : Finset V) {u v : V}
    (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a ∈ S, ∃ b ∉ S, G.Adj a b ∧ b ∈ p.support := by
  induction p with
  | nil => exact absurd hu hv
  | @cons a b c hadj q ih =>
    by_cases hb : b ∈ S
    · obtain ⟨x, hx, y, hy, hxy, hmem⟩ := ih hb hv
      exact ⟨x, hx, y, hy, hxy, List.mem_cons_of_mem _ hmem⟩
    · exact ⟨a, hu, b, hb, hadj, List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q)⟩

private lemma exists_twoSep_of_not_three_conn (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Preconnected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hnot3 : ¬ ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected) :
    Nonempty (TwoSep G) := by
  classical
  push Not at hnot3
  rcases hnot3 with ⟨A, hA_le, hdisc⟩
  have hA_ne0 : A.card ≠ 0 := by
    intro h0
    have hA_emp : A = ∅ := Finset.card_eq_zero.mp h0
    apply hdisc
    intro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p⟩ := hconn u v
    refine ⟨p.induce (Aᶜ : Set V) ?_⟩
    intro w _
    simp [hA_emp]
  have hA_ne1 : A.card ≠ 1 := by
    intro h1
    rcases Finset.card_eq_one.mp h1 with ⟨v, rfl⟩
    apply hdisc
    simpa only [Finset.coe_singleton] using h2conn v
  have hA_eq2 : A.card = 2 := by omega
  rcases Finset.card_eq_two.mp hA_eq2 with ⟨x, y, hxy, rfl⟩
  let Sxy : Set V := (({x, y} : Finset V) : Set V)
  have hnot_pre : ∃ a b : (Sxyᶜ : Set V), ¬ (G.induce (Sxyᶜ : Set V)).Reachable a b := by
    by_contra hall
    push Not at hall
    exact hdisc hall
  rcases hnot_pre with ⟨a, b, hab⟩
  let C : Finset V := Finset.univ.filter fun u =>
    ∃ hu : u ∈ (Sxyᶜ : Set V), (G.induce (Sxyᶜ : Set V)).Reachable a ⟨u, hu⟩
  have ha_mem : a.1 ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a.2, SimpleGraph.Reachable.refl a⟩
  have hb_nmem : b.1 ∉ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    intro hb' hr
    exact hab hr
  have hC_disj : Disjoint C {x, y} := by
    rw [Finset.disjoint_left]
    intro u hu hxy_mem
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with ⟨hu', _⟩
    exact hu' hxy_mem
  have hC_closed : ∀ u ∈ C, ∀ w : V, G.Adj u w → w ∈ C ∪ {x, y} := by
    intro u hu w hadj
    by_cases hw : w ∈ ({x, y} : Finset V)
    · exact Finset.mem_union_right _ hw
    · refine Finset.mem_union_left _ ?_
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rcases hu with ⟨hu', hru⟩
      have hw' : w ∈ (Sxyᶜ : Set V) := hw
      exact ⟨hw', hru.trans (SimpleGraph.Adj.reachable (show (G.induce (Sxyᶜ : Set V)).Adj ⟨u, hu'⟩ ⟨w, hw'⟩ from hadj))⟩
  let D : Finset V := (Finset.univ \ {x, y}) \ C
  have hb_D : b.1 ∈ D := by
    simp only [D, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨b.2, hb_nmem⟩
  have hD_disj : Disjoint D {x, y} := by
    rw [Finset.disjoint_left]
    intro u hu
    simp only [D, Finset.mem_sdiff] at hu
    exact hu.1.2
  have hD_closed : ∀ u ∈ D, ∀ w : V, G.Adj u w → w ∈ D ∪ {x, y} := by
    intro u hu w hadj
    by_cases hw : w ∈ ({x, y} : Finset V)
    · exact Finset.mem_union_right _ hw
    · refine Finset.mem_union_left _ ?_
      simp only [D, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨hw, fun hwC => ?_⟩
      have hmem := hC_closed w hwC u hadj.symm
      rw [Finset.mem_union] at hmem
      rcases hmem with huC | huxy
      · exact hu.2 huC
      · exact hu.1 huxy
  have hC_ge2 : 2 ≤ C.card :=
    component_card_ge_two G hdeg {x, y} C (by rw [Finset.card_pair hxy]) ⟨a.1, ha_mem⟩ hC_disj hC_closed
  have hD_ge2 : 2 ≤ D.card :=
    component_card_ge_two G hdeg {x, y} D (by rw [Finset.card_pair hxy]) ⟨b.1, hb_D⟩ hD_disj hD_closed
  refine ⟨{
    VH := C ∪ {x, y}
    VG₂ := D ∪ {x, y}
    x := x
    y := y
    hxy := hxy
    hunion := by
      ext u
      simp only [Finset.mem_union, Finset.mem_univ, iff_true, D, Finset.mem_sdiff]
      by_cases h1 : u ∈ ({x, y} : Finset V)
      · exact Or.inl (Or.inr h1)
      · by_cases h2 : u ∈ C
        · exact Or.inl (Or.inl h2)
        · exact Or.inr (Or.inl ⟨⟨trivial, h1⟩, h2⟩)
    hinter := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_union, D, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hC | hxy', ⟨_, hnC⟩ | hxy''⟩
        · exact absurd hC hnC
        · exact hxy''
        · exact hxy'
        · exact hxy'
      · intro h; exact ⟨Or.inr h, Or.inr h⟩
    hcardH := by
      rw [Finset.card_union_of_disjoint hC_disj, Finset.card_pair hxy]; omega
    hcardG₂ := by
      rw [Finset.card_union_of_disjoint hD_disj, Finset.card_pair hxy]; omega
    hno_cross := by
      intro u hu w hw hux huy hwx hwy hadj
      have huC : u ∈ C := by
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · simp [hux, huy] at h
      have hwD : w ∈ D := by
        rcases Finset.mem_union.mp hw with h | h
        · exact h
        · simp [hwx, hwy] at h
      have hmem := hC_closed u huC w hadj
      rw [Finset.mem_union] at hmem
      rcases hmem with hwC | hwxy
      · exact (Finset.mem_sdiff.mp hwD).2 hwC
      · simp [hwx, hwy] at hwxy
  }⟩

private def twoSep_flip {G : SimpleGraph V} (d : TwoSep G) : TwoSep G where
  VH := d.VG₂
  VG₂ := d.VH
  x := d.x
  y := d.y
  hxy := d.hxy
  hunion := by rw [Finset.union_comm]; exact d.hunion
  hinter := by rw [Finset.inter_comm]; exact d.hinter
  hcardH := d.hcardG₂
  hcardG₂ := d.hcardH
  hno_cross := fun u hu w hw hux huy hwx hwy hadj =>
    d.hno_cross w hw u hu hwx hwy hux huy hadj.symm

private lemma twoSep_x_mem_VH {G : SimpleGraph V} (d : TwoSep G) : d.x ∈ d.VH := by
  have : d.x ∈ d.VH ∩ d.VG₂ := by rw [d.hinter]; simp
  exact (Finset.mem_inter.mp this).1

private lemma twoSep_y_mem_VH {G : SimpleGraph V} (d : TwoSep G) : d.y ∈ d.VH := by
  have : d.y ∈ d.VH ∩ d.VG₂ := by rw [d.hinter]; simp
  exact (Finset.mem_inter.mp this).1

private noncomputable def twoSep_minimal_is_rLeaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Preconnected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (B : Finset V) (d : TwoSep G) (hdB : d.VH ⊆ B)
    (hmin : ∀ d' : TwoSep G, d'.VH ⊆ B → d.VH.card ≤ d'.VH.card) :
    RLeafDecomp G := by
  classical
  refine {
    VH := d.VH
    VG₂ := d.VG₂
    x := d.x
    y := d.y
    hxy := d.hxy
    hunion := d.hunion
    hinter := d.hinter
    hcardH := d.hcardH
    hcardG₂ := by have := d.hcardG₂; omega
    hno_cross := d.hno_cross
    hT_3conn := ?_
  }
  intro A hA
  set T : SimpleGraph d.VH :=
    (G.induce (d.VH : Set V)) ⊔ SimpleGraph.fromRel (fun a b : d.VH =>
      (a.1 = d.x ∧ b.1 = d.y) ∨ (a.1 = d.y ∧ b.1 = d.x))
  by_contra hdisc
  have hnot_pre : ∃ u₀ v₀ : (Aᶜ : Set d.VH), ¬ (T.induce (Aᶜ : Set d.VH)).Reachable u₀ v₀ := by
    by_contra hall
    push Not at hall
    exact hdisc hall
  rcases hnot_pre with ⟨u₀, v₀, huv₀⟩
  let C₁ : Finset d.VH := Finset.univ.filter fun w =>
    ∃ hw : w ∈ (Aᶜ : Set d.VH), (T.induce (Aᶜ : Set d.VH)).Reachable u₀ ⟨w, hw⟩
  let C₂ : Finset d.VH := (Finset.univ \ A) \ C₁
  have hu₀_C₁ : u₀.1 ∈ C₁ := by
    simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u₀.2, SimpleGraph.Reachable.refl u₀⟩
  have hv₀_C₂ : v₀.1 ∈ C₂ := by
    simp only [C₂, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨v₀.2, ?_⟩
    simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    intro hv' hr; exact huv₀ hr
  have hC₁_no_C₂ : ∀ a ∈ C₁, ∀ b ∈ C₂, ¬ T.Adj a b := by
    intro a ha b hb hadj
    simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [C₂, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
    rcases ha with ⟨ha', hra⟩
    have hbC₁ : b ∈ C₁ := by
      simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hb.1, hra.trans (SimpleGraph.Adj.reachable (show (T.induce (Aᶜ : Set d.VH)).Adj ⟨a, ha'⟩ ⟨b, hb.1⟩ from hadj))⟩
    exact hb.2 hbC₁
  let x_sub : d.VH := ⟨d.x, twoSep_x_mem_VH d⟩
  let y_sub : d.VH := ⟨d.y, twoSep_y_mem_VH d⟩
  have hT_xy : T.Adj x_sub y_sub := by
    refine Or.inr ⟨?_, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    intro h; exact d.hxy (congrArg Subtype.val h)
  -- Since T.Adj x_sub y_sub, one of C₁, C₂ avoids both x_sub and y_sub
  have hex_C : ∃ (C_sub C_other : Finset d.VH),
      C_sub.Nonempty ∧ C_other.Nonempty ∧
      Disjoint C_sub A ∧ Disjoint C_other A ∧ Disjoint C_sub C_other ∧
      C_sub ∪ C_other = Finset.univ \ A ∧
      x_sub ∉ C_sub ∧ y_sub ∉ C_sub ∧
      (∀ a ∈ C_sub, ∀ b ∈ C_other, ¬ T.Adj a b) := by
    by_cases hx1 : x_sub ∈ C₁
    · have hy2 : y_sub ∉ C₂ := fun hy2 => hC₁_no_C₂ x_sub hx1 y_sub hy2 hT_xy
      have hx2 : x_sub ∉ C₂ := fun hx2 => (Finset.mem_sdiff.mp hx2).2 hx1
      refine ⟨C₂, C₁, ⟨v₀.1, hv₀_C₂⟩, ⟨u₀.1, hu₀_C₁⟩, ?_, ?_, ?_, ?_, hx2, hy2,
        fun a ha b hb h => hC₁_no_C₂ b hb a ha h.symm⟩
      · rw [Finset.disjoint_left]; intro z hz; exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
      · rw [Finset.disjoint_left]; intro z hz
        simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hz.1
      · rw [Finset.disjoint_left]; intro z hz; exact (Finset.mem_sdiff.mp hz).2
      · ext z; simp only [C₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hzA : z ∈ A
        · simp [hzA]; intro hC1
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hC1
          exact hC1.1 hzA
        · tauto
    · by_cases hy1 : y_sub ∈ C₁
      · have hx2 : x_sub ∉ C₂ := fun hx2 => hC₁_no_C₂ y_sub hy1 x_sub hx2 hT_xy.symm
        have hy2 : y_sub ∉ C₂ := fun hy2 => (Finset.mem_sdiff.mp hy2).2 hy1
        refine ⟨C₂, C₁, ⟨v₀.1, hv₀_C₂⟩, ⟨u₀.1, hu₀_C₁⟩, ?_, ?_, ?_, ?_, hx2, hy2,
          fun a ha b hb h => hC₁_no_C₂ b hb a ha h.symm⟩
        · rw [Finset.disjoint_left]; intro z hz; exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
        · rw [Finset.disjoint_left]; intro z hz
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact hz.1
        · rw [Finset.disjoint_left]; intro z hz; exact (Finset.mem_sdiff.mp hz).2
        · ext z; simp only [C₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
          by_cases hzA : z ∈ A
          · simp [hzA]; intro hC1
            simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hC1
            exact hC1.1 hzA
          · tauto
      · refine ⟨C₁, C₂, ⟨u₀.1, hu₀_C₁⟩, ⟨v₀.1, hv₀_C₂⟩, ?_, ?_, ?_, ?_, hx1, hy1, hC₁_no_C₂⟩
        · rw [Finset.disjoint_left]; intro z hz
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact hz.1
        · rw [Finset.disjoint_left]; intro z hz; exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
        · rw [Finset.disjoint_right]; intro z hz; exact (Finset.mem_sdiff.mp hz).2
        · ext z; simp only [C₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
          by_cases hzA : z ∈ A
          · simp [hzA]; intro hC1
            simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at hC1
            exact hC1.1 hzA
          · tauto
  rcases hex_C with ⟨C_sub, C_other, hC_ne, hO_ne, hCA_disj, hOA_disj, hCO_disj, hCO_union,
    hx_nC, hy_nC, hCO_no_edge⟩
  let emb : d.VH ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let C : Finset V := C_sub.map emb
  let S : Finset V := A.map emb
  let O : Finset V := C_other.map emb
  have hS_card : S.card ≤ 2 := by simpa [S] using hA
  have hC_disj_S : Disjoint C S := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_map.mp hz1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hz2 with ⟨b, hb, hba⟩
    exact Finset.disjoint_left.mp hCA_disj ha (Subtype.ext hba ▸ hb)
  have hC_closed : ∀ u ∈ C, ∀ w : V, G.Adj u w → w ∈ C ∪ S := by
    intro u hu w hadj
    rcases Finset.mem_map.mp hu with ⟨u_sub, hu_sub, rfl⟩
    have hux : u_sub.1 ≠ d.x := fun h => hx_nC (by convert hu_sub; exact Subtype.ext h.symm)
    have huy : u_sub.1 ≠ d.y := fun h => hy_nC (by convert hu_sub; exact Subtype.ext h.symm)
    have hw_VH : w ∈ d.VH := by
      by_contra hnw
      have hw_G₂ : w ∈ d.VG₂ := by
        have : w ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ w
        exact (Finset.mem_union.mp this).resolve_left hnw
      have hwx : w ≠ d.x := fun h => hnw (h ▸ twoSep_x_mem_VH d)
      have hwy : w ≠ d.y := fun h => hnw (h ▸ twoSep_y_mem_VH d)
      exact d.hno_cross u_sub.1 u_sub.2 w hw_G₂ hux huy hwx hwy hadj
    let w_sub : d.VH := ⟨w, hw_VH⟩
    by_cases hwA : w_sub ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w_sub, hwA, rfl⟩)
    · refine Finset.mem_union_left _ (Finset.mem_map.mpr ⟨w_sub, ?_, rfl⟩)
      have hmem : w_sub ∈ C_sub ∪ C_other := by
        rw [hCO_union]; simp [hwA]
      rcases Finset.mem_union.mp hmem with h1 | h2
      · exact h1
      · exact absurd (Or.inl hadj) (hCO_no_edge u_sub hu_sub w_sub h2)
  -- Show S.card = 2 using hconn and h2conn
  have hO_sub : ∀ z ∈ O, z ∉ C ∧ z ∉ S := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨z_sub, hz_sub, rfl⟩
    constructor
    · intro hC
      rcases Finset.mem_map.mp hC with ⟨a, ha, haeq⟩
      have : a = z_sub := Subtype.ext haeq
      subst this
      exact Finset.disjoint_left.mp hCO_disj ha hz_sub
    · intro hS
      rcases Finset.mem_map.mp hS with ⟨a, ha, haeq⟩
      have : a = z_sub := Subtype.ext haeq
      subst this
      exact Finset.disjoint_left.mp hOA_disj hz_sub ha
  rcases hC_ne with ⟨c₀, hc₀⟩
  rcases hO_ne with ⟨o₀, ho₀⟩
  have hc₀_C : c₀.1 ∈ C := Finset.mem_map.mpr ⟨c₀, hc₀, rfl⟩
  have ho₀_O : o₀.1 ∈ O := Finset.mem_map.mpr ⟨o₀, ho₀, rfl⟩
  have hS_ne0 : S.card ≠ 0 := by
    intro h0
    have hS_emp : S = ∅ := Finset.card_eq_zero.mp h0
    obtain ⟨p⟩ := hconn c₀.1 o₀.1
    obtain ⟨a, ha, b, hb, hadj, _⟩ := walk_exits_set C p hc₀_C (hO_sub o₀.1 ho₀_O).1
    have hmem := hC_closed a ha b hadj
    rw [hS_emp, Finset.union_empty] at hmem
    exact hb hmem
  have hS_ne1 : S.card ≠ 1 := by
    intro h1
    rcases Finset.card_eq_one.mp h1 with ⟨s, hSs⟩
    have hc₀_ns : c₀.1 ≠ s := fun h => by
      have : c₀.1 ∈ S := by rw [hSs, Finset.mem_singleton]; exact h
      exact Finset.disjoint_left.mp hC_disj_S hc₀_C this
    have ho₀_ns : o₀.1 ≠ s := fun h => (hO_sub o₀.1 ho₀_O).2 (by rw [hSs, Finset.mem_singleton]; exact h)
    obtain ⟨p⟩ := h2conn s ⟨c₀.1, hc₀_ns⟩ ⟨o₀.1, ho₀_ns⟩
    let pG : G.Walk c₀.1 o₀.1 := p.map (SimpleGraph.Embedding.induce ({s}ᶜ : Set V)).toHom
    obtain ⟨a, ha, b, hb, hadj, hb_supp⟩ := walk_exits_set C pG hc₀_C (hO_sub o₀.1 ho₀_O).1
    have hmem := hC_closed a ha b hadj
    rw [hSs, Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with hbC | rfl
    · exact hb hbC
    · dsimp only [pG] at hb_supp
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hb_supp
      rcases hb_supp with ⟨b', _, hb'eq⟩
      exact b'.2 hb'eq.symm
  have hS_eq2 : S.card = 2 := by omega
  rcases Finset.card_eq_two.mp hS_eq2 with ⟨a, b, hab, hSab⟩
  have hC_ge2 : 2 ≤ C.card :=
    component_card_ge_two G hdeg S C hS_card ⟨c₀.1, hc₀_C⟩ hC_disj_S hC_closed
  -- Show (Finset.univ \ C) has card ≥ 4 since (d.VG₂ \ {d.x, d.y}) ∪ S ⊆ Finset.univ \ C
  have hG₂_int_disj_VH : Disjoint (d.VG₂ \ {d.x, d.y}) d.VH := by
    rw [Finset.disjoint_left]
    intro z hz hVH
    have hinter : z ∈ d.VH ∩ d.VG₂ := Finset.mem_inter.mpr ⟨hVH, (Finset.mem_sdiff.mp hz).1⟩
    rw [d.hinter] at hinter
    exact (Finset.mem_sdiff.mp hz).2 hinter
  have hG₂_int_card : 2 ≤ (d.VG₂ \ {d.x, d.y}).card := by
    have hsub : ({d.x, d.y} : Finset V) ⊆ d.VG₂ := by
      intro z hz
      have : z ∈ d.VH ∩ d.VG₂ := by rw [d.hinter]; exact hz
      exact (Finset.mem_inter.mp this).2
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair d.hxy]
    have := d.hcardG₂; omega
  have hS_sub_VH : S ⊆ d.VH := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨z_sub, _, rfl⟩
    exact z_sub.2
  have hC_sub_VH : C ⊆ d.VH := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨z_sub, _, rfl⟩
    exact z_sub.2
  have hrem_card : 4 ≤ (Finset.univ \ C).card := by
    have hsub : (d.VG₂ \ {d.x, d.y}) ∪ S ⊆ Finset.univ \ C := by
      intro z hz
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ z, fun hzC => ?_⟩
      rcases Finset.mem_union.mp hz with h1 | h2
      · exact Finset.disjoint_left.mp hG₂_int_disj_VH h1 (hC_sub_VH hzC)
      · exact Finset.disjoint_left.mp hC_disj_S hzC h2
    have hdisj_GS : Disjoint (d.VG₂ \ {d.x, d.y}) S :=
      hG₂_int_disj_VH.mono_right hS_sub_VH
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_GS, hS_eq2] at hcard
    omega
  let d' : TwoSep G := {
    VH := C ∪ S
    VG₂ := (Finset.univ \ C)
    x := a
    y := b
    hxy := hab
    hunion := by
      ext z; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
      tauto
    hinter := by
      ext z
      rw [← hSab]
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hC | hS, hnC⟩
        · exact absurd hC hnC
        · exact hS
      · intro hS
        exact ⟨Or.inr hS, Finset.disjoint_right.mp hC_disj_S hS⟩
    hcardH := by
      rw [Finset.card_union_of_disjoint hC_disj_S, hS_eq2]; omega
    hcardG₂ := hrem_card
    hno_cross := by
      intro u hu w hw hua hub hwa hwb hadj
      have huC : u ∈ C := by
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · rw [hSab] at h; simp [hua, hub] at h
      have hw_nC : w ∉ C := (Finset.mem_sdiff.mp hw).2
      have hmem := hC_closed u huC w hadj
      rw [Finset.mem_union, hSab] at hmem
      rcases hmem with h1 | h2
      · exact hw_nC h1
      · simp [hwa, hwb] at h2
  }
  have hd'_sub : d'.VH ⊆ d.VH := Finset.union_subset hC_sub_VH hS_sub_VH
  have hd'_lt : d'.VH.card < d.VH.card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hd'_sub, fun heq => ?_⟩
    have ho_in : o₀.1 ∈ d'.VH := by rw [heq]; exact o₀.2
    rcases Finset.mem_union.mp ho_in with h1 | h2
    · exact (hO_sub o₀.1 ho₀_O).1 h1
    · exact (hO_sub o₀.1 ho₀_O).2 h2
  have hle := hmin d' (hd'_sub.trans hdB)
  omega

private lemma twoSep_disjoint_complement (G : SimpleGraph V)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (d₁ d₂ : TwoSep G) (h21 : d₂.VH ⊆ d₁.VG₂) :
    d₁.VH ⊆ d₂.VG₂ := by
  intro u hu
  by_cases hxy : u = d₁.x ∨ u = d₁.y
  · -- Suppose u ∈ {d₁.x, d₁.y}. Show u has a neighbor in d₁.VH \ {d₁.x, d₁.y}.
    have hex_nbr : ∃ p ∈ d₁.VH, p ≠ d₁.x ∧ p ≠ d₁.y ∧ G.Adj u p := by
      have hH_int : (d₁.VH \ {d₁.x, d₁.y}).Nonempty := by
        have hsub : ({d₁.x, d₁.y} : Finset V) ⊆ d₁.VH := by
          intro z hz; exact (Finset.mem_inter.mp (by rw [d₁.hinter]; exact hz)).1
        have hc : 2 ≤ (d₁.VH \ {d₁.x, d₁.y}).card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair d₁.hxy]; have := d₁.hcardH; omega
        exact Finset.card_pos.mp (by omega)
      have hG₂_int : (d₁.VG₂ \ {d₁.x, d₁.y}).Nonempty := by
        have hsub : ({d₁.x, d₁.y} : Finset V) ⊆ d₁.VG₂ := by
          intro z hz; exact (Finset.mem_inter.mp (by rw [d₁.hinter]; exact hz)).2
        have hc : 2 ≤ (d₁.VG₂ \ {d₁.x, d₁.y}).card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair d₁.hxy]; have := d₁.hcardG₂; omega
        exact Finset.card_pos.mp (by omega)
      rcases hH_int with ⟨w₁, hw₁⟩
      rcases hG₂_int with ⟨w₂, hw₂⟩
      let other : V := if u = d₁.x then d₁.y else d₁.x
      have hother_ne : u ≠ other := by
        rcases hxy with rfl | rfl
        · simp [other, d₁.hxy]
        · simp [other, d₁.hxy.symm]
      have hw₁_ne : w₁ ≠ other := by
        have := (Finset.mem_sdiff.mp hw₁).2
        simp only [other]; split_ifs <;> intro h <;> exact this (by simp [h])
      have hw₂_ne : w₂ ≠ other := by
        have := (Finset.mem_sdiff.mp hw₂).2
        simp only [other]; split_ifs <;> intro h <;> exact this (by simp [h])
      obtain ⟨p⟩ := h2conn other ⟨w₁, hw₁_ne⟩ ⟨w₂, hw₂_ne⟩
      let pG : G.Walk w₁ w₂ := p.map (SimpleGraph.Embedding.induce ({other}ᶜ : Set V)).toHom
      have hw₂_nH : w₂ ∉ d₁.VH \ {d₁.x, d₁.y} := by
        intro hmem
        have hinter : w₂ ∈ d₁.VH ∩ d₁.VG₂ :=
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hmem).1, (Finset.mem_sdiff.mp hw₂).1⟩
        rw [d₁.hinter] at hinter
        exact (Finset.mem_sdiff.mp hw₂).2 hinter
      obtain ⟨a, ha, b, hb, hadj, hb_supp⟩ := walk_exits_set (d₁.VH \ {d₁.x, d₁.y}) pG hw₁ hw₂_nH
      have hb_ne_other : b ≠ other := by
        dsimp only [pG] at hb_supp
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hb_supp
        rcases hb_supp with ⟨b', _, hb'eq⟩
        exact hb'eq ▸ b'.2
      have ha_VH : a ∈ d₁.VH := (Finset.mem_sdiff.mp ha).1
      have ha_nxy : a ≠ d₁.x ∧ a ≠ d₁.y := by
        have := (Finset.mem_sdiff.mp ha).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        exact this
      have hb_xy : b = d₁.x ∨ b = d₁.y := by
        by_contra hnb
        push Not at hnb
        have hb_G₂ : b ∈ d₁.VG₂ := by
          have : b ∈ d₁.VH ∪ d₁.VG₂ := by rw [d₁.hunion]; exact Finset.mem_univ b
          rcases Finset.mem_union.mp this with hVH | hG₂
          · exact absurd (Finset.mem_sdiff.mpr ⟨hVH, by simp [hnb.1, hnb.2]⟩) hb
          · exact hG₂
        exact d₁.hno_cross a ha_VH b hb_G₂ ha_nxy.1 ha_nxy.2 hnb.1 hnb.2 hadj
      have hbu : b = u := by
        rcases hxy with rfl | rfl <;> rcases hb_xy with rfl | rfl
        · rfl
        · exact absurd rfl (by simp [other] at hb_ne_other)
        · exact absurd rfl (by simp [other, d₁.hxy.symm] at hb_ne_other)
        · rfl
      subst hbu
      exact ⟨a, ha_VH, ha_nxy.1, ha_nxy.2, hadj.symm⟩
    rcases hex_nbr with ⟨p, hp_VH, hpx, hpy, hadj⟩
    by_contra hu_nG₂
    have hu_VH₂ : u ∈ d₂.VH := by
      have : u ∈ d₂.VH ∪ d₂.VG₂ := by rw [d₂.hunion]; exact Finset.mem_univ u
      exact (Finset.mem_union.mp this).resolve_right hu_nG₂
    have hu_nxy₂ : u ≠ d₂.x ∧ u ≠ d₂.y := by
      constructor <;> intro h <;> subst h
      · exact hu_nG₂ (Finset.mem_inter.mp (by rw [d₂.hinter]; simp)).2
      · exact hu_nG₂ (Finset.mem_inter.mp (by rw [d₂.hinter]; simp)).2
    have hp_nG₂₁ : p ∉ d₁.VG₂ := by
      intro hpG₂
      have : p ∈ d₁.VH ∩ d₁.VG₂ := Finset.mem_inter.mpr ⟨hp_VH, hpG₂⟩
      rw [d₁.hinter] at this
      simp [hpx, hpy] at this
    have hp_nVH₂ : p ∉ d₂.VH := fun h => hp_nG₂₁ (h21 h)
    have hp_G₂₂ : p ∈ d₂.VG₂ := by
      have : p ∈ d₂.VH ∪ d₂.VG₂ := by rw [d₂.hunion]; exact Finset.mem_univ p
      exact (Finset.mem_union.mp this).resolve_left hp_nVH₂
    have hp_nxy₂ : p ≠ d₂.x ∧ p ≠ d₂.y := by
      constructor <;> intro h <;> subst h
      · exact hp_nVH₂ (twoSep_x_mem_VH d₂)
      · exact hp_nVH₂ (twoSep_y_mem_VH d₂)
    exact d₂.hno_cross u hu_VH₂ p hp_G₂₂ hu_nxy₂.1 hu_nxy₂.2 hp_nxy₂.1 hp_nxy₂.2 hadj
  · push Not at hxy
    have hu_nG₂₁ : u ∉ d₁.VG₂ := by
      intro huG₂
      have : u ∈ d₁.VH ∩ d₁.VG₂ := Finset.mem_inter.mpr ⟨hu, huG₂⟩
      rw [d₁.hinter] at this
      simp [hxy.1, hxy.2] at this
    have hu_nVH₂ : u ∉ d₂.VH := fun h => hu_nG₂₁ (h21 h)
    have : u ∈ d₂.VH ∪ d₂.VG₂ := by rw [d₂.hunion]; exact Finset.mem_univ u
    exact (Finset.mem_union.mp this).resolve_left hu_nVH₂

end ExtremalSPQR

/-- **SPQR Two-Leaf Theorem (Section 6)**: If `G` is 2-connected with `δ(G) ≥ 3` and is not
3-connected, then `G` has two R-node leaves `μ, μ'` whose interiors are disjoint (`H' ⊆ G₂`). -/
theorem two_r_leaves_of_two_connected_min_deg_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hconn : G.Preconnected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hnot3 : ¬ ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected) :
    ∃ d₁ d₂ : RLeafDecomp G, d₁.VH ⊆ d₂.VG₂ ∧ d₂.VH ⊆ d₁.VG₂ := by
  classical
  have _ := hcard
  obtain ⟨d0⟩ := exists_twoSep_of_not_three_conn G hconn h2conn hdeg hnot3
  -- Step 1: Choose a TwoSep d₁ minimizing VH.card
  have hex1 : ∃ k : ℕ, ∃ d : TwoSep G, d.VH.card = k := ⟨d0.VH.card, d0, rfl⟩
  let k₁ := Nat.find hex1
  obtain ⟨d₁, hd₁_card⟩ := Nat.find_spec hex1
  have hd₁_min : ∀ d' : TwoSep G, d'.VH ⊆ Finset.univ → d₁.VH.card ≤ d'.VH.card := by
    intro d' _
    rw [hd₁_card]
    exact Nat.find_min' hex1 ⟨d', rfl⟩
  let r₁ : RLeafDecomp G :=
    twoSep_minimal_is_rLeaf G hconn h2conn hdeg Finset.univ d₁ (Finset.subset_univ _) hd₁_min
  -- Step 2: Choose a TwoSep d₂ with d₂.VH ⊆ d₁.VG₂ minimizing VH.card
  let d₁_flip := twoSep_flip d₁
  have hex2 : ∃ k : ℕ, ∃ d : TwoSep G, d.VH ⊆ d₁.VG₂ ∧ d.VH.card = k :=
    ⟨d₁_flip.VH.card, d₁_flip, Finset.Subset.refl d₁.VG₂, rfl⟩
  let k₂ := Nat.find hex2
  obtain ⟨d₂, hd₂_sub, hd₂_card⟩ := Nat.find_spec hex2
  have hd₂_min : ∀ d' : TwoSep G, d'.VH ⊆ d₁.VG₂ → d₂.VH.card ≤ d'.VH.card := by
    intro d' hd'
    rw [hd₂_card]
    exact Nat.find_min' hex2 ⟨d', hd', rfl⟩
  let r₂ : RLeafDecomp G :=
    twoSep_minimal_is_rLeaf G hconn h2conn hdeg d₁.VG₂ d₂ hd₂_sub hd₂_min
  have h12 : d₁.VH ⊆ d₂.VG₂ := twoSep_disjoint_complement G h2conn d₁ d₂ hd₂_sub
  exact ⟨r₁, r₂, h12, hd₂_sub⟩

end SignedGraphs
