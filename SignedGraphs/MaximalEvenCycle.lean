import SignedGraphs.Basic
import SignedGraphs.GraphTools
import SignedGraphs.ParityCore

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A chord of a cycle `c` is an edge `s(a, b)` of `G` with `a, b ∈ c.support` and `s(a, b) ∉ c.edges`. -/
def IsChord {G : SimpleGraph V} {v : V} (c : G.Walk v v) (e : Sym2 V) : Prop :=
  ∃ a b : V, e = s(a, b) ∧ a ∈ c.support ∧ b ∈ c.support ∧ G.Adj a b ∧ s(a, b) ∉ c.edges

private lemma shortest_path_in_set {G : SimpleGraph V} (L : Finset V)
    (hL_conn : ∀ (x : V) (hx : x ∈ L) (y : V) (hy : y ∈ L), (G.induce (L : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩)
    {u₁ u₂ : V} (hu₁ : u₁ ∉ L) (hu₂ : u₂ ∉ L) (hne : u₁ ≠ u₂)
    (x₁ x₂ : V) (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L) (h1 : G.Adj u₁ x₁) (h2 : G.Adj x₂ u₂) :
    ∃ (p : G.Walk u₁ u₂), p.IsPath ∧ x₁ ∈ p.support ∧
      (∀ z ∈ p.support, z ≠ u₁ → z ≠ u₂ → z ∈ L) := by
  classical
  obtain ⟨r⟩ := hL_conn x₁ hx₁ x₂ hx₂
  let rp := r.toPath
  let f : (G.induce (L : Set V)) →g G := (SimpleGraph.Embedding.induce (L : Set V)).toHom
  let rG : G.Walk x₁ x₂ := rp.1.map f
  have hrG_path : rG.IsPath := rp.2.map (fun _ _ h => Subtype.ext h)
  have hrG_L : ∀ z ∈ rG.support, z ∈ L := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨z', _, rfl⟩
    exact z'.2
  have h1' : (SimpleGraph.Walk.cons h1 rG).IsPath :=
    SimpleGraph.Walk.IsPath.cons hrG_path (fun hm => hu₁ (hrG_L u₁ hm))
  have h2' : ((SimpleGraph.Walk.cons h1 rG).append (SimpleGraph.Walk.cons h2 .nil)).IsPath := by
    apply isPath_append_of_disjoint_pc _ _ h1' (SimpleGraph.Walk.IsPath.mk' (by simp [G.ne_of_adj h2]))
    intro z hz1 hz2
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz2
    rcases hz2 with rfl | rfl
    · rfl
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz1
      rcases hz1 with h | h
      · exact False.elim (hne h.symm)
      · exact False.elim (hu₂ (hrG_L u₂ h))
  refine ⟨(SimpleGraph.Walk.cons h1 rG).append (SimpleGraph.Walk.cons h2 .nil), h2', ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support rG)
  · intro z hz hz1 hz2
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | h) | (rfl | rfl)
    · exact absurd rfl hz1
    · exact hrG_L z h
    · exact hx₂
    · exact absurd rfl hz2

lemma walk_first_hit_pc {G : SimpleGraph V} (T : Finset V) {a b : V}
    (p : G.Walk a b) (hex : ∃ t ∈ T, t ∈ p.support) :
    ∃ t ∈ T, ∃ q : G.Walk a t, q.IsPath ∧
      (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ q.support, x ≠ t → x ∉ T) := by
  classical
  induction p with
  | nil =>
    rcases hex with ⟨t, htT, ht⟩
    simp at ht; subst ht
    exact ⟨t, htT, .nil, .nil, fun x hx => by simpa using hx, fun x hx hne => by simp at hx; exact absurd hx hne⟩
  | @cons x y z hxy r ih =>
    by_cases hxT : x ∈ T
    · exact ⟨x, hxT, .nil, .nil, fun v hv => by simp at hv; subst hv; exact List.mem_cons_self ..,
        fun v hv hne => by simp at hv; exact absurd hv hne⟩
    · have hex' : ∃ t ∈ T, t ∈ r.support := by
        rcases hex with ⟨t, htT, ht⟩
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | htr
        · exact absurd htT hxT
        · exact ⟨t, htT, htr⟩
      obtain ⟨t, htT, q, hq, hqsub, hqint⟩ := ih hex'
      let q' := (SimpleGraph.Walk.cons hxy q).toPath
      refine ⟨t, htT, q'.1, q'.2, ?_, ?_⟩
      · intro v hv
        have hv' := SimpleGraph.Walk.support_toPath_subset _ hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv' ⊢
        rcases hv' with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (hqsub v h)
      · intro v hv hvt
        have hv' := SimpleGraph.Walk.support_toPath_subset _ hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv'
        rcases hv' with rfl | h
        · exact hxT
        · exact hqint v h hvt

omit [Fintype V] [DecidableEq V] in
private lemma path_len_ge_two_of_not_mem_edges {G : SimpleGraph V} {v u₁ u₂ : V}
    (c : G.Walk v v) (p : G.Walk u₁ u₂) (hne : u₁ ≠ u₂)
    (hp_e : ∀ e ∈ p.edges, e ∈ c.edges) (hchord : s(u₁, u₂) ∉ c.edges) :
    2 ≤ p.length := by
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ w _ hadj q =>
    cases q with
    | nil => exfalso; exact hchord (hp_e s(u₁, w) (by simp))
    | cons _ _ => simp

omit [Fintype V] [DecidableEq V] in
private lemma path_len_ge_two_of_internal {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hne : a ≠ b) (y : V) (hy : y ∈ p.support) (hya : y ≠ a) (hyb : y ≠ b) :
    2 ≤ p.length := by
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ w _ hadj q =>
    cases q with
    | nil =>
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> contradiction
    | cons _ _ => simp

omit [Fintype V] [DecidableEq V] in
private lemma path_len_eq_one_adj {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (h1 : p.length = 1) : G.Adj a b := by
  cases p with
  | nil => simp at h1
  | @cons _ w _ hadj q =>
    cases q with
    | nil => exact hadj
    | cons _ _ => simp at h1

omit [Fintype V] [DecidableEq V] in
private lemma mem_support_of_edges_subset {G : SimpleGraph V} {v a b : V}
    (c : G.Walk v v) (p : G.Walk a b) (hp_pos : 1 ≤ p.length)
    (hp_e : ∀ e ∈ p.edges, e ∈ c.edges) :
    ∀ x ∈ p.support, x ∈ c.support := by
  cases p with
  | nil => simp at hp_pos
  | @cons _ w _ hadj r =>
    intro x hx
    have hex_e : ∃ y, s(x, y) ∈ (SimpleGraph.Walk.cons hadj r).edges := by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hr
      · exact ⟨w, by simp⟩
      · clear hp_pos hp_e
        induction r with
        | nil => simp at hr; subst hr; exact ⟨a, by simp [Sym2.eq_swap]⟩
        | @cons u₁ u₂ u₃ h' r' ih =>
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hr
          rcases hr with rfl | hr'
          · exact ⟨u₂, by simp⟩
          · obtain ⟨y, hy⟩ := ih hr'
            exact ⟨y, by simp [hy]⟩
    rcases hex_e with ⟨y, hy⟩
    exact SimpleGraph.Walk.fst_mem_support_of_mem_edges c (hp_e _ hy)

omit [Fintype V] in
private lemma mem_takeUntil_or_symm {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support),
      x ∈ (p.takeUntil y hy).support ∨ y ∈ (p.takeUntil x hx).support
  | _, _, .nil, x, y, hx, hy => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx hy
    subst hx; subst hy; left; simp
  | a, _, .cons h p, x, y, hx, hy => by
    by_cases hax : a = x
    · subst hax; left; exact SimpleGraph.Walk.start_mem_support _
    · by_cases hay : a = y
      · subst hay; right; exact SimpleGraph.Walk.start_mem_support _
      · have hx' : x ∈ p.support := by
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          exact hx.resolve_left (Ne.symm hax)
        have hy' : y ∈ p.support := by
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
          exact hy.resolve_left (Ne.symm hay)
        rcases mem_takeUntil_or_symm p hx' hy' with h1 | h2
        · left; simp [SimpleGraph.Walk.takeUntil, hay, h1]
        · right; simp [SimpleGraph.Walk.takeUntil, hax, h2]

/-- **Lemma 3.2 (Gao–Li–Ma–Xie)**: Let `G` be a 3-connected simple graph and `D` a nonempty
connected vertex set such that `G - D` contains an even cycle. Then there exists an even cycle
`C` disjoint from `D` such that:
1. `G - V(C)` is connected;
2. Every chord of `C` joins two vertices at even distance along `C`;
3. Either `C` has length 4 and induces `K₄`, or `C` has at most one chord. -/
set_option maxHeartbeats 800000 in
theorem maximal_even_cycle_lemma (G : SimpleGraph V)
    (h3 : ∀ A : Finset V, A.card ≤ 2 → (G.induce (Aᶜ : Set V)).Preconnected)
    (D : Finset V) (d₀ : V) (hd₀ : d₀ ∈ D)
    (hD_conn : ∀ (x : V) (hx : x ∈ D) (y : V) (hy : y ∈ D), (G.induce (D : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle) (heven₀ : Even c₀.length)
    (hdisj₀ : Disjoint c₀.support.toFinset D) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Even c.length ∧ Disjoint c.support.toFinset D ∧
      (G.induce ((c.support.toFinset : Set V)ᶜ)).Preconnected ∧
      (∀ u₁ u₂, u₁ ∈ c.support → u₂ ∈ c.support → u₁ ≠ u₂ → G.Adj u₁ u₂ → s(u₁, u₂) ∉ c.edges →
        ∀ (p₁ p₂ : G.Walk u₁ u₂), p₁.IsPath → p₂.IsPath → p₁.length + p₂.length = c.length →
          (∀ e ∈ p₁.edges, e ∈ c.edges) → (∀ e ∈ p₂.edges, e ∈ c.edges) →
          Even p₁.length ∧ Even p₂.length) ∧
      ((c.length = 4 ∧ ∀ a ∈ c.support, ∀ b ∈ c.support, a ≠ b → G.Adj a b) ∨
        ∀ e₁ e₂ : Sym2 V, IsChord c e₁ → IsChord c e₂ → e₁ = e₂) := by
  classical
  let compD : Finset V → Finset V := fun S =>
    Finset.univ.filter fun u =>
      ∃ hu : u ∈ ((S : Set V)ᶜ), ∃ hd : d₀ ∈ ((S : Set V)ᶜ),
        (G.induce ((S : Set V)ᶜ)).Reachable ⟨d₀, hd⟩ ⟨u, hu⟩
  have hcompD_mono : ∀ S₁ S₂ : Finset V, S₂ ⊆ S₁ → Disjoint S₁ D → compD S₁ ⊆ compD S₂ := by
    intro S₁ S₂ hsub hdisj1 u hu
    simp only [compD, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rcases hu with ⟨hu1, hd1, ⟨r⟩⟩
    have hinc : ∀ x : ((S₁ : Set V)ᶜ), x.1 ∈ ((S₂ : Set V)ᶜ) := fun x h => x.2 (hsub h)
    let φ : G.induce ((S₁ : Set V)ᶜ) →g G.induce ((S₂ : Set V)ᶜ) :=
      { toFun := fun x => ⟨x.1, hinc x⟩
        map_rel' := fun h => h }
    exact ⟨hinc ⟨u, hu1⟩, hinc ⟨d₀, hd1⟩, ⟨r.map φ⟩⟩
  have hD_sub_compD : ∀ S : Finset V, Disjoint S D → D ⊆ compD S := by
    intro S hdisj x hx
    have hdS : d₀ ∈ ((S : Set V)ᶜ) := Finset.disjoint_right.mp hdisj hd₀
    have hxS : x ∈ ((S : Set V)ᶜ) := Finset.disjoint_right.mp hdisj hx
    simp only [compD, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨r⟩ := hD_conn d₀ hd₀ x hx
    let φ : G.induce (D : Set V) →g G.induce ((S : Set V)ᶜ) :=
      { toFun := fun z => ⟨z.1, Finset.disjoint_right.mp hdisj z.2⟩
        map_rel' := fun h => h }
    exact ⟨hxS, hdS, ⟨r.map φ⟩⟩
  let score : Finset V → ℕ → ℕ := fun S len =>
    (Fintype.card V - (compD S).card) * (Fintype.card V + 1) + len
  have hex : ∃ n : ℕ, ∃ (v : V) (c : G.Walk v v),
      c.IsCycle ∧ Even c.length ∧ Disjoint c.support.toFinset D ∧
      score c.support.toFinset c.length = n :=
    ⟨score c₀.support.toFinset c₀.length, v₀, c₀, hc₀, heven₀, hdisj₀, rfl⟩
  obtain ⟨v, c, hc, heven, hdisj, hscore_eq⟩ := Nat.find_spec hex
  have hmin : ∀ {v' : V} (c' : G.Walk v' v'), c'.IsCycle → Even c'.length →
      Disjoint c'.support.toFinset D →
      score c.support.toFinset c.length ≤ score c'.support.toFinset c'.length := by
    intro v' c' hc' hev' hd'
    rw [hscore_eq]
    exact Nat.find_min' hex ⟨v', c', hc', hev', hd', rfl⟩
  have hmax_K : ∀ {v' : V} (c' : G.Walk v' v'), c'.IsCycle → Even c'.length →
      Disjoint c'.support.toFinset D →
      (compD c'.support.toFinset).card ≤ (compD c.support.toFinset).card := by
    intro v' c' hc' hev' hd'
    have hle := hmin c' hc' hev' hd'
    have hc_le : c.length ≤ Fintype.card V := by
      rw [← cycle_support_card c hc]; exact Finset.card_le_univ _
    have hc'_le : c'.length ≤ Fintype.card V := by
      rw [← cycle_support_card c' hc']; exact Finset.card_le_univ _
    have hK_le : (compD c.support.toFinset).card ≤ Fintype.card V := Finset.card_le_univ _
    have hK'_le : (compD c'.support.toFinset).card ≤ Fintype.card V := Finset.card_le_univ _
    dsimp only [score] at hle
    by_contra hgt
    have h1 : Fintype.card V - (compD c'.support.toFinset).card + 1 ≤
        Fintype.card V - (compD c.support.toFinset).card := by omega
    have h2 : (Fintype.card V - (compD c'.support.toFinset).card + 1) * (Fintype.card V + 1) ≤
        (Fintype.card V - (compD c.support.toFinset).card) * (Fintype.card V + 1) :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have hmin_len_sub : ∀ {v' : V} (c' : G.Walk v' v'), c'.IsCycle → Even c'.length →
      c'.support.toFinset ⊆ c.support.toFinset → c.length ≤ c'.length := by
    intro v' c' hc' hev' hsub
    have hd' : Disjoint c'.support.toFinset D := hdisj.mono_left hsub
    have hK_sub : compD c.support.toFinset ⊆ compD c'.support.toFinset :=
      hcompD_mono c.support.toFinset c'.support.toFinset hsub hdisj
    have hK_ge : (compD c.support.toFinset).card ≤ (compD c'.support.toFinset).card :=
      Finset.card_le_card hK_sub
    have hK_le := hmax_K c' hc' hev' hd'
    have hK_eq : (compD c'.support.toFinset).card = (compD c.support.toFinset).card :=
      le_antisymm hK_le hK_ge
    have hle := hmin c' hc' hev' hd'
    dsimp only [score] at hle
    rw [hK_eq] at hle
    omega
  obtain ⟨col, hcol_lt2, hcol_edge, hcol_walk⟩ := even_cycle_bipartition c hc heven
  let K : Finset V := compD c.support.toFinset
  have hK_disj_C : Disjoint K c.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.1
  have hK_closed : ∀ x ∈ K, ∀ y : V, G.Adj x y → y ∈ K ∪ c.support.toFinset := by
    intro x hx y hadj
    by_cases hyC : y ∈ c.support.toFinset
    · exact Finset.mem_union_right _ hyC
    · refine Finset.mem_union_left _ ?_
      simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with ⟨hxC, hdC, hr⟩
      exact ⟨hyC, hdC, hr.trans (SimpleGraph.Adj.reachable (show (G.induce ((c.support.toFinset : Set V)ᶜ)).Adj ⟨x, hxC⟩ ⟨y, hyC⟩ from hadj))⟩
  -- PART 1: Prove G - V(C) is connected
  have hG_minus_C_conn : (G.induce ((c.support.toFinset : Set V)ᶜ)).Preconnected := by
    by_contra hdisc
    have hd₀_nC : d₀ ∈ ((c.support.toFinset : Set V)ᶜ) := Finset.disjoint_right.mp hdisj hd₀
    have hex_w : ∃ w₀ : V, w₀ ∉ c.support.toFinset ∧ w₀ ∉ K := by
      by_contra hall
      push Not at hall
      apply hdisc
      intro a b
      have haK : a.1 ∈ K := hall a.1 a.2
      have hbK : b.1 ∈ K := hall b.1 b.2
      simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and] at haK hbK
      rcases haK with ⟨_, _, hra⟩
      rcases hbK with ⟨_, _, hrb⟩
      exact hra.symm.trans hrb
    rcases hex_w with ⟨w₀, hw₀C, hw₀K⟩
    let L : Finset V := Finset.univ.filter fun u =>
      ∃ hu : u ∈ ((c.support.toFinset : Set V)ᶜ),
        (G.induce ((c.support.toFinset : Set V)ᶜ)).Reachable ⟨w₀, hw₀C⟩ ⟨u, hu⟩
    have hw₀L : w₀ ∈ L := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hw₀C, SimpleGraph.Reachable.refl _⟩
    have hL_disj_C : Disjoint L c.support.toFinset := by
      rw [Finset.disjoint_left]; intro x hx
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    have hL_disj_K : Disjoint L K := by
      rw [Finset.disjoint_left]; intro x hxL hxK
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
      simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and] at hxK
      rcases hxL with ⟨hxC, hrx⟩
      rcases hxK with ⟨_, hdC, hrK⟩
      apply hw₀K
      simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hw₀C, hdC, hrK.trans hrx.symm⟩
    have hL_closed : ∀ x ∈ L, ∀ y : V, G.Adj x y → y ∈ L ∪ c.support.toFinset := by
      intro x hx y hadj
      by_cases hyC : y ∈ c.support.toFinset
      · exact Finset.mem_union_right _ hyC
      · refine Finset.mem_union_left _ ?_
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨hxC, hr⟩
        exact ⟨hyC, hr.trans (SimpleGraph.Adj.reachable (show (G.induce ((c.support.toFinset : Set V)ᶜ)).Adj ⟨x, hxC⟩ ⟨y, hyC⟩ from hadj))⟩
    have hL_conn : ∀ (x : V) (hx : x ∈ L) (y : V) (hy : y ∈ L), (G.induce (L : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x hx y hy
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hx with ⟨hxC, hrx⟩
      rcases hy with ⟨hyC, hry⟩
      obtain ⟨r⟩ := hrx.symm.trans hry
      let f_ind : (G.induce ((c.support.toFinset : Set V)ᶜ)) →g G :=
        (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
      have hrL : ∀ z ∈ (r.map f_ind).support, z ∈ L := by
        intro z hz
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
        rcases hz with ⟨z', hz', rfl⟩
        have hreach_z : (G.induce ((c.support.toFinset : Set V)ᶜ)).Reachable ⟨x, hxC⟩ z' :=
          ⟨r.takeUntil z' hz'⟩
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨z'.2, hrx.trans hreach_z⟩
      exact ⟨(r.map f_ind).induce (L : Set V) hrL⟩
    let NL : Finset V := c.support.toFinset.filter fun u => ∃ x ∈ L, G.Adj x u
    let NK : Finset V := c.support.toFinset.filter fun u => ∃ x ∈ K, G.Adj x u
    have hNL_card : 3 ≤ NL.card := by
      apply sep_card_ge_three_of_three_conn h3 L NL w₀ d₀ hw₀L
        (fun hm => Finset.disjoint_left.mp hL_disj_K hm (hD_sub_compD _ hdisj hd₀))
        (fun hm => Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hm).1 hd₀)
        (hL_disj_C.mono_right (Finset.filter_subset _ _))
      intro x hx y hadj
      have hm := hL_closed x hx y hadj
      rw [Finset.mem_union] at hm
      rcases hm with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, x, hx, hadj⟩)
    have hNK_card : 3 ≤ NK.card := by
      apply sep_card_ge_three_of_three_conn h3 K NK d₀ w₀ (hD_sub_compD _ hdisj hd₀)
        hw₀K (fun hm => hw₀C (Finset.mem_filter.mp hm).1)
        (hK_disj_C.mono_right (Finset.filter_subset _ _))
      intro x hx y hadj
      have hm := hK_closed x hx y hadj
      rw [Finset.mem_union] at hm
      rcases hm with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, x, hx, hadj⟩)
    obtain ⟨u₁, hu₁⟩ := Finset.card_pos.mp (by omega : 0 < NL.card)
    obtain ⟨u₂, hu₂⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu₁]; omega : 0 < (NL.erase u₁).card)
    have hu₂_NL : u₂ ∈ NL := (Finset.mem_erase.mp hu₂).2
    have hu21 : u₂ ≠ u₁ := (Finset.mem_erase.mp hu₂).1
    obtain ⟨u₃, hu₃⟩ := Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem hu₂, Finset.card_erase_of_mem hu₁]; omega : 0 < ((NL.erase u₁).erase u₂).card)
    have hu₃_NL : u₃ ∈ NL := (Finset.mem_erase.mp (Finset.mem_erase.mp hu₃).2).2
    have hu32 : u₃ ≠ u₂ := (Finset.mem_erase.mp hu₃).1
    have hu31 : u₃ ≠ u₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hu₃).2).1
    have hu₁C : u₁ ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hu₁).1
    have hu₂C : u₂ ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hu₂_NL).1
    have hu₃C : u₃ ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hu₃_NL).1
    rcases (Finset.mem_filter.mp hu₁).2 with ⟨x₁, hx₁L, h1⟩
    rcases (Finset.mem_filter.mp hu₂_NL).2 with ⟨x₂, hx₂L, h2⟩
    rcases (Finset.mem_filter.mp hu₃_NL).2 with ⟨x₃, hx₃L, h3_adj⟩
    have hu₁nL : u₁ ∉ L := fun hm => Finset.disjoint_left.mp hL_disj_C hm (List.mem_toFinset.mpr hu₁C)
    have hu₂nL : u₂ ∉ L := fun hm => Finset.disjoint_left.mp hL_disj_C hm (List.mem_toFinset.mpr hu₂C)
    have hu₃nL : u₃ ∉ L := fun hm => Finset.disjoint_left.mp hL_disj_C hm (List.mem_toFinset.mpr hu₃C)
    obtain ⟨Q₁₂, hQ₁₂, hx₁_Q₁₂, hQ₁₂_L⟩ := shortest_path_in_set L hL_conn hu₁nL hu₂nL hu21.symm x₁ x₂ hx₁L hx₂L h1.symm h2
    obtain ⟨r₃⟩ := hL_conn x₃ hx₃L x₁ hx₁L
    let fL : (G.induce (L : Set V)) →g G := (SimpleGraph.Embedding.induce (L : Set V)).toHom
    let r₃G : G.Walk x₃ x₁ := r₃.map fL
    have hr₃_L : ∀ z ∈ r₃G.support, z ∈ L := by
      intro z hz; dsimp only [r₃G] at hz; rw [SimpleGraph.Walk.support_map, List.mem_map] at hz; rcases hz with ⟨z', _, rfl⟩; exact z'.2
    obtain ⟨z, hzQ₁₂_fin, R, hR, hR_sub, hR_int⟩ :=
      walk_first_hit_pc Q₁₂.support.toFinset r₃G ⟨x₁, List.mem_toFinset.mpr hx₁_Q₁₂, SimpleGraph.Walk.end_mem_support r₃G⟩
    have hzQ₁₂ : z ∈ Q₁₂.support := List.mem_toFinset.mp hzQ₁₂_fin
    have hzL : z ∈ L := hr₃_L z (hR_sub z (SimpleGraph.Walk.end_mem_support R))
    have hzu₁ : z ≠ u₁ := fun h => hu₁nL (h ▸ hzL)
    have hzu₂ : z ≠ u₂ := fun h => hu₂nL (h ▸ hzL)
    have hzu₃ : z ≠ u₃ := fun h => hu₃nL (h ▸ hzL)
    let A_p : G.Walk u₁ z := Q₁₂.takeUntil z hzQ₁₂
    let B_p : G.Walk z u₂ := Q₁₂.dropUntil z hzQ₁₂
    let E_p : G.Walk u₃ z := SimpleGraph.Walk.cons h3_adj.symm R
    have hA_path : A_p.IsPath := hQ₁₂.takeUntil hzQ₁₂
    have hB_path : B_p.IsPath := hQ₁₂.dropUntil hzQ₁₂
    have hE_path : E_p.IsPath := SimpleGraph.Walk.IsPath.cons hR (fun hm => hu₃nL (hr₃_L u₃ (hR_sub u₃ hm)))
    have hQ₁₂_len : Q₁₂.length = A_p.length + B_p.length := by
      rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec Q₁₂ hzQ₁₂]
    let Q₁₃ : G.Walk u₁ u₃ := A_p.append E_p.reverse
    let Q₂₃ : G.Walk u₂ u₃ := B_p.reverse.append E_p.reverse
    have hQ₁₃ : Q₁₃.IsPath := by
      apply isPath_append_of_disjoint_pc A_p E_p.reverse hA_path hE_path.reverse
      intro x hxA hxE
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hxE
      have hxQ : x ∈ Q₁₂.support := SimpleGraph.Walk.support_takeUntil_subset Q₁₂ hzQ₁₂ hxA
      rcases hxE with hxu3 | hxR
      · rw [hxu3] at hxQ; exact False.elim (hu₃nL (hQ₁₂_L u₃ hxQ hu31 hu32))
      · by_contra hxz
        exact hR_int x hxR hxz (List.mem_toFinset.mpr hxQ)
    have hQ₂₃ : Q₂₃.IsPath := by
      apply isPath_append_of_disjoint_pc B_p.reverse E_p.reverse hB_path.reverse hE_path.reverse
      intro x hxB hxE
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hxB hxE
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hxE
      have hxQ : x ∈ Q₁₂.support := SimpleGraph.Walk.support_dropUntil_subset Q₁₂ hzQ₁₂ hxB
      rcases hxE with hxu3 | hxR
      · rw [hxu3] at hxQ; exact False.elim (hu₃nL (hQ₁₂_L u₃ hxQ hu31 hu32))
      · by_contra hxz
        exact hR_int x hxR hxz (List.mem_toFinset.mpr hxQ)
    have hQ₁₃_L : ∀ x ∈ Q₁₃.support, x ≠ u₁ → x ≠ u₃ → x ∈ L := by
      intro x hx hx1 hx3
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hxA | hxE
      · have hxQ := SimpleGraph.Walk.support_takeUntil_subset Q₁₂ hzQ₁₂ hxA
        have hx2 : x ≠ u₂ := by
          intro h; rw [h] at hxA
          have hspec := SimpleGraph.Walk.take_spec Q₁₂ hzQ₁₂
          have hnd := hQ₁₂.support_nodup
          rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
          have hdrop_cons : B_p.support = z :: B_p.support.tail := by cases B_p <;> simp
          have hu₂B : u₂ ∈ B_p.support := SimpleGraph.Walk.end_mem_support B_p
          rw [hdrop_cons, List.mem_cons] at hu₂B
          exact hnd.2.2 u₂ hxA u₂ (hu₂B.resolve_left hzu₂.symm) rfl
        exact hQ₁₂_L x hxQ hx1 hx2
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hxE
        exact hr₃_L x (hR_sub x (hxE.resolve_left hx3))
    have hQ₂₃_L : ∀ x ∈ Q₂₃.support, x ≠ u₂ → x ≠ u₃ → x ∈ L := by
      intro x hx hx2 hx3
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hxB | hxE
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hxB
        have hxQ := SimpleGraph.Walk.support_dropUntil_subset Q₁₂ hzQ₁₂ hxB
        have hx1 : x ≠ u₁ := by
          intro h; rw [h] at hxB
          have hspec := SimpleGraph.Walk.take_spec Q₁₂ hzQ₁₂
          have hnd := hQ₁₂.support_nodup
          rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
          have hdrop_cons : B_p.support = z :: B_p.support.tail := by cases B_p <;> simp
          rw [hdrop_cons, List.mem_cons] at hxB
          exact hnd.2.2 u₁ (SimpleGraph.Walk.start_mem_support A_p) u₁ (hxB.resolve_left hzu₁.symm) rfl
        exact hQ₁₂_L x hxQ hx1 hx2
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_cons, List.mem_cons] at hxE
        exact hr₃_L x (hR_sub x (hxE.resolve_left hx3))
    have hz_Q₁₃ : z ∈ Q₁₃.support := by
      rw [SimpleGraph.Walk.mem_support_append_iff]; left; exact SimpleGraph.Walk.end_mem_support A_p
    have hz_Q₂₃ : z ∈ Q₂₃.support := by
      rw [SimpleGraph.Walk.mem_support_append_iff]; left
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact SimpleGraph.Walk.start_mem_support B_p
    have hQ₁₂_ge2 : 2 ≤ Q₁₂.length := path_len_ge_two_of_internal Q₁₂ hu21.symm z hzQ₁₂ hzu₁ hzu₂
    have hQ₁₃_ge2 : 2 ≤ Q₁₃.length := path_len_ge_two_of_internal Q₁₃ hu31.symm z hz_Q₁₃ hzu₁ hzu₃
    have hQ₂₃_ge2 : 2 ≤ Q₂₃.length := path_len_ge_two_of_internal Q₂₃ hu32.symm z hz_Q₂₃ hzu₂ hzu₃
    have hmatch : ∃ (a b : V) (Q : G.Walk a b), a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧
        Q.IsPath ∧ 2 ≤ Q.length ∧ (∀ x ∈ Q.support, x ≠ a → x ≠ b → x ∈ L) ∧
        (Q.length + col a + col b) % 2 = 0 := by
      by_cases h12 : (Q₁₂.length + col u₁ + col u₂) % 2 = 0
      · exact ⟨u₁, u₂, Q₁₂, hu₁C, hu₂C, hu21.symm, hQ₁₂, hQ₁₂_ge2, hQ₁₂_L, h12⟩
      · by_cases h13 : (Q₁₃.length + col u₁ + col u₃) % 2 = 0
        · exact ⟨u₁, u₃, Q₁₃, hu₁C, hu₃C, hu31.symm, hQ₁₃, hQ₁₃_ge2, hQ₁₃_L, h13⟩
        · refine ⟨u₂, u₃, Q₂₃, hu₂C, hu₃C, hu32.symm, hQ₂₃, hQ₂₃_ge2, hQ₂₃_L, ?_⟩
          have hlen13 : Q₁₃.length = A_p.length + E_p.length := by
            simp [Q₁₃, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
          have hlen23 : Q₂₃.length = B_p.length + E_p.length := by
            simp [Q₂₃, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
          omega
    rcases hmatch with ⟨a, b, Q, haC, hbC, hab, hQ, hQ_ge2, hQ_L, hQ_par⟩
    have hex_wK : ∃ w ∈ NK, w ≠ a ∧ w ≠ b := by
      have hcard' : 0 < ((NK.erase a).erase b).card := by
        have h1 : (NK.erase a).card ≥ NK.card - 1 := Finset.pred_card_le_card_erase
        have h2 : ((NK.erase a).erase b).card ≥ (NK.erase a).card - 1 := Finset.pred_card_le_card_erase
        omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard'
      exact ⟨w, (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2,
        (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1, (Finset.mem_erase.mp hw).1⟩
    rcases hex_wK with ⟨w, hwNK, hwa, hwb⟩
    have hwC : w ∈ c.support := List.mem_toFinset.mp (Finset.mem_filter.mp hwNK).1
    rcases (Finset.mem_filter.mp hwNK).2 with ⟨xK, hxK, hxKw⟩
    obtain ⟨p₁, p₂, hp₁, hp₂, hp_len, hp_supp, hp_disj, hp₁_e, hp₂_e, _⟩ :=
      cycle_arcs_edges_subset c hc haC hbC hab
    have hex_arc : ∃ p : G.Walk a b, p.IsPath ∧ w ∉ p.support ∧
        (∀ x ∈ p.support, x ∈ c.support) ∧ (∀ e ∈ p.edges, e ∈ c.edges) := by
      by_cases hw1 : w ∈ p₁.support
      · exact ⟨p₂, hp₂, hp_disj w hw1 hwa hwb, fun x hx => (hp_supp x).mp (Or.inr hx), hp₂_e⟩
      · exact ⟨p₁, hp₁, hw1, fun x hx => (hp_supp x).mp (Or.inl hx), hp₁_e⟩
    rcases hex_arc with ⟨p, hp, hwnp, hpC, hp_e⟩
    have hp_pos : 1 ≤ p.length := by cases p with | nil => exact absurd rfl hab | cons _ _ => simp
    let c' : G.Walk a a := Q.append p.reverse
    have hc'_cyc : c'.IsCycle := by
      apply isCycle_append_reverse_of_disjoint p Q hp hQ _ (by omega)
      intro x hxQ hxa hxb hxp
      exact Finset.disjoint_left.mp hL_disj_C (hQ_L x hxQ hxa hxb) (List.mem_toFinset.mpr (hpC x hxp))
    have hc'_even : Even c'.length := by
      have hp_par := hcol_walk p hp_e
      have hlen_c' : c'.length = Q.length + p.length := by
        simp [c', SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
      exact ⟨c'.length / 2, by omega⟩
    have hc'_sub : c'.support.toFinset ⊆ L ∪ c.support.toFinset := by
      intro x hx
      have hx' := List.mem_toFinset.mp hx
      dsimp only [c'] at hx'
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx'
      rcases hx' with hxQ | hxp
      · by_cases hxa : x = a
        · subst hxa; exact Finset.mem_union_right _ (List.mem_toFinset.mpr haC)
        · by_cases hxb : x = b
          · subst hxb; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hbC)
          · exact Finset.mem_union_left _ (hQ_L x hxQ hxa hxb)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hpC x hxp))
    have hc'_disj_K : Disjoint c'.support.toFinset K := by
      rw [Finset.disjoint_left]
      intro x hx hxK
      rcases Finset.mem_union.mp (hc'_sub hx) with hxL | hxC
      · exact Finset.disjoint_left.mp hL_disj_K hxL hxK
      · exact Finset.disjoint_left.mp hK_disj_C hxK hxC
    have hc'_disj_D : Disjoint c'.support.toFinset D :=
      hc'_disj_K.mono_right (hD_sub_compD _ hdisj)
    have hK_sub_K' : K ⊆ compD c'.support.toFinset := by
      intro u hu
      have huC' : u ∈ ((c'.support.toFinset : Set V)ᶜ) := Finset.disjoint_right.mp hc'_disj_K hu
      have hdC' : d₀ ∈ ((c'.support.toFinset : Set V)ᶜ) := Finset.disjoint_right.mp hc'_disj_D hd₀
      simp only [compD, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with ⟨huC, hdC, ⟨r⟩⟩
      let f_ind : (G.induce ((c.support.toFinset : Set V)ᶜ)) →g G :=
        (SimpleGraph.Embedding.induce ((c.support.toFinset : Set V)ᶜ)).toHom
      have hr_nC' : ∀ y ∈ (r.map f_ind).support, y ∈ ((c'.support.toFinset : Set V)ᶜ) := by
        intro y hy
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
        rcases hy with ⟨y', hy', rfl⟩
        have hyK : y'.1 ∈ K := by
          simp only [K, compD, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨y'.2, hdC, ⟨r.takeUntil y' hy'⟩⟩
        exact Finset.disjoint_right.mp hc'_disj_K hyK
      exact ⟨huC', hdC', ⟨(r.map f_ind).induce ((c'.support.toFinset : Set V)ᶜ) hr_nC'⟩⟩
    have hw_not_C' : w ∉ c'.support.toFinset := by
      intro hm
      have hm' := List.mem_toFinset.mp hm
      dsimp only [c'] at hm'
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm'
      rcases hm' with hwQ | hwp
      · exact Finset.disjoint_left.mp hL_disj_C (hQ_L w hwQ hwa hwb) (List.mem_toFinset.mpr hwC)
      · exact hwnp hwp
    have hw_in_K' : w ∈ compD c'.support.toFinset := by
      have hxK' : xK ∈ compD c'.support.toFinset := hK_sub_K' hxK
      simp only [compD, Finset.mem_filter, Finset.mem_univ, true_and] at hxK' ⊢
      rcases hxK' with ⟨hxKC', hdC', hr⟩
      exact ⟨hw_not_C', hdC', hr.trans (SimpleGraph.Adj.reachable
        (show (G.induce ((c'.support.toFinset : Set V)ᶜ)).Adj ⟨xK, hxKC'⟩ ⟨w, hw_not_C'⟩ from hxKw))⟩
    have hw_not_K : w ∉ K := fun hm => Finset.disjoint_left.mp hK_disj_C hm (List.mem_toFinset.mpr hwC)
    have hlt_K : K.card < (compD c'.support.toFinset).card := by
      have hsub : insert w K ⊆ compD c'.support.toFinset := Finset.insert_subset hw_in_K' hK_sub_K'
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hw_not_K] at hle
      omega
    have hle_K := hmax_K c' hc'_cyc hc'_even hc'_disj_D
    change (compD c.support.toFinset).card < (compD c'.support.toFinset).card at hlt_K
    omega
  -- PART 2: Every chord of C has even distance along C (hence joins vertices of the same color)
  have hchord_even : ∀ u₁ u₂, u₁ ∈ c.support → u₂ ∈ c.support → u₁ ≠ u₂ → G.Adj u₁ u₂ →
      s(u₁, u₂) ∉ c.edges → ∀ (p₁ p₂ : G.Walk u₁ u₂), p₁.IsPath → p₂.IsPath →
      p₁.length + p₂.length = c.length → (∀ e ∈ p₁.edges, e ∈ c.edges) → (∀ e ∈ p₂.edges, e ∈ c.edges) →
      Even p₁.length ∧ Even p₂.length := by
    intro u₁ u₂ hu₁ hu₂ hu hadj hchord p₁ p₂ hp₁ hp₂ hlen hp₁_e hp₂_e
    have hp₁_ge2 : 2 ≤ p₁.length := path_len_ge_two_of_not_mem_edges c p₁ hu hp₁_e hchord
    have hp₂_ge2 : 2 ≤ p₂.length := path_len_ge_two_of_not_mem_edges c p₂ hu hp₂_e hchord
    by_cases hev1 : Even p₁.length
    · refine ⟨hev1, ?_⟩
      rcases heven with ⟨a, ha⟩; rcases hev1 with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
    · exfalso
      rw [Nat.not_even_iff_odd] at hev1
      let q : G.Walk u₁ u₂ := SimpleGraph.Walk.cons hadj .nil
      have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [q, hu])
      let c' : G.Walk u₁ u₁ := q.append p₁.reverse
      have hc'_cyc : c'.IsCycle := by
        apply isCycle_append_reverse_of_disjoint p₁ q hp₁ hq _ (by simp [q]; omega)
        intro x hx h1 h2; simp [q] at hx; rcases hx with rfl | rfl <;> contradiction
      have hc'_ev : Even c'.length := by
        rcases hev1 with ⟨k, hk⟩
        exact ⟨k + 1, by simp [c', q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
      have hc'_sub : c'.support.toFinset ⊆ c.support.toFinset := by
        intro x hx
        have hx' := List.mem_toFinset.mp hx
        dsimp only [c'] at hx'
        rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx'
        rcases hx' with hq' | hp'
        · simp [q] at hq'; rcases hq' with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
        · exact List.mem_toFinset.mpr (mem_support_of_edges_subset c p₁ (by omega) hp₁_e x hp')
      have hle := hmin_len_sub c' hc'_cyc hc'_ev hc'_sub
      simp only [c', q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
      omega
  have hchord_col : ∀ a b, a ∈ c.support → b ∈ c.support → G.Adj a b → s(a, b) ∉ c.edges →
      col a = col b := by
    intro a b ha hb hadj hch
    have hab : a ≠ b := G.ne_of_adj hadj
    obtain ⟨p₁, p₂, hp₁, hp₂, hlen, _, _, hp₁_e, hp₂_e, _⟩ := cycle_arcs_edges_subset c hc ha hb hab
    have ⟨hev1, _⟩ := hchord_even a b ha hb hab hadj hch p₁ p₂ hp₁ hp₂ hlen hp₁_e hp₂_e
    have hpar := hcol_walk p₁ hp₁_e
    have ha2 := hcol_lt2 a
    have hb2 := hcol_lt2 b
    rcases hev1 with ⟨k, hk⟩
    omega
  -- PART 3: Either C is a K₄ or C has at most one chord
  have hchord_struct : (c.length = 4 ∧ ∀ a ∈ c.support, ∀ b ∈ c.support, a ≠ b → G.Adj a b) ∨
      ∀ e₁ e₂ : Sym2 V, IsChord c e₁ → IsChord c e₂ → e₁ = e₂ := by
    by_cases hK4 : c.length = 4 ∧ ∀ a ∈ c.support, ∀ b ∈ c.support, a ≠ b → G.Adj a b
    · exact Or.inl hK4
    · right
      intro e₁ e₂ he₁ he₂
      by_contra hne_e
      rcases he₁ with ⟨a, b, rfl, haC, hbC, hab_adj, hab_ch⟩
      rcases he₂ with ⟨x, y, rfl, hxC, hyC, hxy_adj, hxy_ch⟩
      have hab : a ≠ b := G.ne_of_adj hab_adj
      have hxy : x ≠ y := G.ne_of_adj hxy_adj
      obtain ⟨A₁, A₂, hA₁, hA₂, hA_len, hA_supp, hA_disj, hA₁_e, hA₂_e, _⟩ :=
        cycle_arcs_edges_subset c hc haC hbC hab
      have hA₁_ge2 : 2 ≤ A₁.length := path_len_ge_two_of_not_mem_edges c A₁ hab hA₁_e hab_ch
      have hA₂_ge2 : 2 ≤ A₂.length := path_len_ge_two_of_not_mem_edges c A₂ hab hA₂_e hab_ch
      have ⟨hA₁_ev, hA₂_ev⟩ := hchord_even a b haC hbC hab hab_adj hab_ch A₁ A₂ hA₁ hA₂ hA_len hA₁_e hA₂_e
      have hcol_ab : col a = col b := hchord_col a b haC hbC hab_adj hab_ch
      have hcol_xy : col x = col y := hchord_col x y hxC hyC hxy_adj hxy_ch
      -- Helper for shared-endpoint case: given u ∈ {a, b}, other v ∈ {a, b}, z ∈ C \ {a, b} with chord u-z
      have hshared : ∀ (u v z : V) (A_u A_o : G.Walk u v),
          u ∈ c.support → v ∈ c.support → z ∈ c.support → u ≠ v → z ≠ u → z ≠ v →
          G.Adj u v → G.Adj u z → s(u, z) ∉ c.edges →
          A_u.IsPath → A_o.IsPath → A_u.length + A_o.length = c.length →
          2 ≤ A_o.length → Even A_u.length → z ∈ A_u.support →
          (∀ w ∈ A_u.support, w ∈ c.support) → (∀ e ∈ A_u.edges, e ∈ c.edges) → False := by
        intro u v z A_u A_o huC hvC hzC huv hzu hzv huv_adj huz_adj huz_ch hAu hAo hlen hAo2 hAu_ev hzAu hAuC hAu_e
        let P_uz := A_u.takeUntil z hzAu
        let P_zv := A_u.dropUntil z hzAu
        have hspec := SimpleGraph.Walk.take_spec A_u hzAu
        have hsum : P_uz.length + P_zv.length = A_u.length := by
          rw [← SimpleGraph.Walk.length_append, hspec]
        have hPuz_e : ∀ e ∈ P_uz.edges, e ∈ c.edges := fun e he =>
          hAu_e e (by rw [← hspec, SimpleGraph.Walk.edges_append, List.mem_append]; exact Or.inl he)
        have hPuz_ge2 : 2 ≤ P_uz.length := path_len_ge_two_of_not_mem_edges c P_uz hzu.symm hPuz_e huz_ch
        have hPzv_pos : 1 ≤ P_zv.length := by cases P_zv with | nil => exact absurd rfl hzv | cons _ _ => simp
        have hcol_uz : col u = col z := hchord_col u z huC hzC huz_adj huz_ch
        have hPuz_par := hcol_walk P_uz hPuz_e
        have hPuz_ev : Even P_uz.length := ⟨P_uz.length / 2, by omega⟩
        have hPzv_ev : Even P_zv.length := by
          rcases hAu_ev with ⟨k1, hk1⟩; rcases hPuz_ev with ⟨k2, hk2⟩; exact ⟨k1 - k2, by omega⟩
        have hPzv_ge2 : 2 ≤ P_zv.length := by rcases hPzv_ev with ⟨k, hk⟩; omega
        let q_zv : G.Walk z v := SimpleGraph.Walk.cons huz_adj.symm (SimpleGraph.Walk.cons huv_adj .nil)
        have hq_zv : q_zv.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [q_zv, hzu, hzv, huv])
        have hc'_cyc : (q_zv.append P_zv.reverse).IsCycle := by
          apply isCycle_append_reverse_of_disjoint P_zv q_zv (hAu.dropUntil hzAu) hq_zv _ (by simp [q_zv]; omega)
          intro w hw h1 h2
          simp only [q_zv, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hw
          rcases hw with hw1 | hw2 | hw3
          · exact absurd hw1 h1
          · rw [hw2]; intro hu_in
            have hnd := hAu.support_nodup
            rw [← hspec, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            have hdrop_cons : P_zv.support = z :: P_zv.support.tail := by cases P_zv <;> simp
            rw [hdrop_cons, List.mem_cons] at hu_in
            exact hnd.2.2 u (SimpleGraph.Walk.start_mem_support P_uz) u (hu_in.resolve_left hzu.symm) rfl
          · exact absurd hw3 h2
        have hc'_ev : Even (q_zv.append P_zv.reverse).length := by
          rcases hPzv_ev with ⟨k, hk⟩
          exact ⟨k + 1, by simp [q_zv, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega⟩
        have hc'_sub : (q_zv.append P_zv.reverse).support.toFinset ⊆ c.support.toFinset := by
          intro w hw
          have hw' := List.mem_toFinset.mp hw
          rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw'
          rcases hw' with hq | hp
          · simp only [q_zv, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
          · exact List.mem_toFinset.mpr (hAuC w (SimpleGraph.Walk.support_dropUntil_subset A_u hzAu hp))
        have hle := hmin_len_sub _ hc'_cyc hc'_ev hc'_sub
        simp only [q_zv, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
          SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
        omega
      -- Helper for non-crossing disjoint chords on the same arc A_u : a → b
      have hnoncross : ∀ (p q : V) (A_u A_o : G.Walk a b),
          p ∈ A_u.support → (hqA : q ∈ A_u.support) → p ≠ a → p ≠ b → q ≠ a → q ≠ b → p ≠ q →
          G.Adj p q → s(p, q) ∉ c.edges →
          A_u.IsPath → A_o.IsPath → A_u.length + A_o.length = c.length →
          2 ≤ A_o.length → Even A_u.length →
          (∀ w ∈ A_u.support, w ∈ c.support) → (∀ e ∈ A_u.edges, e ∈ c.edges) →
          p ∈ (A_u.takeUntil q hqA).support → False := by
        intro p q A_u A_o hpA hqA hpa hpb hqa hqb hpq hpq_adj hpq_ch hAu hAo hlen hAo2 hAu_ev hAuC hAu_e hp_before
        let P_aq := A_u.takeUntil q hqA
        let P_qb := A_u.dropUntil q hqA
        let P_ap := P_aq.takeUntil p hp_before
        let P_pq := P_aq.dropUntil p hp_before
        have hspec1 := SimpleGraph.Walk.take_spec A_u hqA
        have hspec2 := SimpleGraph.Walk.take_spec P_aq hp_before
        have hsum1 : P_aq.length + P_qb.length = A_u.length := by rw [← SimpleGraph.Walk.length_append, hspec1]
        have hsum2 : P_ap.length + P_pq.length = P_aq.length := by rw [← SimpleGraph.Walk.length_append, hspec2]
        have hPpq_e : ∀ e ∈ P_pq.edges, e ∈ c.edges := fun e he => by
          apply hAu_e e
          rw [← hspec1, SimpleGraph.Walk.edges_append, List.mem_append]; left
          change e ∈ P_aq.edges
          rw [← hspec2, SimpleGraph.Walk.edges_append, List.mem_append]; right; exact he
        have hPpq_ge2 : 2 ≤ P_pq.length := path_len_ge_two_of_not_mem_edges c P_pq hpq hPpq_e hpq_ch
        have hPap_pos : 1 ≤ P_ap.length := by cases P_ap with | nil => exact absurd rfl hpa.symm | cons _ _ => simp
        have hPqb_pos : 1 ≤ P_qb.length := by cases P_qb with | nil => exact absurd rfl hqb | cons _ _ => simp
        have hcol_pq : col p = col q := hchord_col p q (hAuC p hpA) (hAuC q hqA) hpq_adj hpq_ch
        have hPpq_par := hcol_walk P_pq hPpq_e
        have hPpq_ev : Even P_pq.length := ⟨P_pq.length / 2, by omega⟩
        have hPap_path : P_ap.IsPath := (hAu.takeUntil hqA).takeUntil hp_before
        have hPqb_path : P_qb.IsPath := hAu.dropUntil hqA
        have hPpq_step : (SimpleGraph.Walk.cons hpq_adj P_qb).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons hPqb_path ?_
          intro hp_in
          have hnd := hAu.support_nodup
          rw [← hspec1, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
          have hdrop_cons : P_qb.support = q :: P_qb.support.tail := by cases P_qb <;> simp
          rw [hdrop_cons, List.mem_cons] at hp_in
          exact hnd.2.2 p hp_before p (hp_in.resolve_left hpq) rfl
        let R_ab : G.Walk a b := P_ap.append (SimpleGraph.Walk.cons hpq_adj P_qb)
        have hR_ab : R_ab.IsPath := by
          apply isPath_append_of_disjoint_pc P_ap (SimpleGraph.Walk.cons hpq_adj P_qb) hPap_path hPpq_step
          intro w hw1 hw2
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw2
          rcases hw2 with rfl | hw_qb
          · rfl
          · exfalso
            have hw_aq : w ∈ P_aq.support := SimpleGraph.Walk.support_takeUntil_subset P_aq hp_before hw1
            have hnd := hAu.support_nodup
            rw [← hspec1, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
            by_cases hwq : w = q
            · rw [hwq] at hw1
              have hnd2 : P_aq.support.Nodup := (hAu.takeUntil hqA).support_nodup
              rw [← hspec2, SimpleGraph.Walk.support_append, List.nodup_append] at hnd2
              have hdrop2 : P_pq.support = p :: P_pq.support.tail := by cases P_pq <;> simp
              have hq_pq : q ∈ P_pq.support := SimpleGraph.Walk.end_mem_support P_pq
              rw [hdrop2, List.mem_cons] at hq_pq
              exact hnd2.2.2 q hw1 q (hq_pq.resolve_left hpq.symm) rfl
            · have hdrop_cons : P_qb.support = q :: P_qb.support.tail := by cases P_qb <;> simp
              rw [hdrop_cons, List.mem_cons] at hw_qb
              exact hnd.2.2 w hw_aq w (hw_qb.resolve_left hwq) rfl
        let edge_ab : G.Walk a b := SimpleGraph.Walk.cons hab_adj .nil
        have hedge_ab : edge_ab.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [edge_ab, hab])
        have hc'_cyc : (R_ab.append edge_ab.reverse).IsCycle := by
          apply isCycle_append_reverse_of_disjoint edge_ab R_ab hedge_ab hR_ab _ (by simp [R_ab, edge_ab, SimpleGraph.Walk.length_append]; omega)
          intro w _ h1 h2 hw_e
          simp [edge_ab] at hw_e; rcases hw_e with rfl | rfl <;> contradiction
        have hc'_ev : Even (R_ab.append edge_ab.reverse).length := by
          have hlen_c' : (R_ab.append edge_ab.reverse).length = P_ap.length + P_qb.length + 2 := by
            simp [R_ab, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega
          rcases hAu_ev with ⟨k1, hk1⟩; rcases hPpq_ev with ⟨k2, hk2⟩
          exact ⟨k1 - k2 + 1, by omega⟩
        have hc'_sub : (R_ab.append edge_ab.reverse).support.toFinset ⊆ c.support.toFinset := by
          intro w hw
          have hw' := List.mem_toFinset.mp hw
          rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw'
          rcases hw' with hR | he
          · dsimp only [R_ab] at hR
            rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons, List.mem_cons] at hR
            rcases hR with h1 | hw_eq | h2
            · exact List.mem_toFinset.mpr (hAuC w (SimpleGraph.Walk.support_takeUntil_subset A_u hqA (SimpleGraph.Walk.support_takeUntil_subset P_aq hp_before h1)))
            · rw [hw_eq]; exact List.mem_toFinset.mpr (hAuC p hpA)
            · exact List.mem_toFinset.mpr (hAuC w (SimpleGraph.Walk.support_dropUntil_subset A_u hqA h2))
          · simp [edge_ab] at he; rcases he with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
        have hle := hmin_len_sub _ hc'_cyc hc'_ev hc'_sub
        simp only [R_ab, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
          SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
        omega
      -- Dispatch cases: shared endpoint vs disjoint
      by_cases hxa : x = a
      · subst hxa
        have hyb : y ≠ b := fun h => hne_e (by rw [h])
        rcases (hA_supp y).mpr hyC with hy1 | hy2
        · exact hshared x b y A₁ A₂ haC hbC hyC hab hxy.symm hyb hab_adj hxy_adj hxy_ch hA₁ hA₂ hA_len hA₂_ge2 hA₁_ev hy1 (fun w hw => (hA_supp w).mp (Or.inl hw)) hA₁_e
        · exact hshared x b y A₂ A₁ haC hbC hyC hab hxy.symm hyb hab_adj hxy_adj hxy_ch hA₂ hA₁ (by omega) hA₁_ge2 hA₂_ev hy2 (fun w hw => (hA_supp w).mp (Or.inr hw)) hA₂_e
      · by_cases hxb : x = b
        · subst hxb
          have hya : y ≠ a := fun h => hne_e (by rw [h, Sym2.eq_swap])
          rcases (hA_supp y).mpr hyC with hy1 | hy2
          · exact hshared x a y A₁.reverse A₂.reverse hbC haC hyC hab.symm hxy.symm hya hab_adj.symm hxy_adj hxy_ch hA₁.reverse hA₂.reverse (by simp [hA_len]) (by simp [hA₂_ge2]) (by simpa using hA₁_ev) (by simpa [SimpleGraph.Walk.support_reverse] using hy1) (fun w hw => (hA_supp w).mp (Or.inl (by simpa [SimpleGraph.Walk.support_reverse] using hw))) (fun e he => hA₁_e e (by simpa [SimpleGraph.Walk.edges_reverse] using he))
          · exact hshared x a y A₂.reverse A₁.reverse hbC haC hyC hab.symm hxy.symm hya hab_adj.symm hxy_adj hxy_ch hA₂.reverse hA₁.reverse (by simp; omega) (by simp [hA₁_ge2]) (by simpa using hA₂_ev) (by simpa [SimpleGraph.Walk.support_reverse] using hy2) (fun w hw => (hA_supp w).mp (Or.inr (by simpa [SimpleGraph.Walk.support_reverse] using hw))) (fun e he => hA₂_e e (by simpa [SimpleGraph.Walk.edges_reverse] using he))
        · by_cases hya : y = a
          · subst hya
            have hxb' : x ≠ b := hxb
            rcases (hA_supp x).mpr hxC with hx1 | hx2
            · exact hshared y b x A₁ A₂ haC hbC hxC hab hxy hxb' hab_adj hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₁ hA₂ hA_len hA₂_ge2 hA₁_ev hx1 (fun w hw => (hA_supp w).mp (Or.inl hw)) hA₁_e
            · exact hshared y b x A₂ A₁ haC hbC hxC hab hxy hxb' hab_adj hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₂ hA₁ (by omega) hA₁_ge2 hA₂_ev hx2 (fun w hw => (hA_supp w).mp (Or.inr hw)) hA₂_e
          · by_cases hyb : y = b
            · subst hyb
              rcases (hA_supp x).mpr hxC with hx1 | hx2
              · exact hshared y a x A₁.reverse A₂.reverse hbC haC hxC hab.symm hxy hxa hab_adj.symm hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₁.reverse hA₂.reverse (by simp [hA_len]) (by simp [hA₂_ge2]) (by simpa using hA₁_ev) (by simpa [SimpleGraph.Walk.support_reverse] using hx1) (fun w hw => (hA_supp w).mp (Or.inl (by simpa [SimpleGraph.Walk.support_reverse] using hw))) (fun e he => hA₁_e e (by simpa [SimpleGraph.Walk.edges_reverse] using he))
              · exact hshared y a x A₂.reverse A₁.reverse hbC haC hxC hab.symm hxy hxa hab_adj.symm hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₂.reverse hA₁.reverse (by simp; omega) (by simp [hA₁_ge2]) (by simpa using hA₂_ev) (by simpa [SimpleGraph.Walk.support_reverse] using hx2) (fun w hw => (hA_supp w).mp (Or.inr (by simpa [SimpleGraph.Walk.support_reverse] using hw))) (fun e he => hA₂_e e (by simpa [SimpleGraph.Walk.edges_reverse] using he))
            · -- {a, b} and {x, y} are disjoint!
              -- Helper for crossing chords: p ∈ A_u.support, q ∈ A_o.support
              have hcross : ∀ (p q : V) (A_u A_o : G.Walk a b),
                  p ∈ A_u.support → q ∈ A_o.support → p ≠ a → p ≠ b → q ≠ a → q ≠ b → p ≠ q →
                  G.Adj p q →
                  A_u.IsPath → A_o.IsPath → A_u.length + A_o.length = c.length →
                  (∀ w, w ∈ A_u.support ∨ w ∈ A_o.support ↔ w ∈ c.support) →
                  (∀ w ∈ A_u.support, w ≠ a → w ≠ b → w ∉ A_o.support) →
                  (∀ e ∈ A_u.edges, e ∈ c.edges) → (∀ e ∈ A_o.edges, e ∈ c.edges) →
                  col p = col q → False := by
                intro p q A_u A_o hpA hqA hpa hpb hqa hqb hpq hpq_adj hAu hAo hlen hsupp hdisj_ao hAu_e hAo_e hcol_pq
                let P_ap := A_u.takeUntil p hpA
                let P_pb := A_u.dropUntil p hpA
                let P_aq := A_o.takeUntil q hqA
                let P_qb := A_o.dropUntil q hqA
                have hspec_u := SimpleGraph.Walk.take_spec A_u hpA
                have hspec_o := SimpleGraph.Walk.take_spec A_o hqA
                have hsum_u : P_ap.length + P_pb.length = A_u.length := by rw [← SimpleGraph.Walk.length_append, hspec_u]
                have hsum_o : P_aq.length + P_qb.length = A_o.length := by rw [← SimpleGraph.Walk.length_append, hspec_o]
                have hPap_pos : 1 ≤ P_ap.length := by cases P_ap with | nil => exact absurd rfl hpa.symm | cons _ _ => simp
                have hPpb_pos : 1 ≤ P_pb.length := by cases P_pb with | nil => exact absurd rfl hpb | cons _ _ => simp
                have hPaq_pos : 1 ≤ P_aq.length := by cases P_aq with | nil => exact absurd rfl hqa.symm | cons _ _ => simp
                have hPqb_pos : 1 ≤ P_qb.length := by cases P_qb with | nil => exact absurd rfl hqb | cons _ _ => simp
                have hPap_e : ∀ e ∈ P_ap.edges, e ∈ c.edges := fun e he =>
                  hAu_e e (by rw [← hspec_u, SimpleGraph.Walk.edges_append, List.mem_append]; exact Or.inl he)
                have hPpb_e : ∀ e ∈ P_pb.edges, e ∈ c.edges := fun e he =>
                  hAu_e e (by rw [← hspec_u, SimpleGraph.Walk.edges_append, List.mem_append]; exact Or.inr he)
                have hPaq_e : ∀ e ∈ P_aq.edges, e ∈ c.edges := fun e he =>
                  hAo_e e (by rw [← hspec_o, SimpleGraph.Walk.edges_append, List.mem_append]; exact Or.inl he)
                have hPqb_e : ∀ e ∈ P_qb.edges, e ∈ c.edges := fun e he =>
                  hAo_e e (by rw [← hspec_o, SimpleGraph.Walk.edges_append, List.mem_append]; exact Or.inr he)
                have hpar1 := hcol_walk P_ap hPap_e
                have hpar2 := hcol_walk P_pb hPpb_e
                have hpar3 := hcol_walk P_aq hPaq_e
                have hpar4 := hcol_walk P_qb hPqb_e
                let edge_ab : G.Walk a b := SimpleGraph.Walk.cons hab_adj .nil
                have hedge_ab : edge_ab.IsPath := SimpleGraph.Walk.IsPath.mk' (by simp [edge_ab, hab])
                -- Build C₁' = P_ap ++ (p - q) ++ P_qb ++ (b - a), length = P_ap + P_qb + 2
                have hstep1 : (SimpleGraph.Walk.cons hpq_adj P_qb).IsPath :=
                  SimpleGraph.Walk.IsPath.cons (hAo.dropUntil hqA)
                    (fun hm => hdisj_ao p hpA hpa hpb (SimpleGraph.Walk.support_dropUntil_subset A_o hqA hm))
                let R1 : G.Walk a b := P_ap.append (SimpleGraph.Walk.cons hpq_adj P_qb)
                have hR1 : R1.IsPath := by
                  apply isPath_append_of_disjoint_pc P_ap _ (hAu.takeUntil hpA) hstep1
                  intro w hw1 hw2
                  rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw2
                  rcases hw2 with rfl | hw_qb
                  · rfl
                  · exfalso
                    have hw_u := SimpleGraph.Walk.support_takeUntil_subset A_u hpA hw1
                    have hw_o := SimpleGraph.Walk.support_dropUntil_subset A_o hqA hw_qb
                    by_cases hwa : w = a
                    · rw [hwa] at hw_qb
                      have hnd := hAo.support_nodup
                      rw [← hspec_o, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                      have hdrop_cons : P_qb.support = q :: P_qb.support.tail := by cases P_qb <;> simp
                      rw [hdrop_cons, List.mem_cons] at hw_qb
                      exact hnd.2.2 a (SimpleGraph.Walk.start_mem_support P_aq) a (hw_qb.resolve_left hqa.symm) rfl
                    · by_cases hwb : w = b
                      · rw [hwb] at hw1
                        have hnd := hAu.support_nodup
                        rw [← hspec_u, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                        have hdrop_cons : P_pb.support = p :: P_pb.support.tail := by cases P_pb <;> simp
                        have hb_pb : b ∈ P_pb.support := SimpleGraph.Walk.end_mem_support P_pb
                        rw [hdrop_cons, List.mem_cons] at hb_pb
                        exact hnd.2.2 b hw1 b (hb_pb.resolve_left hpb.symm) rfl
                      · exact hdisj_ao w hw_u hwa hwb hw_o
                have hC1_cyc : (R1.append edge_ab.reverse).IsCycle := by
                  apply isCycle_append_reverse_of_disjoint edge_ab R1 hedge_ab hR1 _ (by simp [R1, edge_ab, SimpleGraph.Walk.length_append]; omega)
                  intro w _ h1 h2 hw_e; simp [edge_ab] at hw_e; rcases hw_e with rfl | rfl <;> contradiction
                have hC1_ev : Even (R1.append edge_ab.reverse).length := by
                  have hlen1 : (R1.append edge_ab.reverse).length = P_ap.length + P_qb.length + 2 := by
                    simp [R1, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega
                  exact ⟨(R1.append edge_ab.reverse).length / 2, by omega⟩
                have hC1_sub : (R1.append edge_ab.reverse).support.toFinset ⊆ c.support.toFinset := by
                  intro w hw
                  have hw' := List.mem_toFinset.mp hw
                  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw'
                  rcases hw' with hR | he
                  · dsimp only [R1] at hR
                    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons, List.mem_cons] at hR
                    rcases hR with h1 | hw_eq | h2
                    · exact List.mem_toFinset.mpr ((hsupp w).mp (Or.inl (SimpleGraph.Walk.support_takeUntil_subset A_u hpA h1)))
                    · rw [hw_eq]; exact List.mem_toFinset.mpr ((hsupp p).mp (Or.inl hpA))
                    · exact List.mem_toFinset.mpr ((hsupp w).mp (Or.inr (SimpleGraph.Walk.support_dropUntil_subset A_o hqA h2)))
                  · simp [edge_ab] at he; rcases he with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
                have hle1 := hmin_len_sub _ hC1_cyc hC1_ev hC1_sub
                simp only [R1, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
                  SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle1
                -- Build C₂' = P_aq ++ (q - p) ++ P_pb ++ (b - a), length = P_aq + P_pb + 2
                have hstep2 : (SimpleGraph.Walk.cons hpq_adj.symm P_pb).IsPath :=
                  SimpleGraph.Walk.IsPath.cons (hAu.dropUntil hpA)
                    (fun hm => hdisj_ao q (SimpleGraph.Walk.support_dropUntil_subset A_u hpA hm) hqa hqb hqA)
                let R2 : G.Walk a b := P_aq.append (SimpleGraph.Walk.cons hpq_adj.symm P_pb)
                have hR2 : R2.IsPath := by
                  apply isPath_append_of_disjoint_pc P_aq _ (hAo.takeUntil hqA) hstep2
                  intro w hw1 hw2
                  rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw2
                  rcases hw2 with rfl | hw_pb
                  · rfl
                  · exfalso
                    have hw_o := SimpleGraph.Walk.support_takeUntil_subset A_o hqA hw1
                    have hw_u := SimpleGraph.Walk.support_dropUntil_subset A_u hpA hw_pb
                    by_cases hwa : w = a
                    · rw [hwa] at hw_pb
                      have hnd := hAu.support_nodup
                      rw [← hspec_u, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                      have hdrop_cons : P_pb.support = p :: P_pb.support.tail := by cases P_pb <;> simp
                      rw [hdrop_cons, List.mem_cons] at hw_pb
                      exact hnd.2.2 a (SimpleGraph.Walk.start_mem_support P_ap) a (hw_pb.resolve_left hpa.symm) rfl
                    · by_cases hwb : w = b
                      · rw [hwb] at hw1
                        have hnd := hAo.support_nodup
                        rw [← hspec_o, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
                        have hdrop_cons : P_qb.support = q :: P_qb.support.tail := by cases P_qb <;> simp
                        have hb_qb : b ∈ P_qb.support := SimpleGraph.Walk.end_mem_support P_qb
                        rw [hdrop_cons, List.mem_cons] at hb_qb
                        exact hnd.2.2 b hw1 b (hb_qb.resolve_left hqb.symm) rfl
                      · exact hdisj_ao w hw_u hwa hwb hw_o
                have hC2_cyc : (R2.append edge_ab.reverse).IsCycle := by
                  apply isCycle_append_reverse_of_disjoint edge_ab R2 hedge_ab hR2 _ (by simp [R2, edge_ab, SimpleGraph.Walk.length_append]; omega)
                  intro w _ h1 h2 hw_e; simp [edge_ab] at hw_e; rcases hw_e with rfl | rfl <;> contradiction
                have hC2_ev : Even (R2.append edge_ab.reverse).length := by
                  have hlen2 : (R2.append edge_ab.reverse).length = P_aq.length + P_pb.length + 2 := by
                    simp [R2, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega
                  exact ⟨(R2.append edge_ab.reverse).length / 2, by omega⟩
                have hC2_sub : (R2.append edge_ab.reverse).support.toFinset ⊆ c.support.toFinset := by
                  intro w hw
                  have hw' := List.mem_toFinset.mp hw
                  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw'
                  rcases hw' with hR | he
                  · dsimp only [R2] at hR
                    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons, List.mem_cons] at hR
                    rcases hR with h1 | hw_eq | h2
                    · exact List.mem_toFinset.mpr ((hsupp w).mp (Or.inr (SimpleGraph.Walk.support_takeUntil_subset A_o hqA h1)))
                    · rw [hw_eq]; exact List.mem_toFinset.mpr ((hsupp q).mp (Or.inr hqA))
                    · exact List.mem_toFinset.mpr ((hsupp w).mp (Or.inl (SimpleGraph.Walk.support_dropUntil_subset A_u hpA h2)))
                  · simp [edge_ab] at he; rcases he with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
                have hle2 := hmin_len_sub _ hC2_cyc hC2_ev hC2_sub
                simp only [R2, edge_ab, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
                  SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle2
                -- Now P_ap = P_pb = P_aq = P_qb = 1, so c.length = 4 and G[V(C)] ≅ K₄!
                have h1_ap : P_ap.length = 1 := by omega
                have h1_pb : P_pb.length = 1 := by omega
                have h1_aq : P_aq.length = 1 := by omega
                have h1_qb : P_qb.length = 1 := by omega
                have hc4 : c.length = 4 := by omega
                have h_ap : G.Adj a p := path_len_eq_one_adj P_ap h1_ap
                have h_pb : G.Adj p b := path_len_eq_one_adj P_pb h1_pb
                have h_aq : G.Adj a q := path_len_eq_one_adj P_aq h1_aq
                have h_qb : G.Adj q b := path_len_eq_one_adj P_qb h1_qb
                have hmem_len1 : ∀ {u v : V} (r : G.Walk u v), r.length = 1 → ∀ w ∈ r.support, w = u ∨ w = v := by
                  intro u v r hr w hw
                  cases r with
                  | nil => simp at hr
                  | cons _ r' => cases r' with
                    | nil => simp at hw; exact hw
                    | cons _ _ => simp at hr
                have hV_eq : ∀ w ∈ c.support, w = a ∨ w = b ∨ w = p ∨ w = q := by
                  intro w hw
                  rcases (hsupp w).mpr hw with hwu | hwo
                  · rw [← hspec_u, SimpleGraph.Walk.mem_support_append_iff] at hwu
                    rcases hwu with h1 | h2
                    · rcases hmem_len1 P_ap h1_ap w h1 with rfl | rfl <;> tauto
                    · rcases hmem_len1 P_pb h1_pb w h2 with rfl | rfl <;> tauto
                  · rw [← hspec_o, SimpleGraph.Walk.mem_support_append_iff] at hwo
                    rcases hwo with h1 | h2
                    · rcases hmem_len1 P_aq h1_aq w h1 with rfl | rfl <;> tauto
                    · rcases hmem_len1 P_qb h1_qb w h2 with rfl | rfl <;> tauto
                apply hK4
                refine ⟨hc4, fun w₁ hw₁ w₂ hw₂ hne => ?_⟩
                rcases hV_eq w₁ hw₁ with rfl | rfl | rfl | rfl <;>
                rcases hV_eq w₂ hw₂ with rfl | rfl | rfl | rfl <;>
                first
                  | exact absurd rfl hne | exact hab_adj | exact hab_adj.symm
                  | exact h_ap | exact h_ap.symm | exact h_aq | exact h_aq.symm
                  | exact h_pb | exact h_pb.symm | exact h_qb | exact h_qb.symm
                  | exact hpq_adj | exact hpq_adj.symm
              rcases (hA_supp x).mpr hxC with hx1 | hx2 <;> rcases (hA_supp y).mpr hyC with hy1 | hy2
              · rcases mem_takeUntil_or_symm A₁ hx1 hy1 with hord | hord
                · exact hnoncross x y A₁ A₂ hx1 hy1 hxa hxb hya hyb hxy hxy_adj hxy_ch hA₁ hA₂ hA_len hA₂_ge2 hA₁_ev (fun w hw => (hA_supp w).mp (Or.inl hw)) hA₁_e hord
                · exact hnoncross y x A₁ A₂ hy1 hx1 hya hyb hxa hxb hxy.symm hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₁ hA₂ hA_len hA₂_ge2 hA₁_ev (fun w hw => (hA_supp w).mp (Or.inl hw)) hA₁_e hord
              · exact hcross x y A₁ A₂ hx1 hy2 hxa hxb hya hyb hxy hxy_adj hA₁ hA₂ hA_len hA_supp hA_disj hA₁_e hA₂_e hcol_xy
              · exact hcross y x A₁ A₂ hy1 hx2 hya hyb hxa hxb hxy.symm hxy_adj.symm hA₁ hA₂ hA_len hA_supp hA_disj hA₁_e hA₂_e hcol_xy.symm
              · rcases mem_takeUntil_or_symm A₂ hx2 hy2 with hord | hord
                · exact hnoncross x y A₂ A₁ hx2 hy2 hxa hxb hya hyb hxy hxy_adj hxy_ch hA₂ hA₁ (by omega) hA₁_ge2 hA₂_ev (fun w hw => (hA_supp w).mp (Or.inr hw)) hA₂_e hord
                · exact hnoncross y x A₂ A₁ hy2 hx2 hya hyb hxa hxb hxy.symm hxy_adj.symm (by rwa [Sym2.eq_swap]) hA₂ hA₁ (by omega) hA₁_ge2 hA₂_ev (fun w hw => (hA_supp w).mp (Or.inr hw)) hA₂_e hord
  exact ⟨v, c, hc, heven, hdisj, hG_minus_C_conn, hchord_even, hchord_struct⟩

end SignedGraphs
