import SignedGraphs.Basic

/-!
# Graph-Theoretic Utilities (Cycle Splitting, Bipartiteness, and 2-Disjoint Paths)

Self-contained elementary graph-theory helpers used across Sections 3, 4, and 6:
- `cycle_arcs_of_mem`: splits any simple cycle `C` at two distinct vertices `u₁, u₂ ∈ V(C)`
  into two internally vertex-disjoint simple `(u₁, u₂)`-paths preserving total length and mod-4 weight.
- `isBipartite_iff_no_odd_cycle`: a finite simple graph is bipartite iff it contains no odd cycle.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private lemma walk_edges_perm_rotate {G : SimpleGraph V} {u v : V}
    (c : G.Walk u u) (hv : v ∈ c.support) :
    (c.rotate hv).edges.Perm c.edges := by
  have h1 : c = (c.takeUntil v hv).append (c.dropUntil v hv) := (SimpleGraph.Walk.take_spec c hv).symm
  have h2 : c.rotate hv = (c.dropUntil v hv).append (c.takeUntil v hv) := rfl
  rw [h2, SimpleGraph.Walk.edges_append]
  conv_rhs => rw [h1, SimpleGraph.Walk.edges_append]
  exact List.perm_append_comm

omit [Fintype V] [DecidableEq V] in
/-- Mod-4 weight is invariant under cycle rotation. -/
lemma walkModFourWeight_rotate {G : SimpleGraph V} (σ : Sym2 V → ℤ) {u v : V}
    (c : G.Walk u u) (hv : v ∈ c.support) :
    walkModFourWeight σ (c.rotate hv) = walkModFourWeight σ c := by
  unfold walkModFourWeight
  exact ((walk_edges_perm_rotate c hv).map (modFourWeight σ)).sum_eq

omit [Fintype V] [DecidableEq V] in
/-- Splitting a simple cycle `c` at two distinct vertices `u₁, u₂ ∈ c.support` produces
two internally vertex-disjoint simple `(u₁, u₂)`-paths `p₁, p₂` whose lengths sum to `c.length`
and whose mod-4 weights sum to `walkModFourWeight σ c`. -/
lemma cycle_arcs_of_mem {G : SimpleGraph V} {v u₁ u₂ : V}
    (c : G.Walk v v) (hc : c.IsCycle)
    (hu₁ : u₁ ∈ c.support) (hu₂ : u₂ ∈ c.support) (hne : u₁ ≠ u₂) :
    ∃ (p₁ p₂ : G.Walk u₁ u₂), p₁.IsPath ∧ p₂.IsPath ∧
      p₁.length + p₂.length = c.length ∧
      (∀ x, x ∈ p₁.support ∨ x ∈ p₂.support ↔ x ∈ c.support) ∧
      (∀ x ∈ p₁.support, x ≠ u₁ → x ≠ u₂ → x ∉ p₂.support) ∧
      (∀ σ : Sym2 V → ℤ, walkModFourWeight σ p₁ + walkModFourWeight σ p₂ =
        walkModFourWeight σ c) := by
  let c' : G.Walk u₁ u₁ := c.rotate hu₁
  have hc' : c'.IsCycle := hc.rotate hu₁
  have hsupp_eq : ∀ x, x ∈ c'.support ↔ x ∈ c.support :=
    fun x => SimpleGraph.Walk.mem_support_rotate_iff c hu₁
  have hu₂' : u₂ ∈ c'.support := (hsupp_eq u₂).mpr hu₂
  let p₁ : G.Walk u₁ u₂ := c'.takeUntil u₂ hu₂'
  let q₂ : G.Walk u₂ u₁ := c'.dropUntil u₂ hu₂'
  let p₂ : G.Walk u₁ u₂ := q₂.reverse
  have hspec : p₁.append q₂ = c' := SimpleGraph.Walk.take_spec c' hu₂'
  have hlen : p₁.length + p₂.length = c.length := by
    have h1 : p₁.length + q₂.length = c'.length := by
      rw [← SimpleGraph.Walk.length_append, hspec]
    have h2 : c'.length = c.length := SimpleGraph.Walk.length_rotate c hu₁
    rw [SimpleGraph.Walk.length_reverse]
    omega
  have hsupp_append : c'.support = p₁.support.dropLast ++ q₂.support := by
    conv_lhs => rw [← hspec]
    exact SimpleGraph.Walk.support_append p₁ q₂
  have htail_nodup : c'.support.tail.Nodup := hc'.support_nodup
  have hp₁_ne_nil : p₁ ≠ .nil := by
    intro h; cases h; exact hne rfl
  have hq₂_ne_nil : q₂ ≠ .nil := by
    intro h; cases h; exact hne rfl
  -- p₁.support = u₁ :: p₁.support.tail, and p₁.support.tail ++ q₂.support.tail = c'.support.tail
  have hsupp_tail : c'.support.tail = p₁.support.tail ++ q₂.support.tail := by
    conv_lhs => rw [← hspec]
    rw [SimpleGraph.Walk.support_append]
    cases hp₁_eq : p₁ with
    | nil => exact absurd hp₁_eq hp₁_ne_nil
    | cons hadj r =>
      simp only [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
        (SimpleGraph.Walk.support_ne_nil r), List.cons_append, List.tail_cons]
      have hq_cons : q₂.support = u₂ :: q₂.support.tail := by
        cases q₂ <;> simp
      have hr_last : r.support.dropLast ++ [u₂] = r.support := by
        have hne_r : r.support ≠ [] := SimpleGraph.Walk.support_ne_nil r
        have hlast : r.support.getLast hne_r = u₂ := SimpleGraph.Walk.getLast_support r
        simpa [hlast] using List.dropLast_append_getLast hne_r
      rw [hq_cons, ← List.singleton_append, ← List.append_assoc, hr_last]
  have hp₁_tail_nd : p₁.support.tail.Nodup := by
    rw [hsupp_tail, List.nodup_append] at htail_nodup
    exact htail_nodup.1
  have hq₂_tail_nd : q₂.support.tail.Nodup := by
    rw [hsupp_tail, List.nodup_append] at htail_nodup
    exact htail_nodup.2.1
  have hdisj_tails : ∀ x ∈ p₁.support.tail, ∀ y ∈ q₂.support.tail, x ≠ y := by
    rw [hsupp_tail, List.nodup_append] at htail_nodup
    exact htail_nodup.2.2
  have hu₁_in_q₂_tail : u₁ ∈ q₂.support.tail := by
    cases hq₂_eq : q₂ with
    | nil => exact absurd hq₂_eq hq₂_ne_nil
    | cons hadj r =>
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact SimpleGraph.Walk.end_mem_support r
  have hp₁_path : p₁.IsPath := by
    refine ⟨?_⟩
    have hp₁_cons : p₁.support = u₁ :: p₁.support.tail := by cases p₁ <;> simp
    rw [hp₁_cons, List.nodup_cons]
    refine ⟨fun hu₁_mem => hdisj_tails u₁ hu₁_mem u₁ hu₁_in_q₂_tail rfl, hp₁_tail_nd⟩
  have hu₂_in_p₁_tail : u₂ ∈ p₁.support.tail := by
    cases hp₁_eq : p₁ with
    | nil => exact absurd hp₁_eq hp₁_ne_nil
    | cons hadj r =>
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact SimpleGraph.Walk.end_mem_support r
  have hq₂_path : q₂.IsPath := by
    refine ⟨?_⟩
    have hq₂_cons : q₂.support = u₂ :: q₂.support.tail := by cases q₂ <;> simp
    rw [hq₂_cons, List.nodup_cons]
    refine ⟨fun hu₂_mem => hdisj_tails u₂ hu₂_in_p₁_tail u₂ hu₂_mem rfl, hq₂_tail_nd⟩
  refine ⟨p₁, p₂, hp₁_path, hq₂_path.reverse, hlen, ?_, ?_, ?_⟩
  · intro x
    rw [← hsupp_eq x, ← hspec, SimpleGraph.Walk.mem_support_append_iff]
    simp [p₂, SimpleGraph.Walk.support_reverse]
  · intro x hxp₁ hx1 hx2 hxp₂
    have hxp₁_tail : x ∈ p₁.support.tail := by
      have hp₁_cons : p₁.support = u₁ :: p₁.support.tail := by cases p₁ <;> simp
      rw [hp₁_cons, List.mem_cons] at hxp₁
      exact hxp₁.resolve_left hx1
    have hxq₂ : x ∈ q₂.support := by
      simpa [p₂, SimpleGraph.Walk.support_reverse] using hxp₂
    have hxq₂_tail : x ∈ q₂.support.tail := by
      have hq₂_cons : q₂.support = u₂ :: q₂.support.tail := by cases q₂ <;> simp
      rw [hq₂_cons, List.mem_cons] at hxq₂
      exact hxq₂.resolve_left hx2
    exact hdisj_tails x hxp₁_tail x hxq₂_tail rfl
  · intro σ
    have h1 : walkModFourWeight σ (p₁.append q₂) = walkModFourWeight σ c' := by rw [hspec]
    rw [SimpleGraph.Walk.edges_append] at *
    have hadd : walkModFourWeight σ (p₁.append q₂) =
        walkModFourWeight σ p₁ + walkModFourWeight σ q₂ := by
      simp [walkModFourWeight, SimpleGraph.Walk.edges_append]
    have hrev : walkModFourWeight σ p₂ = walkModFourWeight σ q₂ := by
      simp [p₂, walkModFourWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
    rw [hrev, ← hadd, h1]
    exact walkModFourWeight_rotate σ c hu₁

/-! ### Bipartiteness ↔ No Odd Cycles -/

omit [Fintype V] [DecidableEq V] in
private lemma coloring_walk_parity {G : SimpleGraph V} (f : G.Coloring (Fin 2)) :
    ∀ {u v : V} (p : G.Walk u v), f v = f u + (p.length : Fin 2)
  | _, _, .nil => by simp
  | u, _, .cons (v := w) hadj p => by
    have hne : f u ≠ f w := f.valid hadj
    have hstep : f w = f u + 1 := by
      fin_cases hu : f u <;> fin_cases hw : f w <;> simp_all
    rw [coloring_walk_parity f p, hstep, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    ring

omit [Fintype V] [DecidableEq V] in
/-- A bipartite graph contains no odd closed walk (in particular, no odd cycle). -/
lemma even_length_of_isBipartite {G : SimpleGraph V} (hbip : G.IsBipartite)
    {v : V} (c : G.Walk v v) : Even c.length := by
  rcases hbip with ⟨f⟩
  have h := coloring_walk_parity f c
  have h0 : (c.length : Fin 2) = 0 := by
    have hsub : f v + (c.length : Fin 2) - f v = f v - f v := congrArg (· - f v) h.symm
    simpa using hsub
  have hdvd : 2 ∣ c.length := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact h0
  rcases hdvd with ⟨k, hk⟩
  exact ⟨k, by omega⟩

omit [Fintype V] [DecidableEq V] in
private lemma isCycle_of_tail_nodup {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hnd : c.support.tail.Nodup) (hlen : 3 ≤ c.length) : c.IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, hnd⟩
  · -- If c.support.tail is nodup and c.length ≥ 3, then c.edges is nodup
    cases c with
    | nil => simp at hlen
    | @cons _ w _ hadj p =>
      -- p : G.Walk w v, and p.support = c.support.tail is Nodup, so p is a path!
      have hp : p.IsPath := ⟨by simpa [SimpleGraph.Walk.support_cons] using hnd⟩
      rw [SimpleGraph.Walk.edges_cons, List.nodup_cons]
      refine ⟨?_, hp.isTrail.edges_nodup⟩
      intro hmem
      have hv_mem : v ∈ p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges p hmem
      have hw_mem : w ∈ p.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges p hmem
      -- p is a path from w to v containing edge s(v, w), so p.length = 1
      have hp1 : p.length = 1 := by
        cases p with
        | nil => simp at hmem
        | @cons _ z _ hadj' q =>
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
          rcases hmem with heq | hq
          · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
            rcases heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
            · exact G.ne_of_adj hadj' rfl
            · cases q with
              | nil => rfl
              | cons hadj'' q'' =>
                have hnd' := hp.support_nodup
                simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd'
                have hv_in : v ∈ (SimpleGraph.Walk.cons hadj'' q'').support :=
                  SimpleGraph.Walk.end_mem_support _
                exact absurd (by simp [hv_in]) hnd'.2.1
          · have hw_in : w ∈ q.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges q hq
            have hnd' := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd'
            exact absurd hw_in hnd'.1
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
  · intro hnil; subst hnil; simp at hlen

omit [Fintype V] [DecidableEq V] in
/-- If a graph has no odd simple cycle, then every closed walk has even length. -/
lemma even_closed_walk_of_no_odd_cycle {G : SimpleGraph V}
    (hno : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
    ∀ (n : ℕ) (v : V) (w : G.Walk v v), w.length = n → Even w.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v w hw
    by_cases h0 : w.length = 0
    · rw [h0]; exact ⟨0, rfl⟩
    by_cases h1 : w.length = 1
    · cases w with
      | nil => simp at h1
      | cons hadj p =>
        cases p with
        | nil => exact G.ne_of_adj hadj rfl
        | cons _ _ => simp at h1
    by_cases h2 : w.length = 2
    · rw [h2]; exact ⟨1, rfl⟩
    have hge3 : 3 ≤ w.length := by omega
    by_cases hnd : w.support.tail.Nodup
    · exact hno v w (isCycle_of_tail_nodup w hnd hge3)
    · -- w.support.tail has a repeated vertex; split w into two strictly shorter closed walks
      classical
      cases w with
      | nil => simp at h0
      | @cons _ u _ hadj p =>
        simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at hnd
        have hex_dup : ∃ (x : V) (p₁ : G.Walk u x) (c : G.Walk x x) (p₂ : G.Walk x v),
            p = p₁.append (c.append p₂) ∧ 0 < c.length := by
          clear hno ih hw h0 h1 h2 hge3 hadj
          induction p with
          | nil => exact absurd (by simp) hnd
          | @cons a b d hadj' q ihq =>
            rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
            by_cases ha : a ∈ q.support
            · refine ⟨a, .nil, SimpleGraph.Walk.cons hadj' (q.takeUntil a ha), q.dropUntil a ha, ?_, ?_⟩
              · simp [SimpleGraph.Walk.take_spec]
              · simp
            · have hndq : ¬ q.support.Nodup := fun hq => hnd ⟨ha, hq⟩
              obtain ⟨x, p₁, c, p₂, hqeq, hpos⟩ := ihq hndq
              refine ⟨x, SimpleGraph.Walk.cons hadj' p₁, c, p₂, ?_, hpos⟩
              rw [hqeq]; rfl
        rcases hex_dup with ⟨x, p₁, c, p₂, hpeq, hc_pos⟩
        let w_rem : G.Walk v v := SimpleGraph.Walk.cons hadj (p₁.append p₂)
        have hlen_sum : (SimpleGraph.Walk.cons hadj p).length = w_rem.length + c.length := by
          rw [hpeq]
          simp [w_rem, SimpleGraph.Walk.length_append]
          omega
        have hw_rem_pos : 0 < w_rem.length := by simp [w_rem]
        have hc_lt : c.length < n := by omega
        have hw_lt : w_rem.length < n := by omega
        have hev_c : Even c.length := ih c.length hc_lt x c rfl
        have hev_rem : Even w_rem.length := ih w_rem.length hw_lt v w_rem rfl
        rw [hlen_sum]
        exact hev_rem.add hev_c

omit [Fintype V] [DecidableEq V] in
/-- A graph with no odd simple cycle is bipartite. -/
lemma isBipartite_of_no_odd_cycle {G : SimpleGraph V}
    (hno : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
    G.IsBipartite := by
  classical
  have hev := even_closed_walk_of_no_odd_cycle hno
  let root : V → V := fun u => Quotient.out (s := G.reachableSetoid) ⟦u⟧
  have hreach : ∀ u : V, G.Reachable (root u) u := fun u =>
    Quotient.exact (Quotient.out_eq (s := G.reachableSetoid) ⟦u⟧)
  let walkFromRoot : ∀ u : V, G.Walk (root u) u := fun u => Classical.choice (hreach u)
  refine ⟨SimpleGraph.Coloring.mk (fun u => ((walkFromRoot u).length : Fin 2)) ?_⟩
  intro u v hadj
  have hroot_eq : root u = root v := by
    simp only [root]
    congr 1
    exact Quotient.sound (SimpleGraph.Adj.reachable hadj)
  let pu : G.Walk (root u) u := walkFromRoot u
  let pv : G.Walk (root u) v := hroot_eq ▸ walkFromRoot v
  have hpv_len : pv.length = (walkFromRoot v).length := by
    cases hroot_eq; rfl
  let closed : G.Walk (root u) (root u) := pu.append (SimpleGraph.Walk.cons hadj pv.reverse)
  have hclosed_ev : Even closed.length := hev closed.length (root u) closed rfl
  have hlen : closed.length = pu.length + (walkFromRoot v).length + 1 := by
    simp [closed, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpv_len]
    omega
  rw [hlen] at hclosed_ev
  intro heq
  have hmod : pu.length % 2 = (walkFromRoot v).length % 2 := by
    have hval := congrArg Fin.val heq
    simpa [Fin.val_natCast] using hval
  rcases hclosed_ev with ⟨k, hk⟩
  omega

/-! ### Menger's Theorem for `k = 2` (Two Vertex-Disjoint Paths Between Sets) -/

omit [Fintype V] in
private lemma exists_shortest_ab_path (G : SimpleGraph V) (A B S : Finset V)
    (hex : ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∉ S) :
    ∃ (a b : V) (p : G.Walk a b),
      a ∈ A ∧ b ∈ B ∧ p.IsPath ∧
      (∀ x ∈ p.support, x ∉ S) ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ A ∧ x ∉ B) := by
  classical
  have hex_len : ∃ k : ℕ, ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      (∀ x ∈ p.support, x ∉ S) ∧ p.length = k := by
    rcases hex with ⟨a, ha, b, hb, p, hp⟩
    exact ⟨p.length, a, ha, b, hb, p, hp, rfl⟩
  let k := Nat.find hex_len
  obtain ⟨a, ha, b, hb, p, hpS, hplen⟩ := Nat.find_spec hex_len
  have hmin : ∀ (a' b' : V), a' ∈ A → b' ∈ B → ∀ (q : G.Walk a' b'),
      (∀ x ∈ q.support, x ∉ S) → p.length ≤ q.length := by
    intro a' b' ha' hb' q hqS
    rw [hplen]
    exact Nat.find_min' hex_len ⟨a', ha', b', hb', q, hqS, rfl⟩
  let p' := p.toPath.1
  have hp'_path : p'.IsPath := p.toPath.2
  have hp'S : ∀ x ∈ p'.support, x ∉ S := fun x hx =>
    hpS x (SimpleGraph.Walk.support_toPath_subset p hx)
  have hp'_len : p'.length = p.length :=
    le_antisymm (SimpleGraph.Walk.length_toPath_le p) (hmin a b ha hb p' hp'S)
  have hmin' : ∀ (a' b' : V), a' ∈ A → b' ∈ B → ∀ (q : G.Walk a' b'),
      (∀ x ∈ q.support, x ∉ S) → p'.length ≤ q.length := by
    intro a' b' ha' hb' q hqS; rw [hp'_len]; exact hmin a' b' ha' hb' q hqS
  refine ⟨a, b, p', ha, hb, hp'_path, hp'S, ?_⟩
  intro x hxp hxa hxb
  constructor
  · intro hxA
    let q := p'.dropUntil x hxp
    have hqS : ∀ y ∈ q.support, y ∉ S := fun y hy =>
      hp'S y (SimpleGraph.Walk.support_dropUntil_subset p hxp hy)
    have hle := hmin' x b hxA hb q hqS
    have hlt : q.length < p'.length := by
      have hspec := SimpleGraph.Walk.take_spec p' hxp
      have hsum : (p'.takeUntil x hxp).length + q.length = p'.length := by
        rw [← SimpleGraph.Walk.length_append, hspec]
      have htpos : 0 < (p'.takeUntil x hxp).length := by
        cases ht : p'.takeUntil x hxp with
        | nil => exact absurd rfl hxa
        | cons _ _ => simp
      omega
    omega
  · intro hxB
    let q := p'.takeUntil x hxp
    have hqS : ∀ y ∈ q.support, y ∉ S := fun y hy =>
      hp'S y (SimpleGraph.Walk.support_takeUntil_subset p hxp hy)
    have hle := hmin' a x ha hxB q hqS
    have hlt : q.length < p'.length := by
      have hspec := SimpleGraph.Walk.take_spec p' hxp
      have hsum : q.length + (p'.dropUntil x hxp).length = p'.length := by
        rw [← SimpleGraph.Walk.length_append, hspec]
      have hdpos : 0 < (p'.dropUntil x hxp).length := by
        cases hd : p'.dropUntil x hxp with
        | nil => exact absurd rfl hxb.symm
        | cons _ _ => simp
      omega
    omega

private lemma walk_exits_finset {G : SimpleGraph V} (S : Finset V) {a b : V}
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

private lemma walk_prefix_to_set {G : SimpleGraph V} (T : Finset V) {a b : V}
    (p : G.Walk a b) (hex : ∃ t ∈ T, t ∈ p.support) :
    ∃ t ∈ T, ∃ q : G.Walk a t,
      (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ q.support.dropLast, x ∉ T) := by
  induction p with
  | nil =>
    rcases hex with ⟨t, htT, ht⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
    subst ht
    exact ⟨t, htT, .nil, fun x hx => by simpa using hx, fun x hx => by simp at hx⟩
  | @cons x y z hxy r ih =>
    by_cases hxT : x ∈ T
    · exact ⟨x, hxT, .nil, fun v hv => by simp at hv; subst hv; exact List.mem_cons_self ..,
        fun v hv => by simp at hv⟩
    · have hex' : ∃ t ∈ T, t ∈ r.support := by
        rcases hex with ⟨t, htT, ht⟩
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | htr
        · exact absurd htT hxT
        · exact ⟨t, htT, htr⟩
      obtain ⟨t, htT, q, hqsub, hqint⟩ := ih hex'
      refine ⟨t, htT, SimpleGraph.Walk.cons hxy q, ?_, ?_⟩
      · intro v hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hvq
        · exact Or.inl rfl
        · exact Or.inr (hqsub v hvq)
      · intro v hv
        rw [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil q),
          List.mem_cons] at hv
        rcases hv with rfl | hvq
        · exact hxT
        · exact hqint v hvq

private lemma trim_ab_path {G : SimpleGraph V} (A B : Finset V) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : G.Walk a b) :
    ∃ a' ∈ A, ∃ b' ∈ B, ∃ q : G.Walk a' b',
      q.IsPath ∧ (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ q.support, x ≠ a' → x ≠ b' → x ∉ A ∧ x ∉ B) := by
  classical
  obtain ⟨b', hb'B, q₁, hq₁_sub, hq₁_int⟩ :=
    walk_prefix_to_set B p ⟨b, hb, SimpleGraph.Walk.end_mem_support p⟩
  let q₁p := q₁.toPath
  have hq₁p_sub : ∀ x ∈ q₁p.1.support, x ∈ q₁.support := fun x hx =>
    SimpleGraph.Walk.support_toPath_subset q₁ hx
  have hq₁p_notB : ∀ x ∈ q₁p.1.support, x ≠ b' → x ∉ B := by
    intro x hx hxb
    have hx1 : x ∈ q₁.support := hq₁p_sub x hx
    have hne : q₁.support ≠ [] := SimpleGraph.Walk.support_ne_nil q₁
    have hlast : q₁.support.getLast hne = b' := SimpleGraph.Walk.getLast_support q₁
    have hsplit := List.dropLast_append_getLast hne
    rw [hlast] at hsplit
    have hx' : x ∈ q₁.support.dropLast ++ [b'] := by rwa [hsplit]
    rw [List.mem_append, List.mem_singleton] at hx'
    exact hq₁_int x (hx'.resolve_right hxb)
  obtain ⟨a', ha'A, q₂rev, hq₂_sub, hq₂_int⟩ :=
    walk_prefix_to_set A q₁p.1.reverse ⟨a, ha, by simp [SimpleGraph.Walk.support_reverse]⟩
  let q := q₂rev.reverse.toPath
  have hq_sub_q₂ : ∀ x ∈ q.1.support, x ∈ q₂rev.support := by
    intro x hx
    have h1 := SimpleGraph.Walk.support_toPath_subset q₂rev.reverse hx
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
  have hq_sub_q₁p : ∀ x ∈ q.1.support, x ∈ q₁p.1.support := by
    intro x hx
    have h2 := hq₂_sub x (hq_sub_q₂ x hx)
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h2
  refine ⟨a', ha'A, b', hb'B, q.1, q.2, fun x hx => hq₁_sub x (hq₁p_sub x (hq_sub_q₁p x hx)), ?_⟩
  intro x hx hxa hxb
  constructor
  · have hx2 : x ∈ q₂rev.support := hq_sub_q₂ x hx
    have hne : q₂rev.support ≠ [] := SimpleGraph.Walk.support_ne_nil q₂rev
    have hlast : q₂rev.support.getLast hne = a' := SimpleGraph.Walk.getLast_support q₂rev
    have hsplit := List.dropLast_append_getLast hne
    rw [hlast] at hsplit
    have hx' : x ∈ q₂rev.support.dropLast ++ [a'] := by rwa [hsplit]
    rw [List.mem_append, List.mem_singleton] at hx'
    exact hq₂_int x (hx'.resolve_right hxa)
  · exact hq₁p_notB x (hq_sub_q₁p x hx) hxb

private lemma isPath_append_of_disjoint {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x ∈ p.support, x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  refine SimpleGraph.Walk.IsPath.mk' ?_
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup.sublist (List.dropLast_sublist _), hq.support_nodup, ?_⟩
  intro x hxp y hyq hxy
  subst hxy
  have hne : p.support ≠ [] := SimpleGraph.Walk.support_ne_nil p
  have hlast : p.support.getLast hne = b := SimpleGraph.Walk.getLast_support p
  have hxb : x = b := hdisj x (List.dropLast_subset _ hxp) hyq
  subst hxb
  have hnd := hp.support_nodup
  rw [← List.dropLast_append_getLast hne, hlast, List.nodup_append] at hnd
  exact hnd.2.2 x hxp x (List.mem_singleton_self x) rfl

private lemma walk_lift_le {G H : SimpleGraph V} (hle : G ≤ H) {u v : V}
    (p : G.Walk u v) :
    ∃ q : H.Walk u v, q.support = p.support ∧ q.length = p.length :=
  ⟨p.map (SimpleGraph.Hom.ofLE hle), by simp, by simp⟩

/-- **Menger's Theorem for `k = 2`**: If `A, B : Finset V` have no 1-vertex separator in `G`
(and `2 ≤ A.card`, `2 ≤ B.card`), then `G` contains two vertex-disjoint simple paths
`p₁ : G.Walk a₁ b₁` and `p₂ : G.Walk a₂ b₂` from `A` to `B`, internally disjoint from `A ∪ B`. -/
open Classical in
theorem two_disjoint_paths_between_sets :
    ∀ (m : ℕ) (G : SimpleGraph V) (A B : Finset V),
      (Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet).card = m →
      2 ≤ A.card → 2 ≤ B.card →
      (∀ v : V, ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, v ∉ p.support) →
      ∃ (a₁ a₂ b₁ b₂ : V) (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂),
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧ a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
        p₁.IsPath ∧ p₂.IsPath ∧
        Disjoint p₁.support.toFinset p₂.support.toFinset ∧
        (∀ x ∈ p₁.support, x ≠ a₁ → x ≠ b₁ → x ∉ A ∧ x ∉ B) ∧
        (∀ x ∈ p₂.support, x ≠ a₂ → x ≠ b₂ → x ∉ A ∧ x ∉ B) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    classical
    intro G A B hm hA hB hno_cut
    -- Case 0: A ∩ B is nonempty
    by_cases hinter : (A ∩ B).Nonempty
    · rcases hinter with ⟨v, hv⟩
      have hvA : v ∈ A := (Finset.mem_inter.mp hv).1
      have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
      have hex2 : ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∉ ({v} : Finset V) := by
        rcases hno_cut v with ⟨a, ha, b, hb, p, hvp⟩
        exact ⟨a, ha, b, hb, p, fun x hx hxv => hvp ((Finset.mem_singleton.mp hxv) ▸ hx)⟩
      obtain ⟨a₂, b₂, p₂, ha₂, hb₂, hp₂, hp₂v, hp₂_int⟩ := exists_shortest_ab_path G A B {v} hex2
      have hvn2 : v ∉ p₂.support := fun h => hp₂v v h (Finset.mem_singleton_self v)
      have hne_a : v ≠ a₂ := fun h => hvn2 (h ▸ SimpleGraph.Walk.start_mem_support p₂)
      have hne_b : v ≠ b₂ := fun h => hvn2 (h ▸ SimpleGraph.Walk.end_mem_support p₂)
      refine ⟨v, a₂, v, b₂, .nil, p₂, hvA, ha₂, hvB, hb₂, hne_a, hne_b,
        SimpleGraph.Walk.IsPath.nil, hp₂, ?_, ?_, hp₂_int⟩
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [SimpleGraph.Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton] at hx1
        subst hx1
        exact hvn2 (List.mem_toFinset.mp hx2)
      · intro x hx h1 _; simp at hx; exact absurd hx h1
    · have hAB_disj : Disjoint A B := Finset.not_nonempty_iff_eq_empty.mp hinter |> Finset.disjoint_iff_inter_eq_empty.mpr
      -- Case 1: There is a direct edge between A and B
      by_cases hedge : ∃ a ∈ A, ∃ b ∈ B, G.Adj a b
      · rcases hedge with ⟨a, ha, b, hb, hadj⟩
        have hab : a ≠ b := G.ne_of_adj hadj
        let p_ab : G.Walk a b := SimpleGraph.Walk.cons hadj .nil
        have hp_ab_path : p_ab.IsPath := by
          refine ⟨?_⟩; simp [p_ab, hab]
        have hp_ab_int : ∀ x ∈ p_ab.support, x ≠ a → x ≠ b → x ∉ A ∧ x ∉ B := by
          intro x hx hxa hxb; simp [p_ab] at hx; rcases hx with rfl | rfl <;> contradiction
        -- Find shortest A-B path avoiding a
        have hex1 : ∃ a' ∈ A, ∃ b' ∈ B, ∃ p : G.Walk a' b', ∀ x ∈ p.support, x ∉ ({a} : Finset V) := by
          rcases hno_cut a with ⟨a', ha', b', hb', p, hap⟩
          exact ⟨a', ha', b', hb', p, fun x hx hxa => hap ((Finset.mem_singleton.mp hxa) ▸ hx)⟩
        obtain ⟨a₁, b₁, p₁, ha₁, hb₁, hp₁, hp₁a, hp₁_int⟩ := exists_shortest_ab_path G A B {a} hex1
        have ha_n1 : a ∉ p₁.support := fun h => hp₁a a h (Finset.mem_singleton_self a)
        by_cases hb_in1 : b ∈ p₁.support
        · -- b ∈ p₁.support, so b₁ = b. Now find shortest A-B path avoiding b.
          have hb₁_eq : b₁ = b := by
            by_contra hne
            have hba₁ : b ≠ a₁ := fun h => Finset.disjoint_left.mp hAB_disj (h ▸ ha₁) hb
            exact (hp₁_int b hb_in1 hba₁ (Ne.symm hne)).2 hb
          have hex2 : ∃ a' ∈ A, ∃ b' ∈ B, ∃ p : G.Walk a' b', ∀ x ∈ p.support, x ∉ ({b} : Finset V) := by
            rcases hno_cut b with ⟨a', ha', b', hb', p, hbp⟩
            exact ⟨a', ha', b', hb', p, fun x hx hxb => hbp ((Finset.mem_singleton.mp hxb) ▸ hx)⟩
          obtain ⟨a₂, b₂, p₂, ha₂, hb₂, hp₂, hp₂b, hp₂_int⟩ := exists_shortest_ab_path G A B {b} hex2
          have hb_n2 : b ∉ p₂.support := fun h => hp₂b b h (Finset.mem_singleton_self b)
          by_cases ha_in2 : a ∈ p₂.support
          · have ha₂_eq : a₂ = a := by
              by_contra hne
              have hab₂ : a ≠ b₂ := fun h => Finset.disjoint_left.mp hAB_disj ha (h ▸ hb₂)
              exact (hp₂_int a ha_in2 (Ne.symm hne) hab₂).1 ha
            by_cases hdisj12 : Disjoint p₁.support.toFinset p₂.support.toFinset
            · have ha12 : a₁ ≠ a₂ := by
                intro h
                have hmem : a₁ ∈ p₁.support := SimpleGraph.Walk.start_mem_support p₁
                rw [h, ha₂_eq] at hmem
                exact ha_n1 hmem
              have hb12 : b₁ ≠ b₂ := by
                intro h
                have hmem : b₂ ∈ p₂.support := SimpleGraph.Walk.end_mem_support p₂
                rw [← h, hb₁_eq] at hmem
                exact hb_n2 hmem
              exact ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, ha12, hb12, hp₁, hp₂, hdisj12, hp₁_int, hp₂_int⟩
            · -- p₁ and p₂ share some vertex z; combine prefix of p₁ with suffix of p₂ avoiding {a, b}
              rw [Finset.not_disjoint_iff] at hdisj12
              rcases hdisj12 with ⟨z, hz1, hz2⟩
              have hz1' : z ∈ p₁.support := List.mem_toFinset.mp hz1
              have hz2' : z ∈ p₂.support := List.mem_toFinset.mp hz2
              have hza : z ≠ a := fun h => ha_n1 (h ▸ hz1')
              have hzb : z ≠ b := fun h => hb_n2 (h ▸ hz2')
              let q : G.Walk a₁ b₂ := (p₁.takeUntil z hz1').append (p₂.dropUntil z hz2')
              have hq_ab : ∀ x ∈ q.support, x ∉ ({a, b} : Finset V) := by
                intro x hx hxab
                rw [SimpleGraph.Walk.mem_support_append_iff] at hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
                rcases hx with hx1 | hx2
                · rcases hxab with rfl | rfl
                  · exact ha_n1 (SimpleGraph.Walk.support_takeUntil_subset p₁ hz1' hx1)
                  · -- x (= b) ∈ (p₁.takeUntil z hz1').support; since b = b₁ and p₁ is a path, x = z!
                    have hspec := SimpleGraph.Walk.take_spec p₁ hz1'
                    have hnd := hp₁.support_nodup
                    rw [← hspec, SimpleGraph.Walk.support_append] at hnd
                    have hb_in_drop : x ∈ (p₁.dropUntil z hz1').support := by
                      rw [← hb₁_eq]; exact SimpleGraph.Walk.end_mem_support _
                    have hb_eq_z : x = z := by
                      by_contra hbz
                      have hne_take : (p₁.takeUntil z hz1').support ≠ [] :=
                        SimpleGraph.Walk.support_ne_nil _
                      have hlast : (p₁.takeUntil z hz1').support.getLast hne_take = z :=
                        SimpleGraph.Walk.getLast_support _
                      have hb_dropLast : x ∈ (p₁.takeUntil z hz1').support.dropLast := by
                        have hsplit := List.dropLast_append_getLast hne_take
                        rw [hlast] at hsplit
                        have hx1' : x ∈ (p₁.takeUntil z hz1').support.dropLast ++ [z] := by
                          rwa [hsplit]
                        rw [List.mem_append, List.mem_singleton] at hx1'
                        exact hx1'.resolve_right hbz
                      rw [List.nodup_append] at hnd
                      exact hnd.2.2 x hb_dropLast x hb_in_drop rfl
                    exact hzb hb_eq_z.symm
                · rcases hxab with rfl | rfl
                  · -- x (= a) ∈ (p₂.dropUntil z hz2').support; since a = a₂ and p₂ is a path, x = z!
                    have hspec := SimpleGraph.Walk.take_spec p₂ hz2'
                    have hnd := hp₂.support_nodup
                    rw [← hspec, SimpleGraph.Walk.support_append] at hnd
                    have ha_eq_z : x = z := by
                      by_contra haz
                      have hne_take : (p₂.takeUntil z hz2').support ≠ [] :=
                        SimpleGraph.Walk.support_ne_nil _
                      have hlast : (p₂.takeUntil z hz2').support.getLast hne_take = z :=
                        SimpleGraph.Walk.getLast_support _
                      have ha_in_take : x ∈ (p₂.takeUntil z hz2').support := by
                        rw [← ha₂_eq]; exact SimpleGraph.Walk.start_mem_support _
                      have ha_dropLast : x ∈ (p₂.takeUntil z hz2').support.dropLast := by
                        have hsplit := List.dropLast_append_getLast hne_take
                        rw [hlast] at hsplit
                        have ha' : x ∈ (p₂.takeUntil z hz2').support.dropLast ++ [z] := by
                          rwa [hsplit]
                        rw [List.mem_append, List.mem_singleton] at ha'
                        exact ha'.resolve_right haz
                      rw [List.nodup_append] at hnd
                      exact hnd.2.2 x ha_dropLast x hx2 rfl
                    exact hza ha_eq_z.symm
                  · exact hb_n2 (SimpleGraph.Walk.support_dropUntil_subset p₂ hz2' hx2)
              obtain ⟨a', b', q', ha', hb', hq'_path, hq'_ab, hq'_int⟩ :=
                exists_shortest_ab_path G A B {a, b} ⟨a₁, ha₁, b₂, hb₂, q, hq_ab⟩
              have ha_nq' : a ∉ q'.support := fun h => hq'_ab a h (by simp)
              have hb_nq' : b ∉ q'.support := fun h => hq'_ab b h (by simp)
              refine ⟨a, a', b, b', p_ab, q', ha, ha', hb, hb',
                fun h => ha_nq' (h ▸ SimpleGraph.Walk.start_mem_support q'),
                fun h => hb_nq' (h ▸ SimpleGraph.Walk.end_mem_support q'),
                hp_ab_path, hq'_path, ?_, hp_ab_int, hq'_int⟩
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              simp only [p_ab, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
                List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hx1
              rcases hx1 with rfl | rfl
              · exact ha_nq' (List.mem_toFinset.mp hx2)
              · exact hb_nq' (List.mem_toFinset.mp hx2)
          · -- a ∉ p₂.support and b ∉ p₂.support: p_ab and p₂ are disjoint!
            refine ⟨a, a₂, b, b₂, p_ab, p₂, ha, ha₂, hb, hb₂,
              fun h => ha_in2 (h ▸ SimpleGraph.Walk.start_mem_support p₂),
              fun h => hb_n2 (h ▸ SimpleGraph.Walk.end_mem_support p₂),
              hp_ab_path, hp₂, ?_, hp_ab_int, hp₂_int⟩
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            simp only [p_ab, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hx1
            rcases hx1 with rfl | rfl
            · exact ha_in2 (List.mem_toFinset.mp hx2)
            · exact hb_n2 (List.mem_toFinset.mp hx2)
        · -- b ∉ p₁.support and a ∉ p₁.support: p_ab and p₁ are disjoint!
          refine ⟨a, a₁, b, b₁, p_ab, p₁, ha, ha₁, hb, hb₁,
            fun h => ha_n1 (h ▸ SimpleGraph.Walk.start_mem_support p₁),
            fun h => hb_in1 (h ▸ SimpleGraph.Walk.end_mem_support p₁),
            hp_ab_path, hp₁, ?_, hp_ab_int, hp₁_int⟩
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [p_ab, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hx1
          rcases hx1 with rfl | rfl
          · exact ha_n1 (List.mem_toFinset.mp hx2)
          · exact hb_in1 (List.mem_toFinset.mp hx2)
      · -- Case 2: Disjoint A B and no direct edge between A and B
        by_cases hred : ∃ e ∈ G.edgeSet, ∀ v : V, ∃ a ∈ A, ∃ b ∈ B,
            ∃ p : (G.deleteEdges {e}).Walk a b, v ∉ p.support
        · rcases hred with ⟨e, heG, hno_cut'⟩
          let G' := G.deleteEdges {e}
          have hlt : (Finset.univ.filter fun e' : Sym2 V => e' ∈ G'.edgeSet).card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨?_, ?_⟩
            · intro e' he'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, G',
                SimpleGraph.edgeSet_deleteEdges, Set.mem_diff] at he' ⊢
              exact he'.1
            · intro heq
              have hmem : e ∈ Finset.univ.filter (fun e' : Sym2 V => e' ∈ G'.edgeSet) := by
                rw [heq]; simp [heG]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, G',
                SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at hmem
              exact hmem.2 trivial
          obtain ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, ha12, hb12, hp₁, hp₂, hdisj, hi₁, hi₂⟩ :=
            ih _ hlt G' A B (by congr 1; ext e; simp) hA hB hno_cut'
          let φ : G' →g G := SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le {e})
          refine ⟨a₁, a₂, b₁, b₂, p₁.map φ, p₂.map φ, ha₁, ha₂, hb₁, hb₂, ha12, hb12,
            hp₁.map (fun _ _ h => h), hp₂.map (fun _ _ h => h), ?_, ?_, ?_⟩
          · simpa [SimpleGraph.Walk.support_map] using hdisj
          · intro x hx; simpa [SimpleGraph.Walk.support_map] using hi₁ x (by simpa [SimpleGraph.Walk.support_map] using hx)
          · intro x hx; simpa [SimpleGraph.Walk.support_map] using hi₂ x (by simpa [SimpleGraph.Walk.support_map] using hx)
        · -- Every edge of G is critical for hno_cut!
          push Not at hred
          -- First get an edge e = s(u, v) of G (must exist since A ≠ ∅, B ≠ ∅, Disjoint A B)
          obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
          rcases hno_cut a₀ with ⟨a', ha', b', hb', p0, _⟩
          have hex_e : ∃ u v : V, G.Adj u v := by
            cases p0 with
            | nil => exact False.elim (Finset.disjoint_left.mp hAB_disj ha' hb')
            | cons hadj _ => exact ⟨_, _, hadj⟩
          rcases hex_e with ⟨u, v, huv⟩
          have huv_mem : s(u, v) ∈ G.edgeSet := huv
          rcases hred s(u, v) huv_mem with ⟨w, hw_cut⟩
          let G' := G.deleteEdges {s(u, v)}
          have hwu : w ≠ u := by
            rintro rfl
            rcases hno_cut w with ⟨a, ha, b, hb, p, hwp⟩
            have hp' : ∀ e ∈ p.edges, e ≠ s(w, v) := by
              intro e he heq
              rw [heq] at he
              exact hwp (SimpleGraph.Walk.fst_mem_support_of_mem_edges p he)
            let q : G'.Walk a b := p.transfer G' (fun e he => by
              rw [SimpleGraph.edgeSet_deleteEdges]
              exact ⟨p.edges_subset_edgeSet he, fun h => hp' e he (Set.mem_singleton_iff.mp h)⟩)
            have hmem := hw_cut a ha b hb q
            rw [SimpleGraph.Walk.support_transfer] at hmem
            exact hwp hmem
          have hwv : w ≠ v := by
            rintro rfl
            rcases hno_cut w with ⟨a, ha, b, hb, p, hwp⟩
            have hp' : ∀ e ∈ p.edges, e ≠ s(u, w) := by
              intro e he heq
              rw [heq] at he
              exact hwp (SimpleGraph.Walk.snd_mem_support_of_mem_edges p he)
            let q : G'.Walk a b := p.transfer G' (fun e he => by
              rw [SimpleGraph.edgeSet_deleteEdges]
              exact ⟨p.edges_subset_edgeSet he, fun h => hp' e he (Set.mem_singleton_iff.mp h)⟩)
            have hmem := hw_cut a ha b hb q
            rw [SimpleGraph.Walk.support_transfer] at hmem
            exact hwp hmem
          -- Define C_A: all vertices reachable from A \ {w} in G' - w
          let C_A : Finset V := Finset.univ.filter fun z =>
            ∃ hz : z ∈ ({w}ᶜ : Set V), ∃ a ∈ A, ∃ ha : a ∈ ({w}ᶜ : Set V),
              (G'.induce ({w}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨z, hz⟩
          have hA_sub_CA : ∀ a ∈ A, a ≠ w → a ∈ C_A := by
            intro a ha haw
            simp only [C_A, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨haw, a, ha, haw, SimpleGraph.Reachable.refl _⟩
          have hw_not_CA : w ∉ C_A := by
            simp only [C_A, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
            intro h; exact absurd rfl h
          have hB_not_CA : ∀ b ∈ B, b ≠ w → b ∉ C_A := by
            intro b hb hbw hbCA
            simp only [C_A, Finset.mem_filter, Finset.mem_univ, true_and] at hbCA
            rcases hbCA with ⟨_, a, ha, haw, ⟨p'⟩⟩
            let f : (G'.induce ({w}ᶜ : Set V)) →g G' := (SimpleGraph.Embedding.induce ({w}ᶜ : Set V)).toHom
            have hwn : w ∉ (p'.map f).support := by
              intro hm
              rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
              rcases hm with ⟨x, _, hxw⟩
              exact x.2 (Set.mem_singleton_iff.mpr hxw)
            exact hwn (hw_cut a ha b hb (p'.map f))
          have hCA_closed : ∀ x ∈ C_A, ∀ y : V, G'.Adj x y → y ≠ w → y ∈ C_A := by
            intro x hx y hadj hyw
            simp only [C_A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            rcases hx with ⟨hxw, a, ha, haw, hreach⟩
            exact ⟨hyw, a, ha, haw, hreach.trans
              (SimpleGraph.Adj.reachable (show (G'.induce ({w}ᶜ : Set V)).Adj ⟨x, hxw⟩ ⟨y, hyw⟩ from hadj))⟩
          have hcross_uv : (u ∈ C_A ∧ v ∉ C_A) ∨ (v ∈ C_A ∧ u ∉ C_A) := by
            rcases hno_cut w with ⟨a, ha, b, hb, p, hwp⟩
            have haw : a ≠ w := fun h => hwp (h ▸ SimpleGraph.Walk.start_mem_support p)
            have hbw : b ≠ w := fun h => hwp (h ▸ SimpleGraph.Walk.end_mem_support p)
            obtain ⟨x, hxCA, y, hyCA, hxy, hxp, hyp⟩ :=
              walk_exits_finset C_A p (hA_sub_CA a ha haw) (hB_not_CA b hb hbw)
            have hyw : y ≠ w := fun h => hwp (h ▸ hyp)
            have hxy_eq : s(x, y) = s(u, v) := by
              by_contra hne
              have hadj' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun h => hne (Set.mem_singleton_iff.mp h)⟩
              exact hyCA (hCA_closed x hxCA y hadj' hyw)
            rcases Sym2.eq_iff.mp hxy_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨hxCA, hyCA⟩
            · exact Or.inr ⟨hxCA, hyCA⟩
          have hex_uv' : ∃ u' v' : V, G.Adj u' v' ∧ u' ≠ w ∧ v' ≠ w ∧
              s(u', v') = s(u, v) ∧ u' ∈ C_A ∧ v' ∉ C_A := by
            rcases hcross_uv with ⟨huCA, hvCA⟩ | ⟨hvCA, huCA⟩
            · exact ⟨u, v, huv, hwu.symm, hwv.symm, rfl, huCA, hvCA⟩
            · exact ⟨v, u, huv.symm, hwv.symm, hwu.symm, Sym2.eq_swap, hvCA, huCA⟩
          rcases hex_uv' with ⟨u', v', huv', hu'w, hv'w, hsuv', hu'CA, hv'CA⟩
          let C_B : Finset V := (Finset.univ.erase w) \ C_A
          have hv'CB : v' ∈ C_B := by simp [C_B, hv'w, hv'CA]
          have hw_not_CB : w ∉ C_B := by simp [C_B]
          have hCA_CB_disj : Disjoint C_A C_B := by
            rw [Finset.disjoint_right]; intro z hz; exact (Finset.mem_sdiff.mp hz).2
          have hB_sub_CB : ∀ b ∈ B, b ≠ w → b ∈ C_B := fun b hb hbw => by
            simp [C_B, hbw, hB_not_CA b hb hbw]
          have hCB_closed : ∀ x ∈ C_B, ∀ y : V, G'.Adj x y → y ≠ w → y ∈ C_B := by
            intro x hx y hadj hyw
            simp only [C_B, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
            refine ⟨hyw, fun hyCA => hx.2 (hCA_closed y hyCA x hadj.symm hx.1)⟩
          let G_A : SimpleGraph V :=
            { Adj := fun x y => G.Adj x y ∧ x ∈ C_A ∪ {w} ∧ y ∈ C_A ∪ {w}
              symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
              loopless := ⟨fun x ⟨h1, _, _⟩ => G.ne_of_adj h1 rfl⟩ }
          let G_B : SimpleGraph V :=
            { Adj := fun x y => G.Adj x y ∧ x ∈ C_B ∪ {w} ∧ y ∈ C_B ∪ {w}
              symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
              loopless := ⟨fun x ⟨h1, _, _⟩ => G.ne_of_adj h1 rfl⟩ }
          have hGA_le : G_A ≤ G := fun _ _ h => h.1
          have hGB_le : G_B ≤ G := fun _ _ h => h.1
          have hGA_lt : (Finset.univ.filter fun e' : Sym2 V => e' ∈ G_A.edgeSet).card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => ?_, fun heq => ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he' ⊢
              exact SimpleGraph.edgeSet_mono hGA_le he'
            · have hmem : s(u', v') ∈ Finset.univ.filter (fun e' : Sym2 V => e' ∈ G_A.edgeSet) := by
                rw [heq]; simp [huv']
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              have hv'mem : v' ∈ C_A ∪ {w} := hmem.2.2
              simp [hv'CA, hv'w] at hv'mem
          have hGB_lt : (Finset.univ.filter fun e' : Sym2 V => e' ∈ G_B.edgeSet).card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => ?_, fun heq => ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he' ⊢
              exact SimpleGraph.edgeSet_mono hGB_le he'
            · have hmem : s(u', v') ∈ Finset.univ.filter (fun e' : Sym2 V => e' ∈ G_B.edgeSet) := by
                rw [heq]; simp [huv']
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              have hu'mem : u' ∈ C_B ∪ {w} := hmem.2.1
              have hu'nCB : u' ∉ C_B := Finset.disjoint_left.mp hCA_CB_disj hu'CA
              simp [hu'nCB, hu'w] at hu'mem
          have hGA_no_cut : ∀ z : V, ∃ a ∈ A, ∃ t ∈ ({w, u'} : Finset V), ∃ q : G_A.Walk a t, z ∉ q.support := by
            intro z
            rcases hno_cut z with ⟨a, ha, b, hb, p, hzp⟩
            have hex_hit : ∃ t ∈ ({w, u'} : Finset V), t ∈ p.support := by
              by_contra hnone
              push Not at hnone
              have hwn : w ∉ p.support := fun h => hnone w (by simp) h
              have hu'n : u' ∉ p.support := fun h => hnone u' (by simp) h
              have haw : a ≠ w := fun h => hwn (h ▸ SimpleGraph.Walk.start_mem_support p)
              have hbw : b ≠ w := fun h => hwn (h ▸ SimpleGraph.Walk.end_mem_support p)
              obtain ⟨x, hxCA, y, hyCA, hxy, hxp, hyp⟩ :=
                walk_exits_finset C_A p (hA_sub_CA a ha haw) (hB_not_CA b hb hbw)
              have hyw : y ≠ w := fun h => hwn (h ▸ hyp)
              have hxy_eq : s(x, y) = s(u', v') := by
                by_contra hne
                have hadj' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun h => hne (hsuv'.symm ▸ Set.mem_singleton_iff.mp h)⟩
                exact hyCA (hCA_closed x hxCA y hadj' hyw)
              rcases Sym2.eq_iff.mp hxy_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hu'n hxp
              · exact hu'n hyp
            obtain ⟨t, ht, q, hqsub, hqint⟩ := walk_prefix_to_set {w, u'} p hex_hit
            have ha_in : a ∈ C_A ∪ {w} := by
              by_cases haw : a = w
              · exact Finset.mem_union_right _ (by simp [haw])
              · exact Finset.mem_union_left _ (hA_sub_CA a ha haw)
            have hlift_GA : ∀ {s t₀ : V} (r : G.Walk s t₀),
                s ∈ C_A ∪ {w} → (∀ x ∈ r.support.dropLast, x ∉ ({w, u'} : Finset V)) →
                ∃ rA : G_A.Walk s t₀, rA.support = r.support := by
              intro s t₀ r
              induction r with
              | nil => intro _ _; exact ⟨.nil, rfl⟩
              | @cons x y t' hxy r' ihr =>
                intro hx hnot
                have hx_dl : x ∈ (SimpleGraph.Walk.cons hxy r').support.dropLast := by
                  rw [SimpleGraph.Walk.support_cons,
                    List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil r')]
                  exact List.mem_cons_self ..
                have hx_nT : x ∉ ({w, u'} : Finset V) := hnot x hx_dl
                have hxw : x ≠ w := fun h => hx_nT (by simp [h])
                have hxu' : x ≠ u' := fun h => hx_nT (by simp [h])
                have hxCA : x ∈ C_A := by
                  rcases Finset.mem_union.mp hx with h1 | h2
                  · exact h1
                  · simp [hxw] at h2
                have hy_in : y ∈ C_A ∪ {w} := by
                  by_cases hyw : y = w
                  · exact Finset.mem_union_right _ (by simp [hyw])
                  · have hne_e : s(x, y) ≠ s(u', v') := by
                      intro h
                      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                      · exact hxu' h1
                      · exact hv'CA (h1 ▸ hxCA)
                    have hadj' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun h => hne_e (hsuv'.symm ▸ Set.mem_singleton_iff.mp h)⟩
                    exact Finset.mem_union_left _ (hCA_closed x hxCA y hadj' hyw)
                have hnot' : ∀ v ∈ r'.support.dropLast, v ∉ ({w, u'} : Finset V) := by
                  intro v hv
                  apply hnot v
                  rw [SimpleGraph.Walk.support_cons,
                    List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil r')]
                  exact List.mem_cons_of_mem _ hv
                obtain ⟨rA', hrA'⟩ := ihr hy_in hnot'
                exact ⟨SimpleGraph.Walk.cons ⟨hxy, hx, hy_in⟩ rA', by simp [hrA']⟩
            obtain ⟨qA, hqA⟩ := hlift_GA q ha_in hqint
            exact ⟨a, ha, t, ht, qA, fun hz => hzp (hqsub z (hqA ▸ hz))⟩
          have hGB_no_cut : ∀ z : V, ∃ t ∈ ({w, v'} : Finset V), ∃ b ∈ B, ∃ q : G_B.Walk t b, z ∉ q.support := by
            intro z
            rcases hno_cut z with ⟨a, ha, b, hb, p, hzp⟩
            have hex_hit : ∃ t ∈ ({w, v'} : Finset V), t ∈ p.reverse.support := by
              by_contra hnone
              push Not at hnone
              have hwn : w ∉ p.support := fun h => hnone w (by simp) (by simp [SimpleGraph.Walk.support_reverse, h])
              have hv'n : v' ∉ p.support := fun h => hnone v' (by simp) (by simp [SimpleGraph.Walk.support_reverse, h])
              have haw : a ≠ w := fun h => hwn (h ▸ SimpleGraph.Walk.start_mem_support p)
              have hbw : b ≠ w := fun h => hwn (h ▸ SimpleGraph.Walk.end_mem_support p)
              obtain ⟨x, hxCA, y, hyCA, hxy, hxp, hyp⟩ :=
                walk_exits_finset C_A p (hA_sub_CA a ha haw) (hB_not_CA b hb hbw)
              have hyw : y ≠ w := fun h => hwn (h ▸ hyp)
              have hxy_eq : s(x, y) = s(u', v') := by
                by_contra hne
                have hadj' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun h => hne (hsuv'.symm ▸ Set.mem_singleton_iff.mp h)⟩
                exact hyCA (hCA_closed x hxCA y hadj' hyw)
              rcases Sym2.eq_iff.mp hxy_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hv'n hyp
              · exact hv'n hxp
            obtain ⟨t, ht, q, hqsub, hqint⟩ := walk_prefix_to_set {w, v'} p.reverse hex_hit
            have hb_in : b ∈ C_B ∪ {w} := by
              by_cases hbw : b = w
              · exact Finset.mem_union_right _ (by simp [hbw])
              · exact Finset.mem_union_left _ (hB_sub_CB b hb hbw)
            have hlift_GB : ∀ {s t₀ : V} (r : G.Walk s t₀),
                s ∈ C_B ∪ {w} → (∀ x ∈ r.support.dropLast, x ∉ ({w, v'} : Finset V)) →
                ∃ rB : G_B.Walk s t₀, rB.support = r.support := by
              intro s t₀ r
              induction r with
              | nil => intro _ _; exact ⟨.nil, rfl⟩
              | @cons x y t' hxy r' ihr =>
                intro hx hnot
                have hx_dl : x ∈ (SimpleGraph.Walk.cons hxy r').support.dropLast := by
                  rw [SimpleGraph.Walk.support_cons,
                    List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil r')]
                  exact List.mem_cons_self ..
                have hx_nT : x ∉ ({w, v'} : Finset V) := hnot x hx_dl
                have hxw : x ≠ w := fun h => hx_nT (by simp [h])
                have hxv' : x ≠ v' := fun h => hx_nT (by simp [h])
                have hxCB : x ∈ C_B := by
                  rcases Finset.mem_union.mp hx with h1 | h2
                  · exact h1
                  · simp [hxw] at h2
                have hy_in : y ∈ C_B ∪ {w} := by
                  by_cases hyw : y = w
                  · exact Finset.mem_union_right _ (by simp [hyw])
                  · have hne_e : s(x, y) ≠ s(u', v') := by
                      intro h
                      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                      · exact Finset.disjoint_left.mp hCA_CB_disj hu'CA (h1 ▸ hxCB)
                      · exact hxv' h1
                    have hadj' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun h => hne_e (hsuv'.symm ▸ Set.mem_singleton_iff.mp h)⟩
                    exact Finset.mem_union_left _ (hCB_closed x hxCB y hadj' hyw)
                have hnot' : ∀ v ∈ r'.support.dropLast, v ∉ ({w, v'} : Finset V) := by
                  intro v hv
                  apply hnot v
                  rw [SimpleGraph.Walk.support_cons,
                    List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil r')]
                  exact List.mem_cons_of_mem _ hv
                obtain ⟨rB', hrB'⟩ := ihr hy_in hnot'
                exact ⟨SimpleGraph.Walk.cons ⟨hxy, hx, hy_in⟩ rB', by simp [hrB']⟩
            obtain ⟨qB, hqB⟩ := hlift_GB q hb_in hqint
            refine ⟨t, ht, b, hb, qB.reverse, fun hz => ?_⟩
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, hqB] at hz
            have h1 := hqsub z hz
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
            exact hzp h1
          -- Apply IH on G_A (A to {w, u'}) and G_B ({w, v'} to B)
          have hcard_wu' : 2 ≤ ({w, u'} : Finset V).card := by
            rw [Finset.card_pair hu'w.symm]
          have hcard_wv' : 2 ≤ ({w, v'} : Finset V).card := by
            rw [Finset.card_pair hv'w.symm]
          obtain ⟨a₁, a₂, s₁, s₂, p₁, p₂, ha₁, ha₂, hs₁, hs₂, ha12, hs12, hp₁, hp₂, hdisj_p, _, _⟩ :=
            ih _ hGA_lt G_A A {w, u'} (by congr 1; ext e; simp) hA hcard_wu' hGA_no_cut
          obtain ⟨t₁, t₂, b₁, b₂, q₁, q₂, ht₁, ht₂, hb₁, hb₂, ht12, hb12, hq₁, hq₂, hdisj_q, _, _⟩ :=
            ih _ hGB_lt G_B {w, v'} B (by congr 1; ext e; simp) hcard_wv' hB hGB_no_cut
          -- Every vertex of a walk in G_A ending in {w, u'} lies in C_A ∪ {w}
          have hGA_supp : ∀ {a s : V} (r : G_A.Walk a s), s ∈ C_A ∪ {w} →
              ∀ x ∈ r.support, x ∈ C_A ∪ {w} := by
            intro a s r hs
            induction r with
            | nil => intro x hx; simp at hx; rwa [hx]
            | @cons x y z hxy r' ih' =>
              intro v hv
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
              rcases hv with rfl | hv'
              · exact hxy.2.1
              · exact ih' hs v hv'
          have hGB_supp : ∀ {t b : V} (r : G_B.Walk t b), t ∈ C_B ∪ {w} →
              ∀ x ∈ r.support, x ∈ C_B ∪ {w} := by
            intro t b r ht
            induction r with
            | nil => intro x hx; simp at hx; rwa [hx]
            | @cons x y z hxy r' ih' =>
              intro v hv
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
              rcases hv with rfl | hv'
              · exact hxy.2.1
              · exact ih' hxy.2.2 v hv'
          -- Match (p_w, p_u) ending at (w, u') and (q_w, q_v) starting at (w, v')
          have hex_p : ∃ (aw au : V) (pw : G_A.Walk aw w) (pu : G_A.Walk au u'),
              aw ∈ A ∧ au ∈ A ∧ pw.IsPath ∧ pu.IsPath ∧
              Disjoint pw.support.toFinset pu.support.toFinset := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hs₁ hs₂
            rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
            · exact absurd rfl hs12
            · exact ⟨a₁, a₂, p₁, p₂, ha₁, ha₂, hp₁, hp₂, hdisj_p⟩
            · exact ⟨a₂, a₁, p₂, p₁, ha₂, ha₁, hp₂, hp₁, hdisj_p.symm⟩
            · exact absurd rfl hs12
          have hex_q : ∃ (bw bv : V) (qw : G_B.Walk w bw) (qv : G_B.Walk v' bv),
              bw ∈ B ∧ bv ∈ B ∧ qw.IsPath ∧ qv.IsPath ∧
              Disjoint qw.support.toFinset qv.support.toFinset := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
            rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
            · exact absurd rfl ht12
            · exact ⟨b₁, b₂, q₁, q₂, hb₁, hb₂, hq₁, hq₂, hdisj_q⟩
            · exact ⟨b₂, b₁, q₂, q₁, hb₂, hb₁, hq₂, hq₁, hdisj_q.symm⟩
            · exact absurd rfl ht12
          rcases hex_p with ⟨aw, au, pw, pu, hawA, hauA, hpw, hpu, hdisj_pwu⟩
          rcases hex_q with ⟨bw, bv, qw, qv, hbwB, hbvB, hqw, hqv, hdisj_qwv⟩
          have hpw_in : ∀ x ∈ pw.support, x ∈ C_A ∪ {w} :=
            hGA_supp pw (Finset.mem_union_right _ (Finset.mem_singleton_self w))
          have hpu_in : ∀ x ∈ pu.support, x ∈ C_A := by
            intro x hx
            have h1 := hGA_supp pu (Finset.mem_union_left _ hu'CA) x hx
            rcases Finset.mem_union.mp h1 with hCA | hw'
            · exact hCA
            · exfalso
              rw [Finset.mem_singleton] at hw'
              subst hw'
              exact Finset.disjoint_left.mp hdisj_pwu
                (List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support pw))
                (List.mem_toFinset.mpr hx)
          have hqw_in : ∀ x ∈ qw.support, x ∈ C_B ∪ {w} :=
            hGB_supp qw (Finset.mem_union_right _ (Finset.mem_singleton_self w))
          have hqv_in : ∀ x ∈ qv.support, x ∈ C_B := by
            intro x hx
            have h1 := hGB_supp qv (Finset.mem_union_left _ hv'CB) x hx
            rcases Finset.mem_union.mp h1 with hCB | hw'
            · exact hCB
            · exfalso
              rw [Finset.mem_singleton] at hw'
              subst hw'
              exact Finset.disjoint_left.mp hdisj_qwv
                (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support qw))
                (List.mem_toFinset.mpr hx)
          let φA : G_A →g G := SimpleGraph.Hom.ofLE hGA_le
          let φB : G_B →g G := SimpleGraph.Hom.ofLE hGB_le
          let rw_path : G.Walk aw bw := (pw.map φA).append (qw.map φB)
          let ruv_path : G.Walk au bv := (pu.map φA).append (SimpleGraph.Walk.cons huv' (qv.map φB))
          have hrw_isPath : rw_path.IsPath := by
            apply isPath_append_of_disjoint (pw.map φA) (qw.map φB) (hpw.map (f := φA) fun _ _ h => h) (hqw.map (f := φB) fun _ _ h => h)
            intro x hxp hxq
            simp only [SimpleGraph.Walk.support_map, List.map_id'] at hxp hxq
            have h1 := hpw_in x hxp
            have h2 := hqw_in x hxq
            rcases Finset.mem_union.mp h1 with hxCA | hxw
            · rcases Finset.mem_union.mp h2 with hxCB | hxw
              · exact absurd hxCB (Finset.disjoint_left.mp hCA_CB_disj hxCA)
              · exact Finset.mem_singleton.mp hxw
            · exact Finset.mem_singleton.mp hxw
          have hruv_isPath : ruv_path.IsPath := by
            have hqv_ext : (SimpleGraph.Walk.cons huv' (qv.map φB)).IsPath := by
              refine SimpleGraph.Walk.IsPath.cons (hqv.map (f := φB) fun _ _ h => h) ?_
              intro hm
              simp only [SimpleGraph.Walk.support_map, List.map_id'] at hm
              exact Finset.disjoint_left.mp hCA_CB_disj hu'CA (hqv_in u' hm)
            apply isPath_append_of_disjoint (pu.map φA) (SimpleGraph.Walk.cons huv' (qv.map φB)) (hpu.map (f := φA) fun _ _ h => h) hqv_ext
            intro x hxp hxq
            simp only [SimpleGraph.Walk.support_map, List.map_id',
              SimpleGraph.Walk.support_cons, List.mem_cons] at hxp hxq
            rcases hxq with rfl | hxq'
            · rfl
            · exact absurd (hqv_in x hxq') (Finset.disjoint_left.mp hCA_CB_disj (hpu_in x hxp))
          have hdisj_r : Disjoint rw_path.support.toFinset ruv_path.support.toFinset := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            have h1 : x ∈ pw.support ∨ x ∈ qw.support := by
              have hm := List.mem_toFinset.mp hx1
              dsimp only [rw_path] at hm
              rw [SimpleGraph.Walk.mem_support_append_iff] at hm
              simpa [φA, φB, SimpleGraph.Walk.support_map] using hm
            have h2 : x ∈ pu.support ∨ x ∈ qv.support := by
              have hm := List.mem_toFinset.mp hx2
              dsimp only [ruv_path] at hm
              rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
                List.mem_cons] at hm
              rcases hm with h | rfl | h
              · left; simpa [φA, SimpleGraph.Walk.support_map] using h
              · left; exact SimpleGraph.Walk.end_mem_support pu
              · right; simpa [φB, SimpleGraph.Walk.support_map] using h
            rcases h1 with hpw' | hqw' <;> rcases h2 with hpu' | hqv'
            · exact Finset.disjoint_left.mp hdisj_pwu (List.mem_toFinset.mpr hpw') (List.mem_toFinset.mpr hpu')
            · have hxCA := hpw_in x hpw'
              have hxCB := hqv_in x hqv'
              rcases Finset.mem_union.mp hxCA with h | h
              · exact Finset.disjoint_left.mp hCA_CB_disj h hxCB
              · exact hw_not_CB (Finset.mem_singleton.mp h ▸ hxCB)
            · have hxCB := hqw_in x hqw'
              have hxCA := hpu_in x hpu'
              rcases Finset.mem_union.mp hxCB with h | h
              · exact Finset.disjoint_left.mp hCA_CB_disj hxCA h
              · exact hw_not_CA (Finset.mem_singleton.mp h ▸ hxCA)
            · exact Finset.disjoint_left.mp hdisj_qwv (List.mem_toFinset.mpr hqw') (List.mem_toFinset.mpr hqv')
          -- Trim both paths so they are internally disjoint from A ∪ B
          obtain ⟨a₁', ha₁', b₁', hb₁', r₁, hr₁_path, hr₁_sub, hr₁_int⟩ :=
            trim_ab_path A B hawA hbwB rw_path
          obtain ⟨a₂', ha₂', b₂', hb₂', r₂, hr₂_path, hr₂_sub, hr₂_int⟩ :=
            trim_ab_path A B hauA hbvB ruv_path
          have hdisj_final : Disjoint r₁.support.toFinset r₂.support.toFinset := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            exact Finset.disjoint_left.mp hdisj_r
              (List.mem_toFinset.mpr (hr₁_sub x (List.mem_toFinset.mp hx1)))
              (List.mem_toFinset.mpr (hr₂_sub x (List.mem_toFinset.mp hx2)))
          have ha12' : a₁' ≠ a₂' := by
            intro h
            subst h
            exact Finset.disjoint_left.mp hdisj_final
              (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support r₁))
              (List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support r₂))
          have hb12' : b₁' ≠ b₂' := by
            intro h
            subst h
            exact Finset.disjoint_left.mp hdisj_final
              (List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support r₁))
              (List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support r₂))
          exact ⟨a₁', a₂', b₁', b₂', r₁, r₂, ha₁', ha₂', hb₁', hb₂', ha12', hb12',
            hr₁_path, hr₂_path, hdisj_final, hr₁_int, hr₂_int⟩

end SignedGraphs
