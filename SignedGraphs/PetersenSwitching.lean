import SignedGraphs.ParityAndCycles

/-!
# Lemma 3.4(3): Two Vertex-Disjoint Odd Cycles Force `(Petersen, -1)`

Helper lemmas for Lemma 3.4(3), including `petersen_switching_iso`.
-/

open SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma odd_cycle_w3 (S : SignedGraph V) (hnoc : IsNOC S)
    {v : V} (c : S.graph.Walk v v) (hc : c.IsCycle) (hodd : Odd c.length) :
    walkModFourWeight S.sign c = 3 :=
  hnoc v c hc hodd

private lemma sign_five_cycle_prod_neg_one (S : SignedGraph V) (hnoc : IsNOC S)
    {a b c d e : V}
    (hab : S.graph.Adj a b) (hbc : S.graph.Adj b c) (hcd : S.graph.Adj c d)
    (hde : S.graph.Adj d e) (hea : S.graph.Adj e a)
    (hnd : [a, b, c, d, e].Nodup) :
    S.sign s(a, b) * S.sign s(b, c) * S.sign s(c, d) * S.sign s(d, e) * S.sign s(e, a) = -1 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hnd
  rcases hnd with ⟨⟨h_ab, h_ac, h_ad, h_ae⟩, ⟨h_bc, h_bd, h_be⟩, ⟨h_cd, h_ce⟩, h_de⟩
  let cyc : S.graph.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))))
  have hcyc : cyc.IsCycle := by
    refine SimpleGraph.Walk.IsCycle.mk' (SimpleGraph.Walk.IsTrail.mk ?_) (by simp [cyc]) ?_
    · simp [cyc, Sym2.eq_iff, h_ab, h_ab.symm, h_ac, h_ac.symm, h_ad, h_ad.symm, h_ae, h_ae.symm,
        h_bc, h_bc.symm, h_bd, h_bd.symm, h_be, h_be.symm, h_cd, h_cd.symm, h_ce, h_ce.symm, h_de, h_de.symm]
    · simp [cyc, h_bc, h_bc.symm, h_bd, h_bd.symm, h_be, h_be.symm, h_ab, h_ab.symm,
        h_cd, h_cd.symm, h_ce, h_ce.symm, h_ac, h_ac.symm, h_de, h_de.symm, h_ad, h_ad.symm, h_ae, h_ae.symm]
  have hw := odd_cycle_w3 S hnoc cyc hcyc ⟨2, by simp [cyc]⟩
  simp only [cyc, walkModFourWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hw
  rcases S.sign_pm_one s(a, b) hab with h1 | h1 <;>
  rcases S.sign_pm_one s(b, c) hbc with h2 | h2 <;>
  rcases S.sign_pm_one s(c, d) hcd with h3 | h3 <;>
  rcases S.sign_pm_one s(d, e) hde with h4 | h4 <;>
  rcases S.sign_pm_one s(e, a) hea with h5 | h5 <;>
  simp [modFourWeight, h1, h2, h3, h4, h5] at hw ⊢

set_option maxHeartbeats 800000 in
/-- If `S` is NOC and `f : Fin 10 → V` is a bijection whose pull-back graph is `petersenGraph`,
then `S` is switching-isomorphic to `(Petersen, -1)`. -/
lemma petersen_switching_iso (S : SignedGraph V) (hnoc : IsNOC S)
    (f : Fin 10 → V) (hf_bij : Function.Bijective f)
    (hf_adj : ∀ i j : Fin 10, petersenGraph.Adj i j ↔ S.graph.Adj (f i) (f j)) :
    SwitchingIso S petersenSignedGraph := by
  classical
  let φ : V ≃ Fin 10 := (Equiv.ofBijective f hf_bij).symm
  have hφf : ∀ i : Fin 10, φ (f i) = i := fun i => (Equiv.ofBijective f hf_bij).symm_apply_apply i
  have hfφ : ∀ x : V, f (φ x) = x := fun x => (Equiv.ofBijective f hf_bij).apply_symm_apply x
  let e : S.graph ≃g petersenSignedGraph.graph :=
    { toEquiv := φ
      map_rel_iff' := by
        intro x y
        change petersenGraph.Adj (φ x) (φ y) ↔ S.graph.Adj x y
        rw [hf_adj, hfφ, hfφ] }
  -- Spanning tree signs s : Fin 10 → ℤ forcing the 9 tree edges to sign -1
  let sg : Fin 10 → Fin 10 → ℤ := fun i j => S.sign s(f i, f j)
  have hsg_pm : ∀ i j : Fin 10, petersenGraph.Adj i j → sg i j = 1 ∨ sg i j = -1 := by
    intro i j hij; exact S.sign_pm_one s(f i, f j) ((hf_adj i j).mp hij)
  have hsg_sym : ∀ i j : Fin 10, sg i j = sg j i := fun i j => by simp [sg, Sym2.eq_swap]
  have hp_adj : ∀ i j : Fin 10, petersenGraph.Adj i j ↔
      ((i.val < 5 ∧ j.val < 5 ∧ (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
       (5 ≤ i.val ∧ 5 ≤ j.val ∧ ((j.val - 5) = ((i.val - 5) + 2) % 5 ∨ (i.val - 5) = ((j.val - 5) + 2) % 5)) ∨
       (i.val < 5 ∧ j.val = i.val + 5) ∨
       (j.val < 5 ∧ i.val = j.val + 5)) ∧ i ≠ j := by
    intro i j; simp [petersenGraph, SimpleGraph.fromRel_adj, and_comm]; tauto
  let s0 : ℤ := 1
  let s1 : ℤ := -sg 0 1
  let s2 : ℤ := -s1 * sg 1 2
  let s3 : ℤ := -s2 * sg 2 3
  let s4 : ℤ := -s3 * sg 3 4
  let s : Fin 10 → ℤ
    | 0 => s0
    | 1 => s1
    | 2 => s2
    | 3 => s3
    | 4 => s4
    | 5 => -s0 * sg 0 5
    | 6 => -s1 * sg 1 6
    | 7 => -s2 * sg 2 7
    | 8 => -s3 * sg 3 8
    | 9 => -s4 * sg 4 9
  have hpm_mul : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      (-a * b = 1 ∨ -a * b = -1) ∧ a * (-a * b) * b = -1 := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> decide
  have h01 : petersenGraph.Adj 0 1 := (hp_adj 0 1).mpr (by decide)
  have h12 : petersenGraph.Adj 1 2 := (hp_adj 1 2).mpr (by decide)
  have h23 : petersenGraph.Adj 2 3 := (hp_adj 2 3).mpr (by decide)
  have h34 : petersenGraph.Adj 3 4 := (hp_adj 3 4).mpr (by decide)
  have h40 : petersenGraph.Adj 4 0 := (hp_adj 4 0).mpr (by decide)
  have h05 : petersenGraph.Adj 0 5 := (hp_adj 0 5).mpr (by decide)
  have h16 : petersenGraph.Adj 1 6 := (hp_adj 1 6).mpr (by decide)
  have h27 : petersenGraph.Adj 2 7 := (hp_adj 2 7).mpr (by decide)
  have h38 : petersenGraph.Adj 3 8 := (hp_adj 3 8).mpr (by decide)
  have h49 : petersenGraph.Adj 4 9 := (hp_adj 4 9).mpr (by decide)
  have h57 : petersenGraph.Adj 5 7 := (hp_adj 5 7).mpr (by decide)
  have h79 : petersenGraph.Adj 7 9 := (hp_adj 7 9).mpr (by decide)
  have h96 : petersenGraph.Adj 9 6 := (hp_adj 9 6).mpr (by decide)
  have h68 : petersenGraph.Adj 6 8 := (hp_adj 6 8).mpr (by decide)
  have h85 : petersenGraph.Adj 8 5 := (hp_adj 8 5).mpr (by decide)
  have hs0_pm : s0 = 1 ∨ s0 = -1 := Or.inl rfl
  have hs1_pm : s1 = 1 ∨ s1 = -1 := by
    have := hpm_mul s0 (sg 0 1) hs0_pm (hsg_pm 0 1 h01); simpa [s0, s1] using this.1
  have hs2_pm : s2 = 1 ∨ s2 = -1 := (hpm_mul s1 (sg 1 2) hs1_pm (hsg_pm 1 2 h12)).1
  have hs3_pm : s3 = 1 ∨ s3 = -1 := (hpm_mul s2 (sg 2 3) hs2_pm (hsg_pm 2 3 h23)).1
  have hs4_pm : s4 = 1 ∨ s4 = -1 := (hpm_mul s3 (sg 3 4) hs3_pm (hsg_pm 3 4 h34)).1
  have hs_pm : ∀ i : Fin 10, s i = 1 ∨ s i = -1 := by
    intro i; fin_cases i
    · exact hs0_pm
    · exact hs1_pm
    · exact hs2_pm
    · exact hs3_pm
    · exact hs4_pm
    · exact (hpm_mul s0 (sg 0 5) hs0_pm (hsg_pm 0 5 h05)).1
    · exact (hpm_mul s1 (sg 1 6) hs1_pm (hsg_pm 1 6 h16)).1
    · exact (hpm_mul s2 (sg 2 7) hs2_pm (hsg_pm 2 7 h27)).1
    · exact (hpm_mul s3 (sg 3 8) hs3_pm (hsg_pm 3 8 h38)).1
    · exact (hpm_mul s4 (sg 4 9) hs4_pm (hsg_pm 4 9 h49)).1
  let σ' : Fin 10 → Fin 10 → ℤ := fun i j => s i * s j * sg i j
  have hσ'_sym : ∀ i j : Fin 10, σ' i j = σ' j i := fun i j => by
    dsimp only [σ']; rw [hsg_sym]; ring
  have ht01 : σ' 0 1 = -1 := by
    have := (hpm_mul s0 (sg 0 1) hs0_pm (hsg_pm 0 1 h01)).2; simpa [σ', s, s0, s1] using this
  have ht12 : σ' 1 2 = -1 := (hpm_mul s1 (sg 1 2) hs1_pm (hsg_pm 1 2 h12)).2
  have ht23 : σ' 2 3 = -1 := (hpm_mul s2 (sg 2 3) hs2_pm (hsg_pm 2 3 h23)).2
  have ht34 : σ' 3 4 = -1 := (hpm_mul s3 (sg 3 4) hs3_pm (hsg_pm 3 4 h34)).2
  have ht05 : σ' 0 5 = -1 := (hpm_mul s0 (sg 0 5) hs0_pm (hsg_pm 0 5 h05)).2
  have ht16 : σ' 1 6 = -1 := (hpm_mul s1 (sg 1 6) hs1_pm (hsg_pm 1 6 h16)).2
  have ht27 : σ' 2 7 = -1 := (hpm_mul s2 (sg 2 7) hs2_pm (hsg_pm 2 7 h27)).2
  have ht38 : σ' 3 8 = -1 := (hpm_mul s3 (sg 3 8) hs3_pm (hsg_pm 3 8 h38)).2
  have ht49 : σ' 4 9 = -1 := (hpm_mul s4 (sg 4 9) hs4_pm (hsg_pm 4 9 h49)).2
  have h5_edge : ∀ (a b c d k : Fin 10),
      petersenGraph.Adj a b → petersenGraph.Adj b c → petersenGraph.Adj c d →
      petersenGraph.Adj d k → petersenGraph.Adj k a →
      [a, b, c, d, k].Nodup →
      σ' a b = -1 → σ' b c = -1 → σ' c d = -1 → σ' d k = -1 → σ' k a = -1 := by
    intro a b c d k hab hbc hcd hdk hka hnd h1 h2 h3 h4
    have hnd_f : [f a, f b, f c, f d, f k].Nodup := by
      have : [f a, f b, f c, f d, f k] = [a, b, c, d, k].map f := rfl
      rw [this]; exact hnd.map hf_bij.1
    have hprod := sign_five_cycle_prod_neg_one S hnoc
      ((hf_adj a b).mp hab) ((hf_adj b c).mp hbc) ((hf_adj c d).mp hcd)
      ((hf_adj d k).mp hdk) ((hf_adj k a).mp hka) hnd_f
    have hsq : ∀ x : Fin 10, s x * s x = 1 := fun x => by rcases hs_pm x with h | h <;> simp [h]
    have hmul : σ' a b * σ' b c * σ' c d * σ' d k * σ' k a =
        sg a b * sg b c * sg c d * sg d k * sg k a := by
      dsimp only [σ']
      calc (s a * s b * sg a b) * (s b * s c * sg b c) * (s c * s d * sg c d) *
            (s d * s k * sg d k) * (s k * s a * sg k a)
          = (s a * s a) * (s b * s b) * (s c * s c) * (s d * s d) * (s k * s k) *
            (sg a b * sg b c * sg c d * sg d k * sg k a) := by ring
        _ = sg a b * sg b c * sg c d * sg d k * sg k a := by
            rw [hsq a, hsq b, hsq c, hsq d, hsq k]; ring
    rw [h1, h2, h3, h4] at hmul
    change _ = S.sign s(f a, f b) * S.sign s(f b, f c) * S.sign s(f c, f d) * S.sign s(f d, f k) * S.sign s(f k, f a) at hmul
    rw [hprod] at hmul
    linarith
  have ht40 : σ' 4 0 = -1 := h5_edge 0 1 2 3 4 h01 h12 h23 h34 h40 (by decide) ht01 ht12 ht23 ht34
  have ht75 : σ' 7 5 = -1 := h5_edge 5 0 1 2 7 h05.symm h01 h12 h27 h57.symm (by decide)
    (by rw [hσ'_sym]; exact ht05) ht01 ht12 ht27
  have ht97 : σ' 9 7 = -1 := h5_edge 7 2 3 4 9 h27.symm h23 h34 h49 h79.symm (by decide)
    (by rw [hσ'_sym]; exact ht27) ht23 ht34 ht49
  have ht69 : σ' 6 9 = -1 := h5_edge 9 4 0 1 6 h49.symm h40 h01 h16 h96.symm (by decide)
    (by rw [hσ'_sym]; exact ht49) ht40 ht01 ht16
  have ht86 : σ' 8 6 = -1 := h5_edge 6 1 2 3 8 h16.symm h12 h23 h38 h68.symm (by decide)
    (by rw [hσ'_sym]; exact ht16) ht12 ht23 ht38
  have ht58 : σ' 5 8 = -1 := h5_edge 8 3 4 0 5 h38.symm h34 h40 h05 h85.symm (by decide)
    (by rw [hσ'_sym]; exact ht38) ht34 ht40 ht05
  let T : Finset V := Finset.univ.filter fun x => s (φ x) = -1
  refine ⟨e, T, ?_⟩
  intro u v huv
  simp only [petersenSignedGraph]
  have hθ : ∀ x : V, (if x ∈ T then (-1 : ℤ) else 1) = s (φ x) := by
    intro x
    rcases hs_pm (φ x) with h | h
    · have : x ∉ T := by simp [T, h]
      simp [this, h]
    · have : x ∈ T := by simp [T, h]
      simp [this, h]
  rw [hθ u, hθ v]
  have hadj_p : petersenGraph.Adj (φ u) (φ v) := (hf_adj (φ u) (φ v)).mpr (by rwa [hfφ, hfφ])
  have hgoal : σ' (φ u) (φ v) = -1 := by
    generalize ha : φ u = a at hadj_p ⊢
    generalize hb : φ v = b at hadj_p ⊢
    fin_cases a <;> fin_cases b <;>
    first
      | exact absurd hadj_p (by rw [hp_adj]; decide)
      | exact ht01 | exact (hσ'_sym 1 0).trans ht01
      | exact ht12 | exact (hσ'_sym 2 1).trans ht12
      | exact ht23 | exact (hσ'_sym 3 2).trans ht23
      | exact ht34 | exact (hσ'_sym 4 3).trans ht34
      | exact ht40 | exact (hσ'_sym 0 4).trans ht40
      | exact ht05 | exact (hσ'_sym 5 0).trans ht05
      | exact ht16 | exact (hσ'_sym 6 1).trans ht16
      | exact ht27 | exact (hσ'_sym 7 2).trans ht27
      | exact ht38 | exact (hσ'_sym 8 3).trans ht38
      | exact ht49 | exact (hσ'_sym 9 4).trans ht49
      | exact ht75 | exact (hσ'_sym 5 7).trans ht75
      | exact ht97 | exact (hσ'_sym 7 9).trans ht97
      | exact ht69 | exact (hσ'_sym 9 6).trans ht69
      | exact ht86 | exact (hσ'_sym 6 8).trans ht86
      | exact ht58 | exact (hσ'_sym 8 5).trans ht58
  simpa [σ', sg, hfφ] using hgoal

lemma cycle_len_eq_five_vertices {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (h5 : c.length = 5) :
    ∃ v1 v2 v3 v4 : V, [v, v1, v2, v3, v4].Nodup ∧
      G.Adj v v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4 ∧ G.Adj v4 v ∧
      (∀ x, x ∈ c.support ↔ x = v ∨ x = v1 ∨ x = v2 ∨ x = v3 ∨ x = v4) ∧
      (∀ e, e ∈ c.edges ↔ e = s(v, v1) ∨ e = s(v1, v2) ∨ e = s(v2, v3) ∨ e = s(v3, v4) ∨ e = s(v4, v)) := by
  cases c with
  | nil => simp at h5
  | @cons _ v1 _ h01 r1 =>
    cases r1 with
    | nil => simp at h5
    | @cons _ v2 _ h12 r2 =>
      cases r2 with
      | nil => simp at h5
      | @cons _ v3 _ h23 r3 =>
        cases r3 with
        | nil => simp at h5
        | @cons _ v4 _ h34 r4 =>
          cases r4 with
          | nil => simp at h5
          | @cons _ v5 _ h45 r5 =>
            cases r5 with
            | nil =>
              have hnd := hc.support_nodup
              simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons] at hnd
              have hnd' : [v, v1, v2, v3, v4].Nodup := by
                have hnd_c : [v1, v2, v3, v4, v].Nodup := hnd
                rw [List.nodup_cons] at hnd_c ⊢
                simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
                  and_true] at hnd_c ⊢
                tauto
              refine ⟨v1, v2, v3, v4, hnd', h01, h12, h23, h34, h45, ?_, ?_⟩
              · intro x; simp [or_comm, or_left_comm, or_assoc]
              · intro e; simp [or_comm, or_left_comm, or_assoc]
            | cons _ _ => simp at h5

lemma cycle_len_eq_three_verts {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (h3 : c.length = 3) :
    ∃ v1 v2 : V, v ≠ v1 ∧ v ≠ v2 ∧ v1 ≠ v2 ∧
      G.Adj v v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v ∧
      (∀ x, x ∈ c.support ↔ x = v ∨ x = v1 ∨ x = v2) := by
  cases c with
  | nil => simp at h3
  | @cons _ v1 _ h01 r1 =>
    cases r1 with
    | nil => simp at h3
    | @cons _ v2 _ h12 r2 =>
      cases r2 with
      | nil => simp at h3
      | @cons _ v3 _ h23 r3 =>
        cases r3 with
        | nil =>
          refine ⟨v1, v2, G.ne_of_adj h01, (G.ne_of_adj h23).symm, G.ne_of_adj h12, h01, h12, h23, ?_⟩
          intro x; simp [or_comm, or_left_comm, or_assoc]
        | cons _ _ => simp at h3

/-- Helper: given a path `p : G.Walk a b` of length `≥ 2`, extract the first internal vertex `x`
with `G.Adj a x` and the remaining subpath `q : G.Walk x b` of length `p.length - 1`. -/
lemma path_split_first {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (h2 : 2 ≤ p.length) :
    ∃ (x : V) (hax : G.Adj a x) (q : G.Walk x b),
      p = SimpleGraph.Walk.cons hax q ∧ q.IsPath ∧ x ≠ a ∧ x ≠ b ∧
      1 ≤ q.length ∧ q.length + 1 = p.length ∧ a ∉ q.support := by
  cases p with
  | nil => simp at h2
  | @cons _ x _ hax q =>
    have hq_pos : 1 ≤ q.length := by simp at h2; omega
    have hxb : x ≠ b := by cases q with | nil => simp at hq_pos | cons h _ =>
      have hnd := (SimpleGraph.Walk.IsPath.of_cons hp).support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      intro heq; subst heq; exact hnd.1 (SimpleGraph.Walk.end_mem_support _)
    have ha_not : a ∉ q.support := by
      have hnd := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    exact ⟨x, hax, q, rfl, SimpleGraph.Walk.IsPath.of_cons hp, (G.ne_of_adj hax).symm, hxb, hq_pos, by simp, ha_not⟩

/-- Helper: on a path `P : G.Walk a b` with a 2-coloring `col : V → Bool` (flipping along edges of `P`),
`(col x = col y) ↔ Even (P.takeUntil x).length ↔ Even (P.takeUntil y).length`. -/
lemma path_bipartite_parity {G : SimpleGraph V} {a b : V} (P : G.Walk a b)
    (col : V → Bool) (hcol : ∀ u v, s(u, v) ∈ P.edges → col u ≠ col v) :
    (col b = col a ↔ Even P.length) := by
  induction P with
  | nil => simp
  | @cons u v w huv r ih =>
    have hne : col u ≠ col v := hcol u v (by simp)
    have ihr := ih (fun x y hxy => hcol x y (by simp [hxy]))
    simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one]
    cases hu : col u <;> cases hv : col v <;> cases hw : col w <;> simp_all

end SignedGraphs
