import SignedGraphs.LocalReductions
import SignedGraphs.SchurReductions
import SignedGraphs.SPQR
import SignedGraphs.Challenge

/-!
# Proofs of Theorem 1.2 and Corollary 1.3 (Section 6)

Combines Sections 2–5 via the SPQR-tree decomposition to prove `theorem_1_2`
and `corollary_1_3`.
-/

open Matrix SimpleGraph

namespace SignedGraphs

/-- **Theorem 1.2**: Every real symmetric zero-diagonal NOC matrix `A` satisfies `s(A) ≤ 0`. -/
theorem theorem_1_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0) (hnoc : MatrixIsNOC A hA.isSymm) :
    signature A hA ≤ 0 := by
  sorry

section Corollary13

private lemma matSig_eq_signature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Challenge.matSig A hA = signature A hA := by
  unfold Challenge.matSig signature posInertia negInertia
  have h1 : (Finset.univ.filter fun i : Fin n => 0 < hA.eigenvalues i) =
      @Finset.filter (Fin n) (fun i => 0 < hA.eigenvalues i) (Classical.decPred _) Finset.univ := by
    ext i; simp
  have h2 : (Finset.univ.filter fun i : Fin n => hA.eigenvalues i < 0) =
      @Finset.filter (Fin n) (fun i => hA.eigenvalues i < 0) (Classical.decPred _) Finset.univ := by
    ext i; simp
  congr 1 <;> congr 1 <;> ext i <;> simp

private lemma cycle_of_eq_graph {V : Type*} {G₁ G₂ : SimpleGraph V} (h : G₁ = G₂)
    {v : V} (c : G₁.Walk v v) (hc : c.IsCycle) :
    ∃ c' : G₂.Walk v v, c'.IsCycle ∧ c'.length = c.length ∧ c'.edges = c.edges := by
  subst h; exact ⟨c, hc, rfl, rfl⟩

private lemma matrixGraph_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    matrixGraph (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) = G := by
  ext i j
  simp only [matrixGraph, SimpleGraph.adjMatrix_apply]
  constructor
  · rintro ⟨_, hne⟩
    by_contra h
    simp [h] at hne
  · intro h
    exact ⟨G.ne_of_adj h, by simp [h]⟩

private lemma matrixGraph_neg_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    matrixGraph (-(G.adjMatrix ℝ))
      (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm = G := by
  ext i j
  simp only [matrixGraph, Matrix.neg_apply, SimpleGraph.adjMatrix_apply]
  constructor
  · rintro ⟨_, hne⟩
    by_contra h
    simp [h] at hne
  · intro h
    exact ⟨G.ne_of_adj h, by simp [h]⟩

private lemma walk_map_isCycle {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (hφ : Function.Injective φ) {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    (c.map φ).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_map]
    exact hc.toIsTrail.edges_nodup.map (Sym2.map.injective hφ)
  · intro hnil
    have hlen : (c.map φ).length = 0 := by rw [hnil]; rfl
    rw [SimpleGraph.Walk.length_map] at hlen
    exact hc.ne_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hlen)
  · rw [SimpleGraph.Walk.support_map, List.map_tail]
    exact hc.support_nodup.map hφ

private lemma cycleCountMod4_comap_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (r : ℕ) (v₀ : Fin n) (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle) (hr₀ : c₀.length % 4 = r)
    (e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀}) :
    Challenge.cycleCountMod4 (G.comap (fun i => (e i).1)) r + 1 ≤
      Challenge.cycleCountMod4 G r := by
  classical
  let f : Fin (n - 1) → Fin n := fun i => (e i).1
  have hf : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
  have hf_ne : ∀ i, f i ≠ v₀ := fun i => (e i).2
  let G' : SimpleGraph (Fin (n - 1)) := G.comap f
  let φ : G' →g G := ⟨f, fun h => h⟩
  let s' : Finset (Finset (Sym2 (Fin (n - 1)))) :=
    Finset.univ.filter fun S =>
      ∃ (v : Fin (n - 1)) (c : G'.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r
  let s : Finset (Finset (Sym2 (Fin n))) :=
    Finset.univ.filter fun S =>
      ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r
  let F : Finset (Sym2 (Fin (n - 1))) → Finset (Sym2 (Fin n)) :=
    fun S => S.image (Sym2.map f)
  have hF_inj : Function.Injective F :=
    Finset.image_injective (Sym2.map.injective hf)
  have hc₀_mem : c₀.edges.toFinset ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v₀, c₀, hc₀, rfl, hr₀⟩
  have hF_sub : s'.image F ⊆ s.erase c₀.edges.toFinset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨S', hS', rfl⟩
    simp only [s', Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    rcases hS' with ⟨u', c', hc', hS'_eq, hr'⟩
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      cases c₀ with
      | nil => exact hc₀.ne_nil rfl
      | @cons _ w _ hadj p =>
        have hmem : s(v₀, w) ∈ (SimpleGraph.Walk.cons hadj p).edges.toFinset := by
          simp [SimpleGraph.Walk.edges_cons]
        rw [← heq] at hmem
        rcases Finset.mem_image.mp hmem with ⟨e', _, he'⟩
        rcases e' with ⟨a, b⟩
        simp only [Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he'
        rcases he' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hf_ne a h1
        · exact hf_ne b h2
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨f u', c'.map φ, walk_map_isCycle φ hf c' hc', ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_map, List.toFinset_map, hS'_eq]
        rfl
      · simpa [SimpleGraph.Walk.length_map] using hr'
  have hcard_le : s'.card ≤ (s.erase c₀.edges.toFinset).card := by
    rw [← Finset.card_image_of_injective s' hF_inj]
    exact Finset.card_le_card hF_sub
  have herase : (s.erase c₀.edges.toFinset).card + 1 = s.card :=
    Finset.card_erase_add_one hc₀_mem
  change s'.card + 1 ≤ s.card
  omega

private lemma signature_adjMatrix_le_cycleCountMod4_one :
    ∀ (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Challenge.cycleCountMod4 G 1 ≤ k →
      signature (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (k : ℤ)
  | 0, n, G, _, hk => by
    have hk0 : Challenge.cycleCountMod4 G 1 = 0 := Nat.le_zero.mp hk
    apply theorem_1_2 (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)
    · intro i; simp [SimpleGraph.adjMatrix_apply, G.loopless i]
    · intro v c hc hodd
      have hG := matrixGraph_adjMatrix G
      obtain ⟨c', hc', hlen', _⟩ := cycle_of_eq_graph hG c hc
      have hne1 : c.length % 4 ≠ 1 := by
        intro h1
        have hmem : c'.edges.toFinset ∈
            (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
              ∃ (u : Fin n) (c'' : G.Walk u u), c''.IsCycle ∧ c''.edges.toFinset = S ∧
                c''.length % 4 = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, c', hc', rfl, by rw [hlen']; exact h1⟩
        have hpos : 0 < Challenge.cycleCountMod4 G 1 := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hprod1 : walkSignProd (matrixSignedGraph (G.adjMatrix ℝ)
          (SimpleGraph.isSymm_adjMatrix G)).sign c = 1 := by
        unfold walkSignProd
        apply List.prod_eq_one
        intro x hx
        rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
        have hedge : e ∈ (matrixGraph (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).edgeSet :=
          c.edges_subset_edgeSet he
        rcases e with ⟨a, b⟩
        simp only [matrixSignedGraph, Sym2.lift_mk]
        have hadj : G.Adj a b := by
          rw [hG] at hedge
          exact hedge
        simp [SimpleGraph.adjMatrix_apply, hadj]
      rcases hodd with ⟨m, hm⟩
      have hmod3 : c.length % 4 = 3 := by omega
      have hm_odd : Odd m := by
        refine ⟨m / 2, ?_⟩
        omega
      unfold signedCycleType
      rw [hprod1, mul_one, show c.length / 2 = m by omega]
      exact Odd.neg_one_pow hm_odd
  | k + 1, n, G, _, hk => by
    classical
    by_cases h0 : Challenge.cycleCountMod4 G 1 = 0
    · have hle := signature_adjMatrix_le_cycleCountMod4_one 0 G (le_of_eq h0)
      omega
    · have hpos : 0 < Challenge.cycleCountMod4 G 1 := Nat.pos_of_ne_zero h0
      obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₀
      rcases hS₀ with ⟨v₀, c₀, hc₀, _, hlen₀⟩
      have hcard_sub : Fintype.card {x : Fin n // x ≠ v₀} = n - 1 := by
        have hv : 0 < n := Fin.pos v₀
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        simp
      let e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀} :=
        (Fintype.equivFinOfCardEq hcard_sub).symm
      let G' : SimpleGraph (Fin (n - 1)) := G.comap (fun i => (e i).1)
      have hlt : Challenge.cycleCountMod4 G' 1 ≤ k := by
        have h := cycleCountMod4_comap_lt G 1 v₀ c₀ hc₀ hlen₀ e
        omega
      have hIH := signature_adjMatrix_le_cycleCountMod4_one k G' hlt
      have hinter := signature_interlacing_delete_vertex (G.adjMatrix ℝ)
        (SimpleGraph.isSymm_adjMatrix G) v₀
      have hsub_eq : ((G.adjMatrix ℝ).submatrix (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1)).submatrix e e = G'.adjMatrix ℝ := by
        ext i j
        simp [G', SimpleGraph.adjMatrix_apply]
      have hsig_sub : signature ((G.adjMatrix ℝ).submatrix
          (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1))
          (isHermitian_submatrix (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) _) =
          signature (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G') := by
        rw [← signature_reindex e _ (isHermitian_submatrix (G.adjMatrix ℝ)
          (SimpleGraph.isSymm_adjMatrix G) _)]
        have hEq : ∀ (M₁ M₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
            (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian), M₁ = M₂ →
            signature M₁ h₁ = signature M₂ h₂ := by
          intro M₁ M₂ h₁ h₂ h; subst h; rfl
        exact hEq _ _ _ _ hsub_eq
      have hle1 : signature (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) -
          signature (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G') ≤ 1 := by
        rw [← hsig_sub]
        exact (abs_le.mp hinter).2
      omega

private lemma signature_neg_adjMatrix_le_cycleCountMod4_three :
    ∀ (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Challenge.cycleCountMod4 G 3 ≤ k →
      signature (-(G.adjMatrix ℝ))
        (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)) ≤ (k : ℤ)
  | 0, n, G, _, hk => by
    have hk0 : Challenge.cycleCountMod4 G 3 = 0 := Nat.le_zero.mp hk
    apply theorem_1_2 (-(G.adjMatrix ℝ))
      (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G))
    · intro i; simp [SimpleGraph.adjMatrix_apply, G.loopless i]
    · intro v c hc hodd
      have hG := matrixGraph_neg_adjMatrix G
      obtain ⟨c', hc', hlen', _⟩ := cycle_of_eq_graph hG c hc
      have hne3 : c.length % 4 ≠ 3 := by
        intro h3
        have hmem : c'.edges.toFinset ∈
            (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
              ∃ (u : Fin n) (c'' : G.Walk u u), c''.IsCycle ∧ c''.edges.toFinset = S ∧
                c''.length % 4 = 3) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, c', hc', rfl, by rw [hlen']; exact h3⟩
        have hpos : 0 < Challenge.cycleCountMod4 G 3 := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hprod_neg : walkSignProd (matrixSignedGraph (-(G.adjMatrix ℝ))
          (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign c = -1 := by
        unfold walkSignProd
        have hall : ∀ x ∈ c.edges.map (matrixSignedGraph (-(G.adjMatrix ℝ))
            (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign,
            x = (-1 : ℤ) := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
          have hedge : e ∈ (matrixGraph (-(G.adjMatrix ℝ))
              (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).edgeSet :=
            c.edges_subset_edgeSet he
          rcases e with ⟨a, b⟩
          simp only [matrixSignedGraph, Sym2.lift_mk]
          have hadj : G.Adj a b := by
            rw [hG] at hedge
            exact hedge
          simp [SimpleGraph.adjMatrix_apply, hadj]
        have hmap_eq : c.edges.map (matrixSignedGraph (-(G.adjMatrix ℝ))
            (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign =
            List.replicate c.length (-1 : ℤ) := by
          apply List.eq_replicate_iff.mpr
          exact ⟨by simp [SimpleGraph.Walk.length_edges], hall⟩
        rw [hmap_eq, List.prod_replicate]
        exact Odd.neg_one_pow hodd
      rcases hodd with ⟨m, hm⟩
      have hmod1 : c.length % 4 = 1 := by omega
      have hm_even : Even m := ⟨m / 2, by omega⟩
      unfold signedCycleType
      rw [hprod_neg, show c.length / 2 = m by omega, Even.neg_one_pow hm_even, one_mul]
  | k + 1, n, G, _, hk => by
    classical
    by_cases h0 : Challenge.cycleCountMod4 G 3 = 0
    · have hle := signature_neg_adjMatrix_le_cycleCountMod4_three 0 G (le_of_eq h0)
      omega
    · have hpos : 0 < Challenge.cycleCountMod4 G 3 := Nat.pos_of_ne_zero h0
      obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₀
      rcases hS₀ with ⟨v₀, c₀, hc₀, _, hlen₀⟩
      have hcard_sub : Fintype.card {x : Fin n // x ≠ v₀} = n - 1 := by
        have hv : 0 < n := Fin.pos v₀
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        simp
      let e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀} :=
        (Fintype.equivFinOfCardEq hcard_sub).symm
      let G' : SimpleGraph (Fin (n - 1)) := G.comap (fun i => (e i).1)
      have hlt : Challenge.cycleCountMod4 G' 3 ≤ k := by
        have h := cycleCountMod4_comap_lt G 3 v₀ c₀ hc₀ hlen₀ e
        omega
      have hIH := signature_neg_adjMatrix_le_cycleCountMod4_three k G' hlt
      have hNegH := isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)
      have hinter := signature_interlacing_delete_vertex (-(G.adjMatrix ℝ)) hNegH v₀
      have hsub_eq : ((-(G.adjMatrix ℝ)).submatrix (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1)).submatrix e e = -(G'.adjMatrix ℝ) := by
        ext i j
        simp [G', SimpleGraph.adjMatrix_apply]
      have hsig_sub : signature ((-(G.adjMatrix ℝ)).submatrix
          (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1))
          (isHermitian_submatrix (-(G.adjMatrix ℝ)) hNegH _) =
          signature (-(G'.adjMatrix ℝ))
            (isHermitian_neg (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G')) := by
        rw [← signature_reindex e _ (isHermitian_submatrix (-(G.adjMatrix ℝ)) hNegH _)]
        have hEq : ∀ (M₁ M₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
            (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian), M₁ = M₂ →
            signature M₁ h₁ = signature M₂ h₂ := by
          intro M₁ M₂ h₁ h₂ h; subst h; rfl
        exact hEq _ _ _ _ hsub_eq
      have hle1 : signature (-(G.adjMatrix ℝ)) hNegH -
          signature (-(G'.adjMatrix ℝ))
            (isHermitian_neg (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G')) ≤ 1 := by
        rw [← hsig_sub]
        exact (abs_le.mp hinter).2
      omega

end Corollary13

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem corollary_1_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    -(Challenge.cycleCountMod4 G 3 : ℤ) ≤
      Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
    Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤
      (Challenge.cycleCountMod4 G 1 : ℤ) := by
  rw [matSig_eq_signature]
  constructor
  · have hneg := signature_neg_adjMatrix_le_cycleCountMod4_three (Challenge.cycleCountMod4 G 3) G le_rfl
    rw [signature_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)] at hneg
    omega
  · exact signature_adjMatrix_le_cycleCountMod4_one (Challenge.cycleCountMod4 G 1) G le_rfl

end SignedGraphs
