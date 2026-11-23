import SignedGraphs.Challenge

/-!
# Non-Vacuity Witnesses and Concrete Small-Case Sanity Checks

Verifies that the hypotheses of `SignedGraphs.Challenge.main_theorem_noc` (Theorem 1.2)
and `SignedGraphs.Challenge.ma_yang_li_conjecture` (Corollary 1.3) are non-vacuous by
constructing explicit witnesses for `n = 0, 1, 2, 3`, including a non-bipartite NOC witness
(the complete graph `K₃` with all `+1` edge weights).
-/

open Matrix SimpleGraph SignedGraphs.Challenge

namespace SignedGraphs.SanityChecks

/-- Non-vacuity witness for `main_theorem_noc` at `n = 0`. -/
theorem witness_noc_n0 :
    ∃ (A : Matrix (Fin 0) (Fin 0) ℝ) (hA : A.IsHermitian),
      (∀ i, A i i = 0) ∧
      (∀ (v : Fin 0) (c : (adjGraph A hA.isSymm).Walk v v),
        c.IsCycle → Odd c.length →
        (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) ∧
      matSig A hA ≤ 0 := by
  refine ⟨0, ?_, fun i => i.elim0, fun v => v.elim0, ?_⟩
  · ext i; exact i.elim0
  · exact main_theorem_noc 0 (by ext i; exact i.elim0) (fun i => i.elim0) (fun v => v.elim0)

/-- Non-vacuity witness for `main_theorem_noc` at `n = 1`. -/
theorem witness_noc_n1 :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A.IsHermitian),
      (∀ i, A i i = 0) ∧
      (∀ (v : Fin 1) (c : (adjGraph A hA.isSymm).Walk v v),
        c.IsCycle → Odd c.length →
        (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) ∧
      matSig A hA ≤ 0 := by
  have hA : (0 : Matrix (Fin 1) (Fin 1) ℝ).IsHermitian := by ext i j; simp
  have hnoc : ∀ (v : Fin 1) (c : (adjGraph (0 : Matrix (Fin 1) (Fin 1) ℝ) hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd (0 : Matrix (Fin 1) (Fin 1) ℝ) c = -1 := by
    intro v c hc _
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons h _ => exact absurd rfl h.2
  exact ⟨0, hA, fun _ => rfl, hnoc, main_theorem_noc 0 hA (fun _ => rfl) hnoc⟩

/-- Non-vacuity witness for `main_theorem_noc` at `n = 2` (the non-zero `K₂` adjacency matrix). -/
theorem witness_noc_k2 :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsHermitian),
      (∀ i, A i i = 0) ∧
      (∃ i j, A i j ≠ 0) ∧
      (∀ (v : Fin 2) (c : (adjGraph A hA.isSymm).Walk v v),
        c.IsCycle → Odd c.length →
        (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) ∧
      matSig A hA ≤ 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := (⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ
  have hA : A.IsHermitian := SimpleGraph.isSymm_adjMatrix (⊤ : SimpleGraph (Fin 2))
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A, SimpleGraph.adjMatrix_apply]
  have hnz : ∃ i j, A i j ≠ 0 := ⟨0, 1, by simp [A, SimpleGraph.adjMatrix_apply]⟩
  have hnoc : ∀ (v : Fin 2) (c : (adjGraph A hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1 := by
    intro v c hc _
    have h3 : 3 ≤ c.length := hc.three_le_length
    have hle : c.length ≤ Fintype.card (Fin 2) := by
      have := c.support.tail.toFinset.card_le_univ
      rw [List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
        SimpleGraph.Walk.length_support] at this
      omega
    simp only [Fintype.card_fin] at hle
    omega
  exact ⟨A, hA, hdiag, hnz, hnoc, main_theorem_noc A hA hdiag hnoc⟩

/-- Non-bipartite non-vacuity witness for `main_theorem_noc` at `n = 3`:
the triangle `K₃` with all `+1` edge weights is non-bipartite and NOC. -/
theorem witness_noc_k3_nonbipartite :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian),
      (∀ i, A i i = 0) ∧
      ¬ (adjGraph A hA.isSymm).IsBipartite ∧
      (∀ (v : Fin 3) (c : (adjGraph A hA.isSymm).Walk v v),
        c.IsCycle → Odd c.length →
        (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) ∧
      matSig A hA ≤ 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ
  have hA : A.IsHermitian := SimpleGraph.isSymm_adjMatrix (⊤ : SimpleGraph (Fin 3))
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A, SimpleGraph.adjMatrix_apply]
  have hnb : ¬ (adjGraph A hA.isSymm).IsBipartite := by
    rintro ⟨f⟩
    have h01 : f 0 ≠ f 1 := f.valid ⟨by decide, by simp [A, SimpleGraph.adjMatrix_apply]⟩
    have h12 : f 1 ≠ f 2 := f.valid ⟨by decide, by simp [A, SimpleGraph.adjMatrix_apply]⟩
    have h02 : f 0 ≠ f 2 := f.valid ⟨by decide, by simp [A, SimpleGraph.adjMatrix_apply]⟩
    generalize hf0 : f 0 = c0; generalize hf1 : f 1 = c1; generalize hf2 : f 2 = c2
    rw [hf0, hf1] at h01; rw [hf1, hf2] at h12; rw [hf0, hf2] at h02
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> simp_all
  have hprod_one : ∀ {u v : Fin 3} (p : (adjGraph A hA.isSymm).Walk u v),
      walkEntrySignProd A p = 1 := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons a b _ hab r ih =>
      have hpos : (0 : ℝ) < A a b := by
        simp [A, SimpleGraph.adjMatrix_apply, hab.1]
      simp [walkEntrySignProd, hpos, ih]
  have hnoc : ∀ (v : Fin 3) (c : (adjGraph A hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1 := by
    intro v c hc _
    have h3 : 3 ≤ c.length := hc.three_le_length
    have hle : c.length ≤ Fintype.card (Fin 3) := by
      have := c.support.tail.toFinset.card_le_univ
      rw [List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
        SimpleGraph.Walk.length_support] at this
      omega
    simp only [Fintype.card_fin] at hle
    have hlen : c.length = 3 := by omega
    rw [hlen, hprod_one c]
    norm_num
  exact ⟨A, hA, hdiag, hnb, hnoc, main_theorem_noc A hA hdiag hnoc⟩

/-- Concrete small-case corollaries of `ma_yang_li_conjecture` for `n = 0, 1, 2, 3`. -/
theorem ma_yang_li_small_cases :
    (∀ G : SimpleGraph (Fin 0), ∀ [DecidableRel G.Adj],
      -(cycleCountMod4 G 3 : ℤ) ≤ matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (cycleCountMod4 G 1 : ℤ)) ∧
    (∀ G : SimpleGraph (Fin 1), ∀ [DecidableRel G.Adj],
      -(cycleCountMod4 G 3 : ℤ) ≤ matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (cycleCountMod4 G 1 : ℤ)) ∧
    (∀ G : SimpleGraph (Fin 2), ∀ [DecidableRel G.Adj],
      -(cycleCountMod4 G 3 : ℤ) ≤ matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (cycleCountMod4 G 1 : ℤ)) ∧
    (∀ G : SimpleGraph (Fin 3), ∀ [DecidableRel G.Adj],
      -(cycleCountMod4 G 3 : ℤ) ≤ matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (cycleCountMod4 G 1 : ℤ)) :=
  ⟨fun G _ => ma_yang_li_conjecture G,
   fun G _ => ma_yang_li_conjecture G,
   fun G _ => ma_yang_li_conjecture G,
   fun G _ => ma_yang_li_conjecture G⟩

end SignedGraphs.SanityChecks
