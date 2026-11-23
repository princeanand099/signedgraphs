import Mathlib
import SignedGraphs.MainTheorem

/-!
# Challenge Statements: Ma–Yang–Li Signature Conjecture

Immutable public theorem statements using only core Lean and Mathlib definitions.
- `main_theorem_noc`: Theorem 1.2 (for every real symmetric zero-diagonal NOC matrix `A`, `s(A) ≤ 0`).
- `ma_yang_li_conjecture`: Corollary 1.3 (for every finite simple graph `G`, `-c₃(G) ≤ s(G) ≤ c₅(G)`).
-/

open Matrix SimpleGraph

namespace SignedGraphs.Challenge

/-- For a real symmetric matrix `A` over `Fin n`, its signature is `n₊(A) - n₋(A)`. -/
noncomputable def matSig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) : ℤ :=
  ((Finset.univ.filter fun i : Fin n => 0 < hA.eigenvalues i).card : ℤ) -
  ((Finset.univ.filter fun i : Fin n => hA.eigenvalues i < 0).card : ℤ)

/-- Underlying graph of a real symmetric matrix `A` on `Fin n`: `i ~ j` iff `i ≠ j ∧ A i j ≠ 0`. -/
def adjGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A i j ≠ 0
  symm := ⟨fun i j h => by
    have hsym : A j i = A i j := congrFun (congrFun hA i) j
    exact ⟨h.1.symm, by rw [hsym]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Sign product along a walk in `Fin n`. -/
noncomputable def walkEntrySignProd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {G : SimpleGraph (Fin n)} : ∀ {u v : Fin n}, G.Walk u v → ℤ
  | _, _, .nil => 1
  | u, _, .cons (v := w) _ p => (if 0 < A u w then 1 else -1) * walkEntrySignProd A p

private lemma matSig_eq_signature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    matSig A hA = SignedGraphs.signature A hA := by
  unfold matSig SignedGraphs.signature SignedGraphs.posInertia SignedGraphs.negInertia
  congr 1

private lemma walkEntrySignProd_eq_walkSignProd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) {u v : Fin n} (p : (SignedGraphs.matrixGraph A hA).Walk u v) :
    walkEntrySignProd A p =
      SignedGraphs.walkSignProd (SignedGraphs.matrixSignedGraph A hA).sign p := by
  induction p with
  | nil => rfl
  | cons _ q ih =>
    simp only [walkEntrySignProd, SignedGraphs.walkSignProd, SimpleGraph.Walk.edges_cons,
      List.map_cons, List.prod_cons]
    rw [← SignedGraphs.walkSignProd, ← ih]
    rfl

/-- **Theorem 1.2 (Main Theorem)**: Every real symmetric zero-diagonal matrix `A` whose
underlying signed graph is NOC satisfies `s(A) ≤ 0`. -/
theorem main_theorem_noc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0)
    (hnoc : ∀ (v : Fin n) (c : (adjGraph A hA.isSymm).Walk v v),
      c.IsCycle → Odd c.length →
      (-1 : ℤ) ^ (c.length / 2) * walkEntrySignProd A c = -1) :
    matSig A hA ≤ 0 := by
  rw [matSig_eq_signature]
  refine SignedGraphs.theorem_1_2 A hA hdiag ?_
  intro v c hc hodd
  unfold SignedGraphs.signedCycleType
  have hprod : walkEntrySignProd A c =
      SignedGraphs.walkSignProd (SignedGraphs.matrixSignedGraph A hA.isSymm).sign c :=
    walkEntrySignProd_eq_walkSignProd A hA.isSymm c
  rw [← hprod]
  exact hnoc v c hc hodd

/-- Number of simple cycle edge-sets in `G` of length congruent to `r` modulo `4`. -/
noncomputable def cycleCountMod4 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
    ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r).card

private lemma cycleCountMod4_eq {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    cycleCountMod4 G r = SignedGraphs.cycleCountMod4 G r := by
  unfold cycleCountMod4 SignedGraphs.cycleCountMod4
  congr 1

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem ma_yang_li_conjecture {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    -(cycleCountMod4 G 3 : ℤ) ≤
      matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
    matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤
      (cycleCountMod4 G 1 : ℤ) := by
  have h1 := matSig_eq_signature (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)
  have h2 := cycleCountMod4_eq G 3
  have h3 := cycleCountMod4_eq G 1
  have hcor := SignedGraphs.corollary_1_3 G
  omega

end SignedGraphs.Challenge
