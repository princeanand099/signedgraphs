import Mathlib

/-!
# Trusted Pure-Mathlib Definitions for `lake comparator`

Shared, pure-Mathlib definitions imported by both `Challenge` (statements only) and
`Solution` (proofs). Keeping these definitions in a single minimal module guarantees
identical elaborated constants across `Challenge` and `Solution` under `lake comparator`.
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

/-- Number of simple cycle edge-sets in `G` of length congruent to `r` modulo `4`. -/
noncomputable def cycleCountMod4 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
    ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r).card

end SignedGraphs.Challenge
