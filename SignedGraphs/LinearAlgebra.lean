import SignedGraphs.Basic

/-!
# Linear Algebra Tools: Switching, Sylvester, Cauchy Interlacing, Weyl Monotonicity

Formalization of Section 2.1 (switching and congruence invariance, bipartite signature = 0)
and the standard matrix inequalities (Sylvester's law of inertia, Cauchy interlacing,
Weyl's monotonicity theorem, Schur-complement signature formula).
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Switching a signed graph at a vertex subset `S ⊆ V`. -/
def switchSign (S : Set V) (σ : Sym2 V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun u v => (if u ∈ S then -1 else 1) * (if v ∈ S then -1 else 1) * σ s(u, v), by
    intro u v
    simp [Sym2.eq_swap, mul_comm, mul_left_comm, mul_assoc]⟩

/-- Two signings are switching-equivalent if one is obtained from the other by switching at some `S`. -/
def SwitchingEquiv (σ₁ σ₂ : Sym2 V → ℤ) : Prop :=
  ∃ S : Set V, ∀ e, σ₂ e = switchSign S σ₁ e

/-- Switching preserves the sign product of every closed walk (cycle). -/
theorem walkSignProd_switch (S : Set V) (σ : Sym2 V → ℤ) {G : SimpleGraph V}
    {v : V} (c : G.Walk v v) :
    walkSignProd (switchSign S σ) c = walkSignProd σ c := by
  sorry

/-- Switching preserves the NOC property. -/
theorem isNOC_switch (S : SignedGraph V) (T : Set V) :
    IsNOC ⟨S.graph, switchSign T S.sign, by sorry⟩ ↔ IsNOC S := by
  sorry

/-- Sylvester's law of inertia for signature: `s(Pᵀ * A * P) = s(A)` for invertible `P`. -/
theorem signature_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) (hP : IsUnit P.det) :
    signature (Pᵀ * A * P) (by sorry) = signature A hA := by
  sorry

/-- Bipartite signed graphs have signature `0` (Section 2.1). -/
theorem signature_eq_zero_of_bipartite (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ v, A v v = 0) (hbip : (matrixGraph A).IsBipartite) :
    signature A hA = 0 := by
  sorry

/-- Weyl's monotonicity theorem for signature: if `B - A` is positive semidefinite,
then `s(A) ≤ s(B)`. -/
theorem signature_mono_of_posSemidef (A B : Matrix V V ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) :
    signature A hA ≤ signature B hB := by
  sorry

/-- Cauchy's interlacing theorem for signature upon deleting one vertex `v`:
`|s(A) - s(A|_{V \ {v}})| ≤ 1`. -/
theorem signature_interlacing_delete_vertex (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
    |signature A hA - signature (A.submatrix (fun x : {x : V // x ≠ v} => x.1)
      (fun x : {x : V // x ≠ v} => x.1)) (by sorry)| ≤ 1 := by
  sorry

end SignedGraphs
