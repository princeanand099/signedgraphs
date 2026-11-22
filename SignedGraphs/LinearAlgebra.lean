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

/-- Switching a signed graph at a vertex subset `S : Finset V`. -/
def switchSign (S : Finset V) (σ : Sym2 V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun u v => (if u ∈ S then -1 else 1) * (if v ∈ S then -1 else 1) * σ s(u, v), by
    intro u v
    simp [Sym2.eq_swap, mul_comm]⟩

/-- Two signings are switching-equivalent if one is obtained from the other by switching at some `S`. -/
def SwitchingEquiv (σ₁ σ₂ : Sym2 V → ℤ) : Prop :=
  ∃ S : Finset V, ∀ e, σ₂ e = switchSign S σ₁ e

private lemma pm_one_sq (P : Prop) [Decidable P] :
    (if P then (-1 : ℤ) else 1) * (if P then -1 else 1) = 1 := by
  split_ifs <;> norm_num

/-- Switching multiplies the sign product of any `(u, v)`-walk by `s(u) * s(v)`. -/
theorem walkSignProd_switch_aux (S : Finset V) (σ : Sym2 V → ℤ) {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) :
    walkSignProd (switchSign S σ) p =
      (if u ∈ S then (-1 : ℤ) else 1) * (if v ∈ S then (-1 : ℤ) else 1) * walkSignProd σ p := by
  induction p with
  | nil =>
    simp [walkSignProd, pm_one_sq]
  | @cons u w v h p ih =>
    simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
    rw [ih]
    have hsw : switchSign S σ s(u, w) =
        (if u ∈ S then (-1 : ℤ) else 1) * (if w ∈ S then (-1 : ℤ) else 1) * σ s(u, w) := by
      simp [switchSign]
    rw [hsw]
    have hsq : (if w ∈ S then (-1 : ℤ) else 1) * (if w ∈ S then (-1 : ℤ) else 1) = 1 :=
      pm_one_sq (w ∈ S)
    calc
      (if u ∈ S then (-1 : ℤ) else 1) * (if w ∈ S then (-1 : ℤ) else 1) * σ s(u, w) *
          ((if w ∈ S then (-1 : ℤ) else 1) * (if v ∈ S then (-1 : ℤ) else 1) *
            (p.edges.map σ).prod)
        = (if u ∈ S then (-1 : ℤ) else 1) * (if v ∈ S then (-1 : ℤ) else 1) *
            ((if w ∈ S then (-1 : ℤ) else 1) * (if w ∈ S then (-1 : ℤ) else 1)) *
            (σ s(u, w) * (p.edges.map σ).prod) := by ring
      _ = (if u ∈ S then (-1 : ℤ) else 1) * (if v ∈ S then (-1 : ℤ) else 1) *
            (σ s(u, w) * (p.edges.map σ).prod) := by rw [hsq, mul_one]

/-- Switching preserves the sign product of every closed walk (cycle). -/
theorem walkSignProd_switch (S : Finset V) (σ : Sym2 V → ℤ) {G : SimpleGraph V}
    {v : V} (c : G.Walk v v) :
    walkSignProd (switchSign S σ) c = walkSignProd σ c := by
  rw [walkSignProd_switch_aux, pm_one_sq, one_mul]

/-- Switching preserves `{+1, -1}` edge values. -/
lemma switchSign_pm_one (S : SignedGraph V) (T : Finset V) :
    ∀ e ∈ S.graph.edgeSet, switchSign T S.sign e = 1 ∨ switchSign T S.sign e = -1 := by
  intro e he
  rcases e with ⟨u, v⟩
  simp only [switchSign, Sym2.lift_mk]
  rcases S.sign_pm_one s(u, v) he with h | h <;> rw [h] <;> split_ifs <;> simp

/-- Switching preserves the NOC property. -/
theorem isNOC_switch (S : SignedGraph V) (T : Finset V) :
    IsNOC ⟨S.graph, switchSign T S.sign, switchSign_pm_one S T⟩ ↔ IsNOC S := by
  simp only [IsNOC, signedCycleType, walkSignProd_switch]

/-- Congruence preserves Hermitian property for real matrices. -/
lemma isHermitian_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) :
    (Pᵀ * A * P).IsHermitian := by
  change (Pᵀ * A * P)ᴴ = Pᵀ * A * P
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hP : Pᴴ = Pᵀ := Matrix.conjTranspose_eq_transpose_of_trivial P
  have hPt : (Pᵀ)ᴴ = P := by rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  rw [hP, hPt, hA.eq, Matrix.mul_assoc]

/-- Sylvester's law of inertia for signature: `s(Pᵀ * A * P) = s(A)` for invertible `P`. -/
theorem signature_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) (hP : IsUnit P.det) :
    signature (Pᵀ * A * P) (isHermitian_congr A P hA) = signature A hA := by
  sorry

/-- Bipartite signed graphs have signature `0` (Section 2.1). -/
theorem signature_eq_zero_of_bipartite (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ v, A v v = 0) (hbip : (matrixGraph A hA.isSymm).IsBipartite) :
    signature A hA = 0 := by
  sorry

/-- Weyl's monotonicity theorem for signature: if `B - A` is positive semidefinite,
then `s(A) ≤ s(B)`. -/
theorem signature_mono_of_posSemidef (A B : Matrix V V ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) :
    signature A hA ≤ signature B hB := by
  sorry

/-- Restriction of a Hermitian matrix to a subtype is Hermitian. -/
lemma isHermitian_submatrix {W : Type*} (A : Matrix V V ℝ) (hA : A.IsHermitian) (f : W → V) :
    (A.submatrix f f).IsHermitian := by
  change (A.submatrix f f)ᴴ = A.submatrix f f
  rw [Matrix.conjTranspose_submatrix, hA.eq]

/-- Cauchy's interlacing theorem for signature upon deleting one vertex `v`:
`|s(A) - s(A|_{V \ {v}})| ≤ 1`. -/
theorem signature_interlacing_delete_vertex (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
    |signature A hA - signature (A.submatrix (fun x : {x : V // x ≠ v} => x.1)
      (fun x : {x : V // x ≠ v} => x.1)) (isHermitian_submatrix A hA _)| ≤ 1 := by
  sorry

end SignedGraphs
