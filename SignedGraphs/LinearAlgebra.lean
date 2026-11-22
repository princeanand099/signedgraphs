import SignedGraphs.Basic

/-!
# Linear Algebra Tools: Switching, Sylvester, Cauchy Interlacing, Weyl Monotonicity

Formalization of Section 2.1 (switching and congruence invariance, bipartite signature = 0)
and the standard matrix inequalities (Sylvester's law of inertia, Cauchy interlacing,
Weyl's monotonicity theorem).
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
omit [Fintype V] in
theorem walkSignProd_switch_aux (S : Finset V) (σ : Sym2 V → ℤ) {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) :
    walkSignProd (switchSign S σ) p =
      (if u ∈ S then (-1 : ℤ) else 1) * (if v ∈ S then (-1 : ℤ) else 1) * walkSignProd σ p := by
  induction p with
  | nil =>
    simp only [walkSignProd, SimpleGraph.Walk.edges_nil, List.map_nil, List.prod_nil, mul_one]
    exact (pm_one_sq _).symm
  | @cons u w v h p ih =>
    simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
    dsimp only [walkSignProd] at ih
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
omit [Fintype V] in
theorem walkSignProd_switch (S : Finset V) (σ : Sym2 V → ℤ) {G : SimpleGraph V}
    {v : V} (c : G.Walk v v) :
    walkSignProd (switchSign S σ) c = walkSignProd σ c := by
  rw [walkSignProd_switch_aux, pm_one_sq, one_mul]

/-- Switching preserves `{+1, -1}` edge values. -/
omit [Fintype V] in
lemma switchSign_pm_one (S : SignedGraph V) (T : Finset V) :
    ∀ e ∈ S.graph.edgeSet, switchSign T S.sign e = 1 ∨ switchSign T S.sign e = -1 := by
  intro e he
  rcases e with ⟨u, v⟩
  simp only [switchSign, Sym2.lift_mk]
  rcases S.sign_pm_one s(u, v) he with h | h <;> rw [h] <;> split_ifs <;> simp

/-- Switching preserves the NOC property. -/
omit [Fintype V] in
theorem isNOC_switch (S : SignedGraph V) (T : Finset V) :
    IsNOC ⟨S.graph, switchSign T S.sign, switchSign_pm_one S T⟩ ↔ IsNOC S := by
  simp only [IsNOC, signedCycleType, walkSignProd_switch]

/-- Congruence preserves Hermitian property for real matrices. -/
omit [DecidableEq V] in
lemma isHermitian_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) :
    (Pᵀ * A * P).IsHermitian := by
  change (Pᵀ * A * P)ᴴ = Pᵀ * A * P
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hP : Pᴴ = Pᵀ := Matrix.conjTranspose_eq_transpose_of_trivial P
  have hPt : (Pᵀ)ᴴ = P := by rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  rw [hP, hPt, hA.eq, Matrix.mul_assoc]

/-- Quadratic form expansion in the orthonormal eigenbasis of a real symmetric matrix. -/
lemma dotProduct_mulVec_eigenbasis (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) :
    dotProduct x (A *ᵥ x) =
      ∑ i : V, hA.eigenvalues i * (hA.eigenvectorBasis.repr ((WithLp.equiv 2 (V → ℝ)).symm x) i) ^ 2 := by
  let b := hA.eigenvectorBasis
  let xe : EuclideanSpace ℝ V := (WithLp.equiv 2 (V → ℝ)).symm x
  have hmul : A *ᵥ x = (WithLp.equiv 2 (V → ℝ)) (∑ i : V, (hA.eigenvalues i * b.repr xe i) • b i) := by
    have hspec := hA.spectral_theorem
    sorry
  sorry

/-- Variational characterization of `posInertia`: maximum dimension of a subspace on which
`x ↦ x ⬝ᵥ (A *ᵥ x)` is strictly positive on nonzero vectors. -/
theorem posInertia_eq_sSup (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    posInertia A hA = sSup { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → 0 < dotProduct x (A *ᵥ x) } := by
  sorry

/-- Variational characterization of `negInertia`: maximum dimension of a subspace on which
`x ↦ x ⬝ᵥ (A *ᵥ x)` is strictly negative on nonzero vectors. -/
theorem negInertia_eq_sSup (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    negInertia A hA = sSup { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → dotProduct x (A *ᵥ x) < 0 } := by
  sorry

/-- Sylvester's law of inertia for signature: `s(Pᵀ * A * P) = s(A)` for invertible `P`. -/
theorem signature_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) (hP : IsUnit P.det) :
    signature (Pᵀ * A * P) (isHermitian_congr A P hA) = signature A hA := by
  let e : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) := P.toLin'.equivOfDetInvertible hP
  have hquad : ∀ x : V → ℝ, dotProduct x ((Pᵀ * A * P) *ᵥ x) = dotProduct (e x) (A *ᵥ e x) := by
    intro x
    simp only [e, Matrix.toLin'_equivOfDetInvertible_apply, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hpos : posInertia (Pᵀ * A * P) (isHermitian_congr A P hA) = posInertia A hA := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e W, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      rw [← hquad x]
      exact hW x hx hx0
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e.symm : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e.symm W, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [hquad (e.symm y), LinearEquiv.apply_symm_apply]
      exact hW y hy hy0
  have hneg : negInertia (Pᵀ * A * P) (isHermitian_congr A P hA) = negInertia A hA := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e W, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      rw [← hquad x]
      exact hW x hx hx0
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e.symm : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e.symm W, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [hquad (e.symm y), LinearEquiv.apply_symm_apply]
      exact hW y hy hy0
  unfold signature
  rw [hpos, hneg]

/-- Negation preserves Hermitian property. -/
omit [Fintype V] [DecidableEq V] in
lemma isHermitian_neg (A : Matrix V V ℝ) (hA : A.IsHermitian) : (-A).IsHermitian := by
  change (-A)ᴴ = -A
  rw [Matrix.conjTranspose_neg, hA.eq]

/-- Signature of `-A` is `-s(A)`. -/
theorem signature_neg (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    signature (-A) (isHermitian_neg A hA) = -signature A hA := by
  have hpos : posInertia (-A) (isHermitian_neg A hA) = negInertia A hA := by
    rw [posInertia_eq_sSup, negInertia_eq_sSup]
    congr 1; ext n; simp [Matrix.neg_mulVec, dotProduct_neg]
  have hneg : negInertia (-A) (isHermitian_neg A hA) = posInertia A hA := by
    rw [negInertia_eq_sSup, posInertia_eq_sSup]
    congr 1; ext n; simp [Matrix.neg_mulVec, dotProduct_neg]
  unfold signature
  rw [hpos, hneg]
  ring

/-- Bipartite signed graphs have signature `0` (Section 2.1). -/
theorem signature_eq_zero_of_bipartite (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ v, A v v = 0) (hbip : (matrixGraph A hA.isSymm).IsBipartite) :
    signature A hA = 0 := by
  rcases hbip with ⟨f, hf⟩
  let d : V → ℝ := fun v => if f v = 0 then 1 else -1
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.prod_univ _ fun v _ => ?_
    dsimp [d]
    split_ifs <;> norm_num
  have hDAD : Dᵀ * A * D = -A := by
    ext u v
    simp only [D, Matrix.transpose_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.neg_apply, d]
    by_cases huv : u = v
    · subst huv; simp [hdiag u]
    · by_cases hAuv : A u v = 0
      · simp [hAuv]
      · have hadj : (matrixGraph A hA.isSymm).Adj u v := ⟨huv, hAuv⟩
        have hne := hf hadj
        have hfin : f u = 0 ∧ f v = 1 ∨ f u = 1 ∧ f v = 0 := by fin_cases (f u) <;> fin_cases (f v) <;> simp_all
        rcases hfin with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [hu, hv]
  have h1 : signature (-A) (isHermitian_neg A hA) = signature A hA := by
    have := signature_congr A D hA hD_det
    simpa [hDAD] using this
  rw [signature_neg] at h1
  omega

/-- Weyl's monotonicity theorem for signature: if `B - A` is positive semidefinite,
then `s(A) ≤ s(B)`. -/
theorem signature_mono_of_posSemidef (A B : Matrix V V ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) :
    signature A hA ≤ signature B hB := by
  sorry

/-- Restriction of a Hermitian matrix to a subtype is Hermitian. -/
omit [Fintype V] [DecidableEq V] in
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
