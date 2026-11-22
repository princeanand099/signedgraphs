import SignedGraphs.Basic

/-!
# Linear Algebra Tools: Switching, Sylvester, Cauchy Interlacing, Weyl Monotonicity

Formalization of Section 2.1 (switching and congruence invariance, bipartite signature = 0)
and the standard matrix inequalities (Sylvester's law of inertia, Cauchy interlacing,
Weyl's monotonicity theorem).
-/

open Matrix SimpleGraph

namespace SignedGraphs

section Switching

variable {V : Type*} [DecidableEq V]

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

end Switching

section MatrixInequalities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Congruence preserves Hermitian property for real matrices. -/
lemma isHermitian_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) :
    (Pᵀ * A * P).IsHermitian := by
  change (Pᵀ * A * P)ᴴ = Pᵀ * A * P
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hP : Pᴴ = Pᵀ := Matrix.conjTranspose_eq_transpose_of_trivial P
  have hPt : (Pᵀ)ᴴ = P := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  rw [hP, hPt, hA.eq, Matrix.mul_assoc]

/-- Negation preserves Hermitian property. -/
lemma isHermitian_neg (A : Matrix V V ℝ) (hA : A.IsHermitian) : (-A).IsHermitian := by
  change (-A)ᴴ = -A
  rw [Matrix.conjTranspose_neg, hA.eq]

/-- Restriction of a Hermitian matrix to a subtype is Hermitian. -/
lemma isHermitian_submatrix {W : Type*} (A : Matrix V V ℝ) (hA : A.IsHermitian) (f : W → V) :
    (A.submatrix f f).IsHermitian := by
  change (A.submatrix f f)ᴴ = A.submatrix f f
  rw [Matrix.conjTranspose_submatrix, hA.eq]

private lemma spectral_quad_form (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    ∃ e : (V → ℝ) ≃ₗ[ℝ] (V → ℝ),
      ∀ x : V → ℝ, dotProduct x (A *ᵥ x) = ∑ i : V, hA.eigenvalues i * (e x i) ^ 2 := by
  let U : Matrix V V ℝ := (hA.eigenvectorUnitary : Matrix V V ℝ)
  have hstar : star U = Uᵀ := Matrix.conjTranspose_eq_transpose_of_trivial U
  have hU_left : Uᵀ * U = 1 := by
    have h : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
    rwa [hstar] at h
  have hU_right : U * Uᵀ = 1 := by
    have h : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
    rwa [hstar] at h
  let e : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
    { toFun := fun x => Uᵀ *ᵥ x
      invFun := fun y => U *ᵥ y
      map_add' := fun x y => Matrix.mulVec_add Uᵀ x y
      map_smul' := fun c x => Matrix.mulVec_smul Uᵀ c x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hU_right]
      right_inv := fun y => by simp [Matrix.mulVec_mulVec, hU_left] }
  refine ⟨e, fun x => ?_⟩
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    have h := hA.spectral_theorem
    change A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U at h
    simpa [hstar] using h
  conv_lhs => rw [hspec]
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  simp only [e, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private def coordSubmodule (P : V → Prop) : Submodule ℝ (V → ℝ) where
  carrier := { y : V → ℝ | ∀ i, ¬ P i → y i = 0 }
  add_mem' ha hb i hi := by simp [ha i hi, hb i hi]
  zero_mem' i _ := rfl
  smul_mem' c a ha i hi := by simp [ha i hi]

private lemma finrank_coordSubmodule (P : V → Prop) [DecidablePred P] :
    Module.finrank ℝ (coordSubmodule P) = (Finset.univ.filter P).card := by
  let e : coordSubmodule P ≃ₗ[ℝ] ({ i : V // P i } → ℝ) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun z => ⟨fun i => if hi : P i then z ⟨i, hi⟩ else 0, fun i hi => by simp [hi]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun y => by
        ext i
        by_cases hi : P i
        · simp [hi]
        · simp [hi, y.2 i hi]
      right_inv := fun z => by
        ext ⟨i, hi⟩
        simp [hi] }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

private lemma posInertia_eq_sSup_aux (d : V → ℝ) :
    (Finset.univ.filter fun i : V => 0 < d i).card =
      sSup { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
        Module.finrank ℝ W = n ∧ ∀ y ∈ W, y ≠ 0 → 0 < ∑ i : V, d i * (y i) ^ 2 } := by
  classical
  let S := { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
    Module.finrank ℝ W = n ∧ ∀ y ∈ W, y ≠ 0 → 0 < ∑ i : V, d i * (y i) ^ 2 }
  have hbdd : BddAbove S := ⟨Fintype.card V, by rintro n ⟨W, rfl, _⟩; simpa using Submodule.finrank_le W⟩
  let Wpos : Submodule ℝ (V → ℝ) := coordSubmodule (fun i => 0 < d i)
  let Wnonpos : Submodule ℝ (V → ℝ) := coordSubmodule (fun i => ¬ (0 < d i))
  have hmem : (Finset.univ.filter fun i : V => 0 < d i).card ∈ S := by
    refine ⟨Wpos, finrank_coordSubmodule (fun i => 0 < d i), fun y hy hy0 => ?_⟩
    have hy_zero : ∀ i, ¬ (0 < d i) → y i = 0 := hy
    have hex : ∃ i, 0 < d i ∧ y i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hy0
      ext i
      by_cases hi : 0 < d i
      · exact hnone i hi
      · exact hy_zero i hi
    rcases hex with ⟨i₀, hd₀, hy₀⟩
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    · by_cases hi : 0 < d i
      · exact mul_nonneg hi.le (sq_nonneg _)
      · simp [hy_zero i hi]
    · exact mul_pos hd₀ (sq_pos_of_ne_zero hy₀)
  refine le_antisymm (le_csSup hbdd hmem) (csSup_le ⟨_, hmem⟩ ?_)
  rintro n ⟨W, rfl, hW⟩
  have hdisj : W ⊓ Wnonpos = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyW, hyN⟩
    by_contra hy0
    have hpos := hW y hyW hy0
    have hle : ∑ i : V, d i * (y i) ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : 0 < d i
      · have hyi : y i = 0 := hyN i (not_not.mpr hi)
        simp [hyi]
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (sq_nonneg _)
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W Wnonpos
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hle_card : Module.finrank ℝ (↥(W ⊔ Wnonpos)) ≤ Fintype.card V :=
    (Submodule.finrank_le (W ⊔ Wnonpos)).trans_eq (Module.finrank_fintype_fun_eq_card ℝ)
  have hnonpos_card : Module.finrank ℝ Wnonpos = (Finset.univ.filter fun i : V => ¬ (0 < d i)).card :=
    finrank_coordSubmodule (fun i => ¬ (0 < d i))
  have hpart : (Finset.univ.filter fun i : V => 0 < d i).card +
      (Finset.univ.filter fun i : V => ¬ (0 < d i)).card = Fintype.card V :=
    Finset.card_filter_add_card_filter_not (fun i : V => 0 < d i)
  omega

/-- Variational characterization of `posInertia`: maximum dimension of a subspace on which
`x ↦ x ⬝ᵥ (A *ᵥ x)` is strictly positive on nonzero vectors. -/
theorem posInertia_eq_sSup (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    posInertia A hA = sSup { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → 0 < dotProduct x (A *ᵥ x) } := by
  obtain ⟨e, he⟩ := spectral_quad_form A hA
  unfold posInertia
  rw [posInertia_eq_sSup_aux hA.eigenvalues]
  congr 1; ext n; constructor
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W.map e.symm.toLinearMap, LinearEquiv.finrank_map_eq e.symm W, ?_⟩
    rintro x hx hx0
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
    change 0 < dotProduct (e.symm y) (A *ᵥ e.symm y)
    rw [he (e.symm y)]
    change 0 < ∑ i : V, hA.eigenvalues i * (e (e.symm y) i) ^ 2
    rw [LinearEquiv.apply_symm_apply]
    exact hW y hy hy0
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W.map e.toLinearMap, LinearEquiv.finrank_map_eq e W, ?_⟩
    rintro y hy hy0
    rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    change 0 < ∑ i : V, hA.eigenvalues i * (e x i) ^ 2
    rw [← he x]
    exact hW x hx hx0

/-- Variational characterization of `negInertia`: maximum dimension of a subspace on which
`x ↦ x ⬝ᵥ (A *ᵥ x)` is strictly negative on nonzero vectors. -/
theorem negInertia_eq_sSup (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    negInertia A hA = sSup { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → dotProduct x (A *ᵥ x) < 0 } := by
  obtain ⟨e, he⟩ := spectral_quad_form A hA
  have hneg_card : (Finset.univ.filter fun i : V => hA.eigenvalues i < 0).card =
      (Finset.univ.filter fun i : V => 0 < -hA.eigenvalues i).card := by
    congr 1; ext i; simp [neg_pos]
  unfold negInertia
  rw [hneg_card, posInertia_eq_sSup_aux (fun i => -hA.eigenvalues i)]
  congr 1; ext n; constructor
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W.map e.symm.toLinearMap, LinearEquiv.finrank_map_eq e.symm W, ?_⟩
    rintro x hx hx0
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
    change dotProduct (e.symm y) (A *ᵥ e.symm y) < 0
    rw [he (e.symm y)]
    change ∑ i : V, hA.eigenvalues i * (e (e.symm y) i) ^ 2 < 0
    rw [LinearEquiv.apply_symm_apply]
    have hypos := hW y hy hy0
    simp only [neg_mul, Finset.sum_neg_distrib, neg_pos] at hypos
    exact hypos
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W.map e.toLinearMap, LinearEquiv.finrank_map_eq e W, ?_⟩
    rintro y hy hy0
    rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    change 0 < ∑ i : V, (-hA.eigenvalues i) * (e x i) ^ 2
    simp only [neg_mul, Finset.sum_neg_distrib, neg_pos]
    rw [← he x]
    exact hW x hx hx0

private lemma posSubspace_bddAbove (A : Matrix V V ℝ) :
    BddAbove { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → 0 < dotProduct x (A *ᵥ x) } := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨W, rfl, _⟩
  simpa using Submodule.finrank_le W

private lemma negSubspace_bddAbove (A : Matrix V V ℝ) :
    BddAbove { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → dotProduct x (A *ᵥ x) < 0 } := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨W, rfl, _⟩
  simpa using Submodule.finrank_le W

/-- Sylvester's law of inertia for signature: `s(Pᵀ * A * P) = s(A)` for invertible `P`. -/
theorem signature_congr (A P : Matrix V V ℝ) (hA : A.IsHermitian) (hP : IsUnit P.det) :
    signature (Pᵀ * A * P) (isHermitian_congr A P hA) = signature A hA := by
  let e : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => P⁻¹ *ᵥ x
      map_add' := fun x y => Matrix.mulVec_add P x y
      map_smul' := fun c x => Matrix.mulVec_smul P c x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP] }
  have hquad : ∀ x : V → ℝ, dotProduct x ((Pᵀ * A * P) *ᵥ x) = dotProduct (e x) (A *ᵥ e x) := by
    intro x
    change dotProduct x ((Pᵀ * A * P) *ᵥ x) = dotProduct (P *ᵥ x) (A *ᵥ (P *ᵥ x))
    rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  have hpos : posInertia (Pᵀ * A * P) (isHermitian_congr A P hA) = posInertia A hA := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e W, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      change 0 < dotProduct (e x) (A *ᵥ e x)
      rw [← hquad x]
      exact hW x hx hx0
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e.symm : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e.symm W, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      change 0 < dotProduct (e.symm y) ((Pᵀ * A * P) *ᵥ e.symm y)
      rw [hquad (e.symm y)]
      change 0 < dotProduct (e (e.symm y)) (A *ᵥ e (e.symm y))
      rw [LinearEquiv.apply_symm_apply]
      exact hW y hy hy0
  have hneg : negInertia (Pᵀ * A * P) (isHermitian_congr A P hA) = negInertia A hA := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e W, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      change dotProduct (e x) (A *ᵥ e x) < 0
      rw [← hquad x]
      exact hW x hx hx0
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map (e.symm : (V → ℝ) →ₗ[ℝ] (V → ℝ)), LinearEquiv.finrank_map_eq e.symm W, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      change dotProduct (e.symm y) ((Pᵀ * A * P) *ᵥ e.symm y) < 0
      rw [hquad (e.symm y)]
      change dotProduct (e (e.symm y)) (A *ᵥ e (e.symm y)) < 0
      rw [LinearEquiv.apply_symm_apply]
      exact hW y hy hy0
  unfold signature
  rw [hpos, hneg]

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
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro v _
    dsimp [d]
    split_ifs <;> norm_num
  have hDAD : Dᵀ * A * D = -A := by
    ext u v
    simp only [D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.neg_apply, d]
    by_cases huv : u = v
    · subst huv; simp [hdiag u]
    · by_cases hAuv : A u v = 0
      · simp [hAuv]
      · have hadj : (matrixGraph A hA.isSymm).Adj u v := ⟨huv, hAuv⟩
        have hne := hf hadj
        have hfu : f u = 0 ∨ f u = 1 := by omega
        have hfv : f v = 0 ∨ f v = 1 := by omega
        rcases hfu with hu | hu <;> rcases hfv with hv | hv
        · exfalso; exact hne (by rw [hu, hv])
        · simp [hu, hv]
        · simp [hu, hv]
        · exfalso; exact hne (by rw [hu, hv])
  have h1 : signature (-A) (isHermitian_neg A hA) = signature A hA := by
    have := signature_congr A D hA hD_det
    simpa [hDAD] using this
  rw [signature_neg A hA] at h1
  omega

/-- Weyl's monotonicity theorem for signature: if `B - A` is positive semidefinite,
then `s(A) ≤ s(B)`. -/
theorem signature_mono_of_posSemidef (A B : Matrix V V ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) :
    signature A hA ≤ signature B hB := by
  have hquad : ∀ x : V → ℝ, dotProduct x (A *ᵥ x) ≤ dotProduct x (B *ᵥ x) := by
    intro x
    have hnn := hAB.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hnn
    exact hnn
  have hpos : posInertia A hA ≤ posInertia B hB := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    refine csSup_le_csSup (posSubspace_bddAbove B) ⟨0, ⊥, finrank_bot ℝ (V → ℝ), fun x hx hx0 => ?_⟩ ?_
    · exfalso; exact hx0 hx
    · rintro n ⟨W, rfl, hW⟩
      exact ⟨W, rfl, fun x hx hx0 => lt_of_lt_of_le (hW x hx hx0) (hquad x)⟩
  have hneg : negInertia B hB ≤ negInertia A hA := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    refine csSup_le_csSup (negSubspace_bddAbove A) ⟨0, ⊥, finrank_bot ℝ (V → ℝ), fun x hx hx0 => ?_⟩ ?_
    · exfalso; exact hx0 hx
    · rintro n ⟨W, rfl, hW⟩
      exact ⟨W, rfl, fun x hx hx0 => lt_of_le_of_lt (hquad x) (hW x hx hx0)⟩
  unfold signature
  omega

/-- Cauchy's interlacing theorem for signature upon deleting one vertex `v`:
`|s(A) - s(A|_{V \ {v}})| ≤ 1`. -/
theorem signature_interlacing_delete_vertex (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
    |signature A hA - signature (A.submatrix (fun x : {x : V // x ≠ v} => x.1)
      (fun x : {x : V // x ≠ v} => x.1)) (isHermitian_submatrix A hA _)| ≤ 1 := by
  let W₀ := {x : V // x ≠ v}
  let A' : Matrix W₀ W₀ ℝ := A.submatrix (fun x : W₀ => x.1) (fun x : W₀ => x.1)
  have hA' : A'.IsHermitian := isHermitian_submatrix A hA _
  let ι : (W₀ → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun y u => if h : u = v then 0 else y ⟨u, h⟩
      map_add' := fun y₁ y₂ => by ext u; by_cases h : u = v <;> simp [h]
      map_smul' := fun c y => by ext u; by_cases h : u = v <;> simp [h] }
  have hι_inj : Function.Injective ι := by
    intro y₁ y₂ h
    ext ⟨u, hu⟩
    have := congrFun h u
    simpa [ι, hu] using this
  have hquad_ι : ∀ y : W₀ → ℝ, dotProduct (ι y) (A *ᵥ ι y) = dotProduct y (A' *ᵥ y) := by
    intro y
    simp only [dotProduct, Matrix.mulVec, ι, A', Matrix.submatrix_apply]
    have hsumV : ∀ f : V → ℝ, f v = 0 →
        (∑ u : V, f u) = ∑ x : W₀, f x.1 := by
      intro f hfv
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ v), hfv, zero_add]
      refine (Finset.sum_bij (fun (x : W₀) _ => x.1)
        (fun x _ => Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩)
        (fun a _ b _ h => Subtype.ext h)
        (fun u hu => ⟨⟨u, (Finset.mem_erase.mp hu).1⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)).symm
    rw [hsumV _ (by simp)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [x.2, ↓reduceDIte]
    congr 1
    rw [hsumV _ (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [z.2, ↓reduceDIte]
  let proj : (V → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj v
  have hker_mem : ∀ x ∈ LinearMap.ker proj, ∃ y : W₀ → ℝ, ι y = x := by
    intro x hx
    refine ⟨fun z => x z.1, ?_⟩
    ext u
    by_cases hu : u = v
    · subst hu
      change (if h : u = u then (0 : ℝ) else _) = x u
      simp only [↓reduceDIte]
      exact Eq.symm (by simpa [proj] using hx)
    · simp [ι, hu]
  have hfinrank_map_ι : ∀ U : Submodule ℝ (W₀ → ℝ), Module.finrank ℝ (U.map ι) = Module.finrank ℝ U :=
    fun U => (Submodule.equivMapOfInjective ι hι_inj U).finrank_eq.symm
  have hpos_le : posInertia A' hA' ≤ posInertia A hA := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    refine csSup_le_csSup (posSubspace_bddAbove A) ⟨0, ⊥, finrank_bot ℝ (W₀ → ℝ), fun y hy hy0 => ?_⟩ ?_
    · exfalso; exact hy0 hy
    · rintro n ⟨U, rfl, hU⟩
      refine ⟨U.map ι, hfinrank_map_ι U, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [hquad_ι y]
      exact hU y hy hy0
  have hneg_le : negInertia A' hA' ≤ negInertia A hA := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    refine csSup_le_csSup (negSubspace_bddAbove A) ⟨0, ⊥, finrank_bot ℝ (W₀ → ℝ), fun y hy hy0 => ?_⟩ ?_
    · exfalso; exact hy0 hy
    · rintro n ⟨U, rfl, hU⟩
      refine ⟨U.map ι, hfinrank_map_ι U, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [hquad_ι y]
      exact hU y hy hy0
  have hsub_codim : ∀ U : Submodule ℝ (V → ℝ),
      Module.finrank ℝ ↥U ≤ Module.finrank ℝ ↥(U ⊓ LinearMap.ker proj) + 1 := by
    intro U
    let f : ↥U →ₗ[ℝ] ℝ := proj.domRestrict U
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hrange : Module.finrank ℝ ↥(LinearMap.range f) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range f)
    have hker_map : (LinearMap.ker f).map U.subtype ≤ U ⊓ LinearMap.ker proj := by
      rintro x ⟨⟨y, hyU⟩, hyker, rfl⟩
      exact ⟨hyU, by simpa [f] using hyker⟩
    have hker_le : Module.finrank ℝ ↥(LinearMap.ker f) ≤ Module.finrank ℝ ↥(U ⊓ LinearMap.ker proj) := by
      have hinj : Function.Injective U.subtype := Subtype.val_injective
      rw [← (Submodule.equivMapOfInjective U.subtype hinj (LinearMap.ker f)).finrank_eq]
      exact Submodule.finrank_mono hker_map
    omega
  have hpos_ge : posInertia A hA ≤ posInertia A' hA' + 1 := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    refine csSup_le ⟨0, ⊥, finrank_bot ℝ (V → ℝ), fun x hx hx0 => by exfalso; exact hx0 hx⟩ ?_
    rintro n ⟨U, rfl, hU⟩
    let U' : Submodule ℝ (W₀ → ℝ) := (U ⊓ LinearMap.ker proj).comap ι
    have hU'_map : U'.map ι = U ⊓ LinearMap.ker proj := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        rcases hker_mem x hx.2 with ⟨y, rfl⟩
        exact ⟨y, hx, rfl⟩
    have hfinU' : Module.finrank ℝ ↥U' = Module.finrank ℝ ↥(U ⊓ LinearMap.ker proj) := by
      rw [← hfinrank_map_ι U', hU'_map]
    have hU'_le : Module.finrank ℝ ↥U' ≤ sSup { m : ℕ | ∃ W₁ : Submodule ℝ (W₀ → ℝ),
        Module.finrank ℝ ↥W₁ = m ∧ ∀ y ∈ W₁, y ≠ 0 → 0 < dotProduct y (A' *ᵥ y) } := by
      refine le_csSup (posSubspace_bddAbove A') ⟨U', rfl, fun y hy hy0 => ?_⟩
      rw [← hquad_ι y]
      exact hU (ι y) hy.1 (fun h => hy0 (hι_inj (by simpa using h)))
    linarith [hsub_codim U]
  have hneg_ge : negInertia A hA ≤ negInertia A' hA' + 1 := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    refine csSup_le ⟨0, ⊥, finrank_bot ℝ (V → ℝ), fun x hx hx0 => by exfalso; exact hx0 hx⟩ ?_
    rintro n ⟨U, rfl, hU⟩
    let U' : Submodule ℝ (W₀ → ℝ) := (U ⊓ LinearMap.ker proj).comap ι
    have hU'_map : U'.map ι = U ⊓ LinearMap.ker proj := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        rcases hker_mem x hx.2 with ⟨y, rfl⟩
        exact ⟨y, hx, rfl⟩
    have hfinU' : Module.finrank ℝ ↥U' = Module.finrank ℝ ↥(U ⊓ LinearMap.ker proj) := by
      rw [← hfinrank_map_ι U', hU'_map]
    have hU'_le : Module.finrank ℝ ↥U' ≤ sSup { m : ℕ | ∃ W₁ : Submodule ℝ (W₀ → ℝ),
        Module.finrank ℝ ↥W₁ = m ∧ ∀ y ∈ W₁, y ≠ 0 → dotProduct y (A' *ᵥ y) < 0 } := by
      refine le_csSup (negSubspace_bddAbove A') ⟨U', rfl, fun y hy hy0 => ?_⟩
      rw [← hquad_ι y]
      exact hU (ι y) hy.1 (fun h => hy0 (hι_inj (by simpa using h)))
    linarith [hsub_codim U]
  unfold signature
  change |(posInertia A hA : ℤ) - negInertia A hA - ((posInertia A' hA' : ℤ) - negInertia A' hA')| ≤ 1
  rw [abs_le]
  omega

end MatrixInequalities

end SignedGraphs
