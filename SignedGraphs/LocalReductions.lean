import SignedGraphs.LinearAlgebraExtra

/-!
# Local Algebraic Reductions (Section 2.2)

This file formalizes the two local algebraic reductions of Section 2.2:
* Lemma 2.1 (`cut_vertex_reduction`): Cut-vertex reduction.
* Lemma 2.2 (`degree_two_reduction`): Degree-2 vertex reduction.
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma signature_congr_eq {W : Type*} [Fintype W] [DecidableEq W]
    {M₁ M₂ : Matrix W W ℝ} (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) :
    signature M₁ h₁ = signature M₂ h₂ := by
  subst h; rfl

lemma exists_ker_dotProduct_eq_one {W : Type} [Fintype W] [DecidableEq W]
    (M : Matrix W W ℝ) (hM : M.IsHermitian) (r : W → ℝ) :
    (∃ x : W → ℝ, M *ᵥ x = r) ∨ (∃ u : W → ℝ, M *ᵥ u = 0 ∧ dotProduct u r = 1) := by
  classical
  by_cases h : ∃ x : W → ℝ, M *ᵥ x = r
  · exact Or.inl h
  · right
    let R := LinearMap.range M.mulVecLin
    let K := LinearMap.ker M.mulVecLin
    let φ : (W → ℝ) →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
      { toFun := fun x =>
          { toFun := fun k => dotProduct k.1 x
            map_add' := fun a b => by simp [dotProduct_add]
            map_smul' := fun c a => by simp [smul_dotProduct] }
        map_add' := fun x y => by ext k; simp [dotProduct_add]
        map_smul' := fun c x => by ext k; simp [dotProduct_smul] }
    have hR_le : R ≤ LinearMap.ker φ := by
      rintro x ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      ext ⟨k, hk⟩
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      have hMk : M *ᵥ k = 0 := LinearMap.mem_ker.mp hk
      have hMT : Mᵀ = M := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq
      calc dotProduct k (M.mulVecLin y)
          = dotProduct k (M *ᵥ y) := rfl
        _ = dotProduct (k ᵥ* M) y := Matrix.dotProduct_mulVec k M y
        _ = dotProduct (Mᵀ *ᵥ k) y := by rw [Matrix.mulVec_transpose]
        _ = dotProduct (M *ᵥ k) y := by rw [hMT]
        _ = 0 := by rw [hMk, zero_dotProduct]
    have hφ_surj : Function.Surjective φ := by
      intro f
      obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
      let F : (W → ℝ) →ₗ[ℝ] ℝ := f.comp (K.linearProjOfIsCompl K' hK')
      refine ⟨fun i => F (Pi.single i 1), ?_⟩
      ext ⟨k, hk⟩
      have hk_eq : k = ∑ i : W, k i • Pi.single i (1 : ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      calc φ (fun i => F (Pi.single i 1)) ⟨k, hk⟩
          = ∑ i : W, k i * F (Pi.single i 1) := rfl
        _ = F (∑ i : W, k i • Pi.single i 1) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_smul, smul_eq_mul]
        _ = F k := by rw [← hk_eq]
        _ = f ⟨k, hk⟩ := by
            show f ((K.linearProjOfIsCompl K' hK') k) = f ⟨k, hk⟩
            congr 1
            exact Submodule.linearProjOfIsCompl_apply_left hK' ⟨k, hk⟩
    have hfin_RK : Module.finrank ℝ R + Module.finrank ℝ K = Fintype.card W := by
      simpa [R, K, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have hfin_φ : Module.finrank ℝ (LinearMap.range φ) + Module.finrank ℝ (LinearMap.ker φ) =
        Fintype.card W := by
      simpa [Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker φ
    have hfin_range_φ : Module.finrank ℝ (LinearMap.range φ) = Module.finrank ℝ K := by
      rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, Subspace.dual_finrank_eq]
    have hfin_eq : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.ker φ) := by omega
    have hReq : R = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_eq hR_le hfin_eq
    have hr_not_mem : r ∉ LinearMap.ker φ := by
      rw [← hReq]
      rintro ⟨x, hx⟩
      exact h ⟨x, hx⟩
    rw [LinearMap.mem_ker] at hr_not_mem
    have hex : ∃ k : K, dotProduct k.1 r ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hr_not_mem
      ext k
      exact hnone k
    rcases hex with ⟨⟨k, hk⟩, hkr⟩
    refine ⟨(dotProduct k r)⁻¹ • k, ?_, ?_⟩
    · have hMk : M *ᵥ k = 0 := LinearMap.mem_ker.mp hk
      rw [Matrix.mulVec_smul, hMk, smul_zero]
    · rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hkr]

/-- **Lemma 2.1 (Cut-vertex reduction)**: If `v` is a cut-vertex decomposing `G` into two
induced subgraphs `G₁, G₂` on `V₁, V₂` with `V₁ ∩ V₂ = {v}`, `|V₁| < |V|`, `|V₂| < |V|`,
and Theorem 1.2 holds for all NOC matrices of order strictly less than `|V|`, then `s(A) ≤ 0`. -/
theorem cut_vertex_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (v : V) (V₁ V₂ : Finset V)
    (hunion : V₁ ∪ V₂ = Finset.univ)
    (hinter : V₁ ∩ V₂ = {v})
    (hcard₁ : V₁.card < Fintype.card V)
    (hcard₂ : V₂.card < Fintype.card V)
    (hno_cross : ∀ u ∈ V₁, ∀ w ∈ V₂, u ≠ v → w ≠ v → A u w = 0)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W < Fintype.card V →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ x, B x x = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  classical
  have hv_mem : v ∈ V₁ ∩ V₂ := by rw [hinter]; simp
  have hv₁ : v ∈ V₁ := (Finset.mem_inter.mp hv_mem).1
  have hv₂ : v ∈ V₂ := (Finset.mem_inter.mp hv_mem).2
  let U₁ := {u : V // u ∈ V₁ ∧ u ≠ v}
  let U₂ := {w : V // w ∈ V₂ ∧ w ≠ v}
  have hU₁_not_V₂ : ∀ u : U₁, u.1 ∉ V₂ := by
    intro ⟨u, hu1, huv⟩ hu2
    have : u ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hu1, hu2⟩
    rw [hinter, Finset.mem_singleton] at this
    exact huv this
  have hU₂_not_V₁ : ∀ w : U₂, w.1 ∉ V₁ := by
    intro ⟨w, hw2, hwv⟩ hw1
    have : w ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hw1, hw2⟩
    rw [hinter, Finset.mem_singleton] at this
    exact hwv this
  let e : (Unit ⊕ U₁) ⊕ U₂ ≃ V :=
    { toFun := fun
        | Sum.inl (Sum.inl ()) => v
        | Sum.inl (Sum.inr u) => u.1
        | Sum.inr w => w.1
      invFun := fun x =>
        if hx : x = v then Sum.inl (Sum.inl ())
        else if hx1 : x ∈ V₁ then Sum.inl (Sum.inr ⟨x, hx1, hx⟩)
        else Sum.inr ⟨x, by
          have : x ∈ V₁ ∪ V₂ := by rw [hunion]; exact Finset.mem_univ x
          exact (Finset.mem_union.mp this).resolve_left hx1, hx⟩
      left_inv := fun z => by
        rcases z with ((⟨⟩ | ⟨u, hu1, huv⟩) | ⟨w, hw2, hwv⟩)
        · simp
        · simp [huv, hu1]
        · have hw1 : w ∉ V₁ := hU₂_not_V₁ ⟨w, hw2, hwv⟩
          simp [hwv, hw1]
      right_inv := fun x => by
        by_cases hx : x = v
        · simp [hx]
        · by_cases hx1 : x ∈ V₁ <;> simp [hx, hx1] }
  let f₁ : Unit ⊕ U₁ → V := Sum.elim (fun _ => v) (fun u => u.1)
  have hf₁_inj : Function.Injective f₁ := by
    rintro (⟨⟩ | ⟨u₁, _, hu₁⟩) (⟨⟩ | ⟨u₂, _, hu₂⟩) h
    · rfl
    · exact absurd h.symm hu₂
    · exact absurd h hu₁
    · exact congrArg Sum.inr (Subtype.ext h)
  let f₂ : Unit ⊕ U₂ → V := Sum.elim (fun _ => v) (fun w => w.1)
  have hf₂_inj : Function.Injective f₂ := by
    rintro (⟨⟩ | ⟨w₁, _, hw₁⟩) (⟨⟩ | ⟨w₂, _, hw₂⟩) h
    · rfl
    · exact absurd h.symm hw₂
    · exact absurd h hw₁
    · exact congrArg Sum.inr (Subtype.ext h)
  have hcard_f₁ : Fintype.card (Unit ⊕ U₁) = V₁.card := by
    have e₁ : Unit ⊕ U₁ ≃ {x : V // x ∈ V₁} :=
      { toFun := fun x => ⟨f₁ x, by rcases x with ⟨⟩ | ⟨u, hu1, _⟩; exact hv₁; exact hu1⟩
        invFun := fun x => if hx : x.1 = v then Sum.inl () else Sum.inr ⟨x.1, x.2, hx⟩
        left_inv := fun x => by
          rcases x with ⟨⟩ | ⟨u, hu1, huv⟩
          · simp [f₁]
          · simp [f₁, huv]
        right_inv := fun ⟨x, hx⟩ => by
          by_cases h : x = v <;> simp [f₁, h] }
    rw [Fintype.card_congr e₁, Fintype.card_coe]
  have hcard_f₂ : Fintype.card (Unit ⊕ U₂) = V₂.card := by
    have e₂ : Unit ⊕ U₂ ≃ {x : V // x ∈ V₂} :=
      { toFun := fun x => ⟨f₂ x, by rcases x with ⟨⟩ | ⟨w, hw2, _⟩; exact hv₂; exact hw2⟩
        invFun := fun x => if hx : x.1 = v then Sum.inl () else Sum.inr ⟨x.1, x.2, hx⟩
        left_inv := fun x => by
          rcases x with ⟨⟩ | ⟨w, hw2, hwv⟩
          · simp [f₂]
          · simp [f₂, hwv]
        right_inv := fun ⟨x, hx⟩ => by
          by_cases h : x = v <;> simp [f₂, h] }
    rw [Fintype.card_congr e₂, Fintype.card_coe]
  let A_blk := A.submatrix e e
  have hA_blk : A_blk.IsHermitian := isHermitian_submatrix A hA e
  rw [← signature_reindex e A hA]
  let A₁ : Matrix U₁ U₁ ℝ := A.submatrix (fun u => u.1) (fun u => u.1)
  let A₂ : Matrix U₂ U₂ ℝ := A.submatrix (fun w => w.1) (fun w => w.1)
  have hA₁ : A₁.IsHermitian := isHermitian_submatrix A hA _
  have hA₂ : A₂.IsHermitian := isHermitian_submatrix A hA _
  let AG₁ : Matrix (Unit ⊕ U₁) (Unit ⊕ U₁) ℝ := A.submatrix f₁ f₁
  let AG₂ : Matrix (Unit ⊕ U₂) (Unit ⊕ U₂) ℝ := A.submatrix f₂ f₂
  have hAG₁ : AG₁.IsHermitian := isHermitian_submatrix A hA f₁
  have hAG₂ : AG₂.IsHermitian := isHermitian_submatrix A hA f₂
  have hsA₁ : signature A₁ hA₁ ≤ 0 := by
    refine ih U₁ ?_ A₁ hA₁ (fun u => hdiag u.1)
      (matrixIsNOC_submatrix_injective A hA.isSymm hnoc _ Subtype.coe_injective hA₁.isSymm)
    have : Fintype.card U₁ + 1 = Fintype.card (Unit ⊕ U₁) := by simp [add_comm]
    omega
  have hsA₂ : signature A₂ hA₂ ≤ 0 := by
    refine ih U₂ ?_ A₂ hA₂ (fun w => hdiag w.1)
      (matrixIsNOC_submatrix_injective A hA.isSymm hnoc _ Subtype.coe_injective hA₂.isSymm)
    have : Fintype.card U₂ + 1 = Fintype.card (Unit ⊕ U₂) := by simp [add_comm]
    omega
  have hsG₁ : signature AG₁ hAG₁ ≤ 0 :=
    ih (Unit ⊕ U₁) (by omega) AG₁ hAG₁ (fun x => hdiag (f₁ x))
      (matrixIsNOC_submatrix_injective A hA.isSymm hnoc f₁ hf₁_inj hAG₁.isSymm)
  have hsG₂ : signature AG₂ hAG₂ ≤ 0 :=
    ih (Unit ⊕ U₂) (by omega) AG₂ hAG₂ (fun x => hdiag (f₂ x))
      (matrixIsNOC_submatrix_injective A hA.isSymm hnoc f₂ hf₂_inj hAG₂.isSymm)
  let r₁ : U₁ → ℝ := fun u => A u.1 v
  let r₂ : U₂ → ℝ := fun w => A w.1 v
  have hsym_uv : ∀ x y : V, A x y = A y x := fun x y => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hA.eq x) y).symm
  rcases exists_ker_dotProduct_eq_one A₁ hA₁ r₁ with ⟨x₁, hx₁⟩ | ⟨u, hu_ker, hu_dot⟩
  · rcases exists_ker_dotProduct_eq_one A₂ hA₂ r₂ with ⟨x₂, hx₂⟩ | ⟨u, hu_ker, hu_dot⟩
    · -- Case 2: r₁ ∈ im(A₁) and r₂ ∈ im(A₂)
      let e0 : Unit ⊕ (U₁ ⊕ U₂) ≃ (Unit ⊕ U₁) ⊕ U₂ := (Equiv.sumAssoc Unit U₁ U₂).symm
      let A_blk0 := A_blk.submatrix e0 e0
      have hA_blk0 : A_blk0.IsHermitian := isHermitian_submatrix A_blk hA_blk e0
      rw [← signature_reindex e0 A_blk hA_blk]
      let X : Matrix (U₁ ⊕ U₂) Unit ℝ := Matrix.of fun z _ => Sum.elim x₁ x₂ z
      let P : Matrix (Unit ⊕ (U₁ ⊕ U₂)) (Unit ⊕ (U₁ ⊕ U₂)) ℝ := Matrix.fromBlocks 1 0 (-X) 1
      let Q : Matrix (Unit ⊕ (U₁ ⊕ U₂)) (Unit ⊕ (U₁ ⊕ U₂)) ℝ := Matrix.fromBlocks 1 0 X 1
      have hPQ : P * Q = 1 := by
        simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
      have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
      let c₁ : ℝ := dotProduct r₁ x₁
      let c₂ : ℝ := dotProduct r₂ x₂
      let S₁ : Matrix Unit Unit ℝ := Matrix.of (fun _ _ => -c₁ - c₂)
      let B_diag := Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks A₁ 0 0 A₂)
      have hA_blk0_eq : A_blk0 = Matrix.fromBlocks 0
          (Matrix.of fun _ z => Sum.elim r₁ r₂ z)
          (Matrix.of fun z _ => Sum.elim r₁ r₂ z)
          (Matrix.fromBlocks A₁ 0 0 A₂) := by
        ext a b
        rcases a with ⟨⟩ | (i | i) <;> rcases b with ⟨⟩ | (j | j)
        · simp [A_blk0, A_blk, e0, e, hdiag v]
        · simp [A_blk0, A_blk, e0, e, r₁, hsym_uv v j.1]
        · simp [A_blk0, A_blk, e0, e, r₂, hsym_uv v j.1]
        · simp [A_blk0, A_blk, e0, e, r₁]
        · simp [A_blk0, A_blk, e0, e, A₁]
        · simp [A_blk0, A_blk, e0, e, hno_cross i.1 i.2.1 j.1 j.2.1 i.2.2 j.2.2]
        · simp [A_blk0, A_blk, e0, e, r₂]
        · simp [A_blk0, A_blk, e0, e, hsym_uv i.1 j.1, hno_cross j.1 j.2.1 i.1 i.2.1 j.2.2 i.2.2]
        · simp [A_blk0, A_blk, e0, e, A₂]
      have hcongr : Pᵀ * A_blk0 * P = B_diag := by
        rw [hA_blk0_eq]
        simp only [P, B_diag, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
          Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
          Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        congr 1
        · ext ⟨⟩ ⟨⟩
          have hx₁_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * x₁ k = r₁ i := fun i => congr_fun hx₁ i
          have hx₂_j : ∀ j : U₂, ∑ k : U₂, A₂ j k * x₂ k = r₂ j := fun j => congr_fun hx₂ j
          have hsym1 : ∀ m k : U₁, A₁ m k = A₁ k m := fun m k => hsym_uv m.1 k.1
          have hsym2 : ∀ m k : U₂, A₂ m k = A₂ k m := fun m k => hsym_uv m.1 k.1
          simp only [S₁, X, c₁, c₂, dotProduct, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
            Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fintype.sum_sum_type,
            Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
            Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
            mul_zero, Finset.sum_const_zero, add_zero, zero_add]
          have hzero1 : ∀ k : U₁, r₁ k + -(∑ m : U₁, x₁ m * A₁ m k) = 0 := fun k => by
            have h : ∑ m : U₁, x₁ m * A₁ m k = r₁ k := by
              simpa [hsym1 _ k, mul_comm (x₁ _)] using hx₁_i k
            linarith
          have hzero2 : ∀ k : U₂, r₂ k + -(∑ m : U₂, x₂ m * A₂ m k) = 0 := fun k => by
            have h : ∑ m : U₂, x₂ m * A₂ m k = r₂ k := by
              simpa [hsym2 _ k, mul_comm (x₂ _)] using hx₂_j k
            linarith
          have h3 : ∑ k : U₁, x₁ k * r₁ k = ∑ k : U₁, r₁ k * x₁ k :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          have h4 : ∑ k : U₂, x₂ k * r₂ k = ∑ k : U₂, r₂ k * x₂ k :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          simp only [hzero1, hzero2, zero_mul, Finset.sum_const_zero, neg_zero, add_zero, h3, h4]
          ring
        · ext ⟨⟩ z
          rcases z with i | j
          · have hx₁_i : ∑ k : U₁, A₁ i k * x₁ k = r₁ i := congr_fun hx₁ i
            have hsym1 : ∀ k : U₁, A₁ k i = A₁ i k := fun k => hsym_uv k.1 i.1
            simp only [X, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.of_apply, Matrix.zero_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, mul_zero, Finset.sum_const_zero,
              add_zero]
            simp only [hsym1, mul_comm (x₁ _), hx₁_i]
            ring
          · have hx₂_j : ∑ k : U₂, A₂ j k * x₂ k = r₂ j := congr_fun hx₂ j
            have hsym2 : ∀ k : U₂, A₂ k j = A₂ j k := fun k => hsym_uv k.1 j.1
            simp only [X, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.of_apply, Matrix.zero_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, mul_zero, Finset.sum_const_zero,
              zero_add]
            simp only [hsym2, mul_comm (x₂ _), hx₂_j]
            ring
        · ext z ⟨⟩
          rcases z with i | j
          · have hx₁_i : ∑ k : U₁, A₁ i k * x₁ k = r₁ i := congr_fun hx₁ i
            simp only [X, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
              Matrix.zero_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, zero_mul, Finset.sum_const_zero,
              add_zero, hx₁_i]
            ring
          · have hx₂_j : ∑ k : U₂, A₂ j k * x₂ k = r₂ j := congr_fun hx₂ j
            simp only [X, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
              Matrix.zero_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, zero_mul, Finset.sum_const_zero,
              zero_add, hx₂_j]
            ring
      have hS₁ : S₁.IsHermitian := by ext ⟨⟩ ⟨⟩; simp [S₁, Matrix.conjTranspose_apply]
      have hsB_diag : signature A_blk0 hA_blk0 = signature S₁ hS₁ + (signature A₁ hA₁ + signature A₂ hA₂) := by
        rw [← signature_congr A_blk0 P hA_blk0 hP_det]
        rw [signature_congr_eq (isHermitian_congr A_blk0 P hA_blk0)
          (isHermitian_fromBlocks S₁ hS₁ _ (isHermitian_fromBlocks A₁ hA₁ A₂ hA₂)) hcongr]
        rw [signature_fromBlocks S₁ hS₁ _ (isHermitian_fromBlocks A₁ hA₁ A₂ hA₂),
            signature_fromBlocks A₁ hA₁ A₂ hA₂]
      rw [hsB_diag]
      have hM₁ : (Matrix.of (fun _ _ : Unit => -c₁)).IsHermitian := by
        ext ⟨⟩ ⟨⟩; simp [Matrix.conjTranspose_apply]
      have hM₂ : (Matrix.of (fun _ _ : Unit => -c₂)).IsHermitian := by
        ext ⟨⟩ ⟨⟩; simp [Matrix.conjTranspose_apply]
      have hsG₁_split : signature AG₁ hAG₁ =
          signature (Matrix.of (fun _ _ : Unit => -c₁)) hM₁ + signature A₁ hA₁ := by
        let X₁ : Matrix U₁ Unit ℝ := Matrix.of fun i _ => x₁ i
        let P₁ : Matrix (Unit ⊕ U₁) (Unit ⊕ U₁) ℝ := Matrix.fromBlocks 1 0 (-X₁) 1
        let Q₁ : Matrix (Unit ⊕ U₁) (Unit ⊕ U₁) ℝ := Matrix.fromBlocks 1 0 X₁ 1
        have hPQ₁ : P₁ * Q₁ = 1 := by simp [P₁, Q₁, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
        have hP₁_det : IsUnit P₁.det := isUnit_iff_exists_inv.mpr ⟨Q₁.det, by rw [← Matrix.det_mul, hPQ₁, Matrix.det_one]⟩
        have hAG₁_eq : AG₁ = Matrix.fromBlocks 0 (Matrix.of fun _ i => r₁ i) (Matrix.of fun i _ => r₁ i) A₁ := by
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j
          · simp [AG₁, f₁, hdiag v]
          · simp [AG₁, f₁, r₁, hsym_uv v j.1]
          · simp [AG₁, f₁, r₁]
          · simp [AG₁, f₁, A₁]
        have hcongr₁ : P₁ᵀ * AG₁ * P₁ = Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => -c₁)) 0 0 A₁ := by
          rw [hAG₁_eq]
          simp only [P₁, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
            Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
            Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
          congr 1
          · ext ⟨⟩ ⟨⟩
            have hx₁_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * x₁ k = r₁ i := fun i => congr_fun hx₁ i
            have hsym1 : ∀ m k : U₁, A₁ m k = A₁ k m := fun m k => hsym_uv m.1 k.1
            simp only [X₁, c₁, dotProduct, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply,
              Matrix.transpose_apply, Matrix.of_apply]
            have hzero1 : ∀ k : U₁, r₁ k + -(∑ m : U₁, x₁ m * A₁ m k) = 0 := fun k => by
              have h : ∑ m : U₁, x₁ m * A₁ m k = r₁ k := by
                simpa [hsym1 _ k, mul_comm (x₁ _)] using hx₁_i k
              linarith
            have h3 : ∑ k : U₁, x₁ k * r₁ k = ∑ k : U₁, r₁ k * x₁ k :=
              Finset.sum_congr rfl fun k _ => mul_comm _ _
            simp only [hzero1, zero_mul, Finset.sum_const_zero, neg_zero, add_zero, h3]
          · ext ⟨⟩ i
            have hx₁_i : ∑ k : U₁, A₁ i k * x₁ k = r₁ i := congr_fun hx₁ i
            have hsym1 : ∀ k : U₁, A₁ k i = A₁ i k := fun k => hsym_uv k.1 i.1
            simp only [X₁, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.of_apply, Matrix.zero_apply, hsym1, mul_comm (x₁ _), hx₁_i]
            ring
          · ext i ⟨⟩
            have hx₁_i : ∑ k : U₁, A₁ i k * x₁ k = r₁ i := congr_fun hx₁ i
            simp only [X₁, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
              Matrix.zero_apply, hx₁_i]
            ring
        rw [← signature_congr AG₁ P₁ hAG₁ hP₁_det]
        rw [signature_congr_eq (isHermitian_congr AG₁ P₁ hAG₁)
          (isHermitian_fromBlocks _ hM₁ A₁ hA₁) hcongr₁]
        exact signature_fromBlocks _ hM₁ A₁ hA₁
      have hsG₂_split : signature AG₂ hAG₂ =
          signature (Matrix.of (fun _ _ : Unit => -c₂)) hM₂ + signature A₂ hA₂ := by
        let X₂ : Matrix U₂ Unit ℝ := Matrix.of fun i _ => x₂ i
        let P₂ : Matrix (Unit ⊕ U₂) (Unit ⊕ U₂) ℝ := Matrix.fromBlocks 1 0 (-X₂) 1
        let Q₂ : Matrix (Unit ⊕ U₂) (Unit ⊕ U₂) ℝ := Matrix.fromBlocks 1 0 X₂ 1
        have hPQ₂ : P₂ * Q₂ = 1 := by simp [P₂, Q₂, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
        have hP₂_det : IsUnit P₂.det := isUnit_iff_exists_inv.mpr ⟨Q₂.det, by rw [← Matrix.det_mul, hPQ₂, Matrix.det_one]⟩
        have hAG₂_eq : AG₂ = Matrix.fromBlocks 0 (Matrix.of fun _ i => r₂ i) (Matrix.of fun i _ => r₂ i) A₂ := by
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j
          · simp [AG₂, f₂, hdiag v]
          · simp [AG₂, f₂, r₂, hsym_uv v j.1]
          · simp [AG₂, f₂, r₂]
          · simp [AG₂, f₂, A₂]
        have hcongr₂ : P₂ᵀ * AG₂ * P₂ = Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => -c₂)) 0 0 A₂ := by
          rw [hAG₂_eq]
          simp only [P₂, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
            Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
            Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
          congr 1
          · ext ⟨⟩ ⟨⟩
            have hx₂_j : ∀ j : U₂, ∑ k : U₂, A₂ j k * x₂ k = r₂ j := fun j => congr_fun hx₂ j
            have hsym2 : ∀ m k : U₂, A₂ m k = A₂ k m := fun m k => hsym_uv m.1 k.1
            simp only [X₂, c₂, dotProduct, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply,
              Matrix.transpose_apply, Matrix.of_apply]
            have hzero2 : ∀ k : U₂, r₂ k + -(∑ m : U₂, x₂ m * A₂ m k) = 0 := fun k => by
              have h : ∑ m : U₂, x₂ m * A₂ m k = r₂ k := by
                simpa [hsym2 _ k, mul_comm (x₂ _)] using hx₂_j k
              linarith
            have h3 : ∑ k : U₂, x₂ k * r₂ k = ∑ k : U₂, r₂ k * x₂ k :=
              Finset.sum_congr rfl fun k _ => mul_comm _ _
            simp only [hzero2, zero_mul, Finset.sum_const_zero, neg_zero, add_zero, h3]
          · ext ⟨⟩ i
            have hx₂_i : ∑ k : U₂, A₂ i k * x₂ k = r₂ i := congr_fun hx₂ i
            have hsym2 : ∀ k : U₂, A₂ k i = A₂ i k := fun k => hsym_uv k.1 i.1
            simp only [X₂, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.of_apply, Matrix.zero_apply, hsym2, mul_comm (x₂ _), hx₂_i]
            ring
          · ext i ⟨⟩
            have hx₂_i : ∑ k : U₂, A₂ i k * x₂ k = r₂ i := congr_fun hx₂ i
            simp only [X₂, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
              Matrix.zero_apply, hx₂_i]
            ring
        rw [← signature_congr AG₂ P₂ hAG₂ hP₂_det]
        rw [signature_congr_eq (isHermitian_congr AG₂ P₂ hAG₂)
          (isHermitian_fromBlocks _ hM₂ A₂ hA₂) hcongr₂]
        exact signature_fromBlocks _ hM₂ A₂ hA₂
      by_cases hneg : signature A₁ hA₁ ≤ -1 ∨ signature A₂ hA₂ ≤ -1
      · have hS₁_le : signature S₁ hS₁ ≤ 1 := signature_one_by_one_le_one (-c₁ - c₂) hS₁
        omega
      · push Not at hneg
        have h01 : signature A₁ hA₁ = 0 := by omega
        have h02 : signature A₂ hA₂ = 0 := by omega
        have hc1_le : -c₁ ≤ 0 := signature_one_by_one_le_zero_iff (-c₁) hM₁ (by omega)
        have hc2_le : -c₂ ≤ 0 := signature_one_by_one_le_zero_iff (-c₂) hM₂ (by omega)
        have hS₁_le : signature S₁ hS₁ ≤ 0 :=
          signature_one_by_one_nonpos (-c₁ - c₂) (by linarith) hS₁
        omega
    · -- Case 1b: r₂ ∉ im(A₂), decouple G₂ ⊕ A₁
      let e2 : (Unit ⊕ U₂) ⊕ U₁ ≃ (Unit ⊕ U₁) ⊕ U₂ :=
        { toFun := fun
            | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
            | Sum.inl (Sum.inr w) => Sum.inr w
            | Sum.inr u => Sum.inl (Sum.inr u)
          invFun := fun
            | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
            | Sum.inl (Sum.inr u) => Sum.inr u
            | Sum.inr w => Sum.inl (Sum.inr w)
          left_inv := fun x => by rcases x with (⟨⟩ | w) | u <;> rfl
          right_inv := fun x => by rcases x with (⟨⟩ | u) | w <;> rfl }
      let A_blk2 := A_blk.submatrix e2 e2
      have hA_blk2 : A_blk2.IsHermitian := isHermitian_submatrix A_blk hA_blk e2
      rw [← signature_reindex e2 A_blk hA_blk]
      let Y : Matrix (Unit ⊕ U₂) U₁ ℝ := Matrix.of fun a i => match a with
        | Sum.inl () => 0
        | Sum.inr w => u w * r₁ i
      let P : Matrix ((Unit ⊕ U₂) ⊕ U₁) ((Unit ⊕ U₂) ⊕ U₁) ℝ := Matrix.fromBlocks 1 (-Y) 0 1
      let Q : Matrix ((Unit ⊕ U₂) ⊕ U₁) ((Unit ⊕ U₂) ⊕ U₁) ℝ := Matrix.fromBlocks 1 Y 0 1
      have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
      have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
      let R₁ : Matrix (Unit ⊕ U₂) U₁ ℝ := Matrix.of fun a i => match a with
        | Sum.inl () => r₁ i
        | Sum.inr _ => 0
      have hA_blk2_eq : A_blk2 = Matrix.fromBlocks AG₂ R₁ R₁ᵀ A₁ := by
        ext a b
        rcases a with (⟨⟩ | w) | i <;> rcases b with (⟨⟩ | w') | j
        · simp [A_blk2, A_blk, e2, e, AG₂, f₂]
        · simp [A_blk2, A_blk, e2, e, AG₂, f₂]
        · simp [A_blk2, A_blk, e2, e, R₁, r₁, hsym_uv v j.1]
        · simp [A_blk2, A_blk, e2, e, AG₂, f₂]
        · simp [A_blk2, A_blk, e2, e, AG₂, f₂]
        · simp [A_blk2, A_blk, e2, e, R₁, hsym_uv w.1 j.1, hno_cross j.1 j.2.1 w.1 w.2.1 j.2.2 w.2.2]
        · simp [A_blk2, A_blk, e2, e, R₁, r₁]
        · simp [A_blk2, A_blk, e2, e, R₁, hno_cross i.1 i.2.1 w'.1 w'.2.1 i.2.2 w'.2.2]
        · simp [A_blk2, A_blk, e2, e, A₁]
      have hAG₂_Y : AG₂ * Y = R₁ := by
        have hu_ker_w : ∀ w : U₂, ∑ k : U₂, A₂ w k * u k = 0 := fun w => congr_fun hu_ker w
        ext a i
        rcases a with ⟨⟩ | w
        · simp only [AG₂, f₂, Y, R₁, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type,
            Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_add]
          calc ∑ k : U₂, A v k.1 * (u k * r₁ i)
              = (∑ k : U₂, u k * r₂ k) * r₁ i := by
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
                simp [r₂, hsym_uv v k.1]; ring
            _ = r₁ i := by change dotProduct u r₂ * r₁ i = r₁ i; rw [hu_dot, one_mul]
        · simp only [AG₂, f₂, Y, R₁, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type,
            Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_add]
          calc ∑ k : U₂, A w.1 k.1 * (u k * r₁ i)
              = (∑ k : U₂, A₂ w k * u k) * r₁ i := by
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; simp [A₂]; ring
            _ = 0 := by rw [hu_ker_w w, zero_mul]
      have hYT_R₁ : Yᵀ * R₁ = 0 := by
        ext i j
        simp [Y, R₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
      have hcongr : Pᵀ * A_blk2 * P = Matrix.fromBlocks AG₂ 0 0 A₁ := by
        rw [hA_blk2_eq]
        simp only [P, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
          Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
          Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        have hAG₂T : AG₂ᵀ = AG₂ := by
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hAG₂.eq
        have hYT_AG₂ : Yᵀ * AG₂ = R₁ᵀ := by
          calc Yᵀ * AG₂ = Yᵀ * AG₂ᵀ := by rw [hAG₂T]
            _ = (AG₂ * Y)ᵀ := (Matrix.transpose_mul AG₂ Y).symm
            _ = R₁ᵀ := by rw [hAG₂_Y]
        congr 1
        · rw [hAG₂_Y, neg_add_cancel]
        · rw [hYT_AG₂, neg_add_cancel]
        · rw [hYT_AG₂, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, hYT_R₁, neg_zero, zero_add]
      rw [← signature_congr A_blk2 P hA_blk2 hP_det]
      rw [signature_congr_eq (isHermitian_congr A_blk2 P hA_blk2)
        (isHermitian_fromBlocks AG₂ hAG₂ A₁ hA₁) hcongr]
      rw [signature_fromBlocks AG₂ hAG₂ A₁ hA₁]
      omega
  · -- Case 1a: r₁ ∉ im(A₁), decouple G₁ ⊕ A₂
    let Y : Matrix (Unit ⊕ U₁) U₂ ℝ := Matrix.of fun a j => match a with
      | Sum.inl () => 0
      | Sum.inr i => u i * r₂ j
    let P : Matrix ((Unit ⊕ U₁) ⊕ U₂) ((Unit ⊕ U₁) ⊕ U₂) ℝ := Matrix.fromBlocks 1 (-Y) 0 1
    let Q : Matrix ((Unit ⊕ U₁) ⊕ U₂) ((Unit ⊕ U₁) ⊕ U₂) ℝ := Matrix.fromBlocks 1 Y 0 1
    have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
    let R₂ : Matrix (Unit ⊕ U₁) U₂ ℝ := Matrix.of fun a j => match a with
      | Sum.inl () => r₂ j
      | Sum.inr _ => 0
    have hA_blk_eq : A_blk = Matrix.fromBlocks AG₁ R₂ R₂ᵀ A₂ := by
      ext a b
      rcases a with (⟨⟩ | i) | j <;> rcases b with (⟨⟩ | i') | j'
      · simp [A_blk, e, AG₁, f₁]
      · simp [A_blk, e, AG₁, f₁]
      · simp [A_blk, e, R₂, r₂, hsym_uv v j'.1]
      · simp [A_blk, e, AG₁, f₁]
      · simp [A_blk, e, AG₁, f₁]
      · simp [A_blk, e, R₂, hno_cross i.1 i.2.1 j'.1 j'.2.1 i.2.2 j'.2.2]
      · simp [A_blk, e, R₂, r₂]
      · simp [A_blk, e, R₂, hsym_uv j.1 i'.1, hno_cross i'.1 i'.2.1 j.1 j.2.1 i'.2.2 j.2.2]
      · simp [A_blk, e, A₂]
    have hAG₁_Y : AG₁ * Y = R₂ := by
      have hu_ker_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * u k = 0 := fun i => congr_fun hu_ker i
      ext a j
      rcases a with ⟨⟩ | i
      · simp only [AG₁, f₁, Y, R₂, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type,
          Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_add]
        calc ∑ k : U₁, A v k.1 * (u k * r₂ j)
            = (∑ k : U₁, u k * r₁ k) * r₂ j := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
              simp [r₁, hsym_uv v k.1]; ring
          _ = r₂ j := by change dotProduct u r₁ * r₂ j = r₂ j; rw [hu_dot, one_mul]
      · simp only [AG₁, f₁, Y, R₂, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type,
          Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_add]
        calc ∑ k : U₁, A i.1 k.1 * (u k * r₂ j)
            = (∑ k : U₁, A₁ i k * u k) * r₂ j := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; simp [A₁]; ring
          _ = 0 := by rw [hu_ker_i i, zero_mul]
    have hYT_R₂ : Yᵀ * R₂ = 0 := by
      ext i j
      simp [Y, R₂, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
    have hcongr : Pᵀ * A_blk * P = Matrix.fromBlocks AG₁ 0 0 A₂ := by
      rw [hA_blk_eq]
      simp only [P, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
        Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      have hAG₁T : AG₁ᵀ = AG₁ := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hAG₁.eq
      have hYT_AG₁ : Yᵀ * AG₁ = R₂ᵀ := by
        calc Yᵀ * AG₁ = Yᵀ * AG₁ᵀ := by rw [hAG₁T]
          _ = (AG₁ * Y)ᵀ := (Matrix.transpose_mul AG₁ Y).symm
          _ = R₂ᵀ := by rw [hAG₁_Y]
      congr 1
      · rw [hAG₁_Y, neg_add_cancel]
      · rw [hYT_AG₁, neg_add_cancel]
      · rw [hYT_AG₁, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, hYT_R₂, neg_zero, zero_add]
    rw [← signature_congr A_blk P hA_blk hP_det]
    rw [signature_congr_eq (isHermitian_congr A_blk P hA_blk)
      (isHermitian_fromBlocks AG₁ hAG₁ A₂ hA₂) hcongr]
    rw [signature_fromBlocks AG₁ hAG₁ A₂ hA₂]
    omega

private lemma sign_diff_cases (a b : ℝ) (hab : a - b ≠ 0) :
    (a ≠ 0 ∧ (if 0 < a then (1 : ℤ) else -1) = (if 0 < a - b then 1 else -1)) ∨
    (b ≠ 0 ∧ (if 0 < b then (1 : ℤ) else -1) = -(if 0 < a - b then 1 else -1)) := by
  by_cases hpos : 0 < a - b
  · by_cases ha : 0 < a
    · exact Or.inl ⟨ne_of_gt ha, by simp [ha, hpos]⟩
    · have hb : b < 0 := by linarith
      exact Or.inr ⟨ne_of_lt hb, by simp [not_lt.mpr hb.le, hpos]⟩
  · have hneg : a - b < 0 := lt_of_le_of_ne (not_lt.mp hpos) hab
    by_cases ha : a < 0
    · exact Or.inl ⟨ne_of_lt ha, by simp [not_lt.mpr ha.le, hpos]⟩
    · have hb : 0 < b := by linarith
      exact Or.inr ⟨ne_of_gt hb, by simp [hb, hpos]⟩

private lemma walk_eq_append_last {W : Type*} {G : SimpleGraph W} {a b : W}
    (q : G.Walk a b) (hlen : 0 < q.length) :
    ∃ (c : W) (p : G.Walk a c) (h : G.Adj c b),
      q = p.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) := by
  induction q with
  | nil => simp at hlen
  | @cons u v w hadj r ih =>
    cases r with
    | nil => exact ⟨u, SimpleGraph.Walk.nil, hadj, rfl⟩
    | @cons v₁ v₂ v₃ h₂ r' =>
      obtain ⟨c, p, h, hr⟩ := ih (by simp)
      exact ⟨c, SimpleGraph.Walk.cons hadj p, h, by rw [hr]; rfl⟩

/-- **Lemma 2.2 (Degree-2 vertex reduction)**: If `v` has degree 2 in `G(A)` (with `|V| ≥ 3`)
and Theorem 1.2 holds for all NOC matrices of order `|V| - 2`, then `s(A) ≤ 0`. -/
set_option maxHeartbeats 800000 in
theorem degree_two_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (hn : 3 ≤ Fintype.card V)
    (v x y : V) (hxy : x ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (hN : ∀ w, (matrixGraph A hA.isSymm).Adj v w ↔ w = x ∨ w = y)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W = Fintype.card V - 2 →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ z, B z z = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  classical
  have hAvx_ne : A v x ≠ 0 := ((hN x).mpr (Or.inl rfl)).2
  have hAvy_ne : A v y ≠ 0 := ((hN y).mpr (Or.inr rfl)).2
  have hAvw_zero : ∀ w : V, w ≠ x → w ≠ y → A v w = 0 := by
    intro w hwx hwy
    by_cases hwv : w = v
    · rw [hwv]; exact hdiag v
    · by_contra hne
      have hadj : (matrixGraph A hA.isSymm).Adj v w := ⟨Ne.symm hwv, hne⟩
      rcases (hN w).mp hadj with rfl | rfl <;> contradiction
  let d : V → ℝ := fun u => if u = x then (A v x)⁻¹ else if u = y then (A v y)⁻¹ else 1
  have hd_ne : ∀ u, d u ≠ 0 := by
    intro u
    dsimp [d]
    split_ifs <;> simp [hAvx_ne, hAvy_ne]
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun u _ => hd_ne u)
  let B : Matrix V V ℝ := Dᵀ * A * D
  have hB : B.IsHermitian := isHermitian_congr A D hA
  have hB_eq : B = Matrix.diagonal d * A * Matrix.diagonal d := by
    simp [B, D, Matrix.diagonal_transpose]
  have hB_diag : ∀ u, B u u = 0 := fun u => by
    simp [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, hdiag u]
  have hB_noc : MatrixIsNOC B hB.isSymm := by
    have hB_sym : (Matrix.diagonal d * A * Matrix.diagonal d).IsSymm := hB_eq ▸ hB.isSymm
    have h := matrixIsNOC_diagonal_congr A hA.isSymm hnoc d hd_ne hB_sym
    simpa [hB_eq] using h
  have hB_vx : B v x = 1 := by
    simp [B, D, d, Matrix.diagonal_mul, Matrix.mul_diagonal, hvx, hvy, hAvx_ne]
  have hB_vy : B v y = 1 := by
    simp [B, D, d, Matrix.diagonal_mul, Matrix.mul_diagonal, hvx, hvy, hxy.symm, hAvy_ne]
  have hB_vw : ∀ w : V, w ≠ x → w ≠ y → B v w = 0 := fun w hwx hwy => by
    simp [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, hAvw_zero w hwx hwy]
  have hsym_B : ∀ a b : V, B a b = B b a := fun a b => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq a) b).symm
  rw [← signature_congr A D hA hD_det]
  change signature B hB ≤ 0
  have hBxy_nonneg : 0 ≤ B x y := by
    by_contra hneg
    push Not at hneg
    have hBxy_ne : B x y ≠ 0 := ne_of_lt hneg
    let c : (matrixSignedGraph B hB.isSymm).graph.Walk v v :=
      SimpleGraph.Walk.cons ⟨hvx, by rw [hB_vx]; norm_num⟩
        (SimpleGraph.Walk.cons ⟨hxy, hBxy_ne⟩
          (SimpleGraph.Walk.cons ⟨hvy.symm, by rw [hsym_B, hB_vy]; norm_num⟩ SimpleGraph.Walk.nil))
    have hlen_c : c.length = 3 := rfl
    have hedges_c : c.edges = [s(v, x), s(x, y), s(y, v)] := rfl
    have hsupp_c : c.support.tail = [x, y, v] := rfl
    have hc_cyc : c.IsCycle := by
      refine ⟨⟨⟨?_⟩, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by rw [hlen_c]; simp)⟩, ?_⟩
      · rw [hedges_c]
        simp [Sym2.eq_iff, hxy, hvx, hvy, hvx.symm, hvy.symm, hxy.symm]
      · rw [hsupp_c]
        simp [hxy, hvx.symm, hvy.symm]
    have hodd : Odd c.length := ⟨1, rfl⟩
    have hnoc_c := hB_noc v c hc_cyc hodd
    have hsign_c : signedCycleType (matrixSignedGraph B hB.isSymm).sign c = 1 := by
      rw [signedCycleType, walkSignProd, hlen_c, hedges_c]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        matrixSignedGraph, Sym2.lift_mk, hB_vx, hsym_B y v, hB_vy, not_lt.mpr hneg.le]
      norm_num
    rw [hsign_c] at hnoc_c
    norm_num at hnoc_c
  let U := {w : V // w ≠ v ∧ w ≠ x ∧ w ≠ y}
  let e : Fin 3 ⊕ U ≃ V :=
    { toFun := fun
        | Sum.inl 0 => v
        | Sum.inl 1 => x
        | Sum.inl 2 => y
        | Sum.inr w => w.1
      invFun := fun z =>
        if hz0 : z = v then Sum.inl 0
        else if hz1 : z = x then Sum.inl 1
        else if hz2 : z = y then Sum.inl 2
        else Sum.inr ⟨z, hz0, hz1, hz2⟩
      left_inv := fun z => by
        rcases z with i | ⟨w, hwv, hwx, hwy⟩
        · fin_cases i <;> simp [hvx.symm, hvy.symm, hxy.symm]
        · simp [hwv, hwx, hwy]
      right_inv := fun z => by
        by_cases hz0 : z = v
        · simp [hz0]
        · by_cases hz1 : z = x
          · simp [hz0, hz1, hvx.symm]
          · by_cases hz2 : z = y
            · simp [hz0, hz1, hz2, hvy.symm, hxy.symm]
            · simp [hz0, hz1, hz2] }
  have hcard_U : Fintype.card (Unit ⊕ U) = Fintype.card V - 2 := by
    have hcard_e : 3 + Fintype.card U = Fintype.card V := by
      simpa [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
    simp [Fintype.card_sum]
    omega
  let B_blk := B.submatrix e e
  have hB_blk : B_blk.IsHermitian := isHermitian_submatrix B hB e
  rw [← signature_reindex e B hB]
  let P₃ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 1; 0, 1, -1]
  let Q₃ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, (1/2 : ℝ), (1/2 : ℝ); 0, (1/2 : ℝ), -(1/2 : ℝ)]
  let P₁ : Matrix (Fin 3 ⊕ U) (Fin 3 ⊕ U) ℝ := Matrix.fromBlocks P₃ 0 0 1
  let Q₁ : Matrix (Fin 3 ⊕ U) (Fin 3 ⊕ U) ℝ := Matrix.fromBlocks Q₃ 0 0 1
  have hPQ₃ : P₃ * Q₃ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [P₃, Q₃, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hPQ₁ : P₁ * Q₁ = 1 := by
    simp [P₁, Q₁, Matrix.fromBlocks_multiply, hPQ₃, Matrix.fromBlocks_one]
  have hP₁_det : IsUnit P₁.det := isUnit_iff_exists_inv.mpr ⟨Q₁.det, by rw [← Matrix.det_mul, hPQ₁, Matrix.det_one]⟩
  rw [← signature_congr B_blk P₁ hB_blk hP₁_det]
  let Btilde := P₁ᵀ * B_blk * P₁
  have hBtilde : Btilde.IsHermitian := isHermitian_congr B_blk P₁ hB_blk
  let e₂ : Fin 2 ⊕ (Unit ⊕ U) ≃ Fin 3 ⊕ U :=
    { toFun := fun
        | Sum.inl 0 => Sum.inl 0
        | Sum.inl 1 => Sum.inl 1
        | Sum.inr (Sum.inl ()) => Sum.inl 2
        | Sum.inr (Sum.inr w) => Sum.inr w
      invFun := fun
        | Sum.inl 0 => Sum.inl 0
        | Sum.inl 1 => Sum.inl 1
        | Sum.inl 2 => Sum.inr (Sum.inl ())
        | Sum.inr w => Sum.inr (Sum.inr w)
      left_inv := fun a => by
        rcases a with i | (⟨⟩ | w)
        · fin_cases i <;> rfl
        · rfl
        · rfl
      right_inv := fun a => by
        rcases a with i | w
        · fin_cases i <;> rfl
        · rfl }
  let Btilde₂ := Btilde.submatrix e₂ e₂
  have hBtilde₂ : Btilde₂.IsHermitian := isHermitian_submatrix Btilde hBtilde e₂
  rw [← signature_reindex e₂ Btilde hBtilde]
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 2, 2 * B x y]
  let R : Matrix (Fin 2) (Unit ⊕ U) ℝ := Matrix.of fun i z => match i, z with
    | 0, _ => 0
    | 1, Sum.inl () => 0
    | 1, Sum.inr u => B x u.1 + B y u.1
  let A' : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ := Matrix.of fun a b => match a, b with
    | Sum.inl (), Sum.inl () => -2 * B x y
    | Sum.inl (), Sum.inr u => B x u.1 - B y u.1
    | Sum.inr u, Sum.inl () => B u.1 x - B u.1 y
    | Sum.inr u, Sum.inr w => B u.1 w.1
  have hBtilde_blk : Btilde = Matrix.fromBlocks
      (P₃ᵀ * B_blk.toBlocks₁₁ * P₃) (P₃ᵀ * B_blk.toBlocks₁₂)
      (B_blk.toBlocks₂₁ * P₃) B_blk.toBlocks₂₂ := by
    have hBblk_split : B_blk = Matrix.fromBlocks B_blk.toBlocks₁₁ B_blk.toBlocks₁₂
        B_blk.toBlocks₂₁ B_blk.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks B_blk).symm
    have hP1T : P₁ᵀ = Matrix.fromBlocks P₃ᵀ 0 0 1 := by
      simp [P₁, Matrix.fromBlocks_transpose]
    calc Btilde = P₁ᵀ * B_blk * P₁ := rfl
      _ = Matrix.fromBlocks P₃ᵀ 0 0 1 *
            Matrix.fromBlocks B_blk.toBlocks₁₁ B_blk.toBlocks₁₂ B_blk.toBlocks₂₁ B_blk.toBlocks₂₂ *
            Matrix.fromBlocks P₃ 0 0 1 := by rw [hP1T, hBblk_split]
      _ = _ := by
            simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  have hBtilde₂_eq : Btilde₂ = Matrix.fromBlocks H R Rᵀ A' := by
    ext a b
    simp only [Btilde₂, Matrix.submatrix_apply, hBtilde_blk]
    rcases a with i | (⟨⟩ | u) <;> rcases b with j | (⟨⟩ | w)
    · fin_cases i <;> fin_cases j <;>
        simp [e₂, B_blk, e, P₃, H, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x] <;> ring
    · fin_cases i <;>
        simp [e₂, B_blk, e, P₃, R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x] <;> ring
    · fin_cases i <;>
        simp [e₂, B_blk, e, P₃, R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          hB_vw w.1 w.2.2.1 w.2.2.2]
    · fin_cases j <;>
        simp [e₂, B_blk, e, P₃, R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x] <;> ring
    · simp [e₂, B_blk, e, P₃, A', Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        hB_diag v, hB_diag x, hB_diag y, hsym_B y x]
      ring
    · simp [e₂, B_blk, e, P₃, A', Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        sub_eq_add_neg]
    · fin_cases j <;>
        simp [e₂, B_blk, e, P₃, R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          hsym_B u.1 v, hB_vw u.1 u.2.2.1 u.2.2.2, hsym_B x u.1, hsym_B y u.1]
    · simp [e₂, B_blk, e, P₃, A', Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        sub_eq_add_neg]
    · simp [e₂, B_blk, e, A']
  let S : Matrix (Fin 2) (Unit ⊕ U) ℝ := Matrix.of fun i z => match i, z with
    | 0, Sum.inl () => 0
    | 0, Sum.inr u => (B x u.1 + B y u.1) / 2
    | 1, _ => 0
  let P₂ : Matrix (Fin 2 ⊕ (Unit ⊕ U)) (Fin 2 ⊕ (Unit ⊕ U)) ℝ := Matrix.fromBlocks 1 (-S) 0 1
  let Q₂ : Matrix (Fin 2 ⊕ (Unit ⊕ U)) (Fin 2 ⊕ (Unit ⊕ U)) ℝ := Matrix.fromBlocks 1 S 0 1
  have hPQ₂ : P₂ * Q₂ = 1 := by simp [P₂, Q₂, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hP₂_det : IsUnit P₂.det := isUnit_iff_exists_inv.mpr ⟨Q₂.det, by rw [← Matrix.det_mul, hPQ₂, Matrix.det_one]⟩
  rw [← signature_congr Btilde₂ P₂ hBtilde₂ hP₂_det]
  have hHS : H * S = R := by
    ext i z
    fin_cases i <;> rcases z with ⟨⟩ | u <;>
      simp [H, S, R, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hST_R : Sᵀ * R = 0 := by
    ext z z'
    rcases z with ⟨⟩ | u <;> rcases z' with ⟨⟩ | w <;>
      simp [S, R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  have hH : H.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]
  have hHT : Hᵀ = H := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.eq
  have hcongr₂ : P₂ᵀ * Btilde₂ * P₂ = Matrix.fromBlocks H 0 0 A' := by
    rw [hBtilde₂_eq]
    simp only [P₂, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hST_H : Sᵀ * H = Rᵀ := by
      calc Sᵀ * H = Sᵀ * Hᵀ := by rw [hHT]
        _ = (H * S)ᵀ := (Matrix.transpose_mul H S).symm
        _ = Rᵀ := by rw [hHS]
    congr 1
    · rw [hHS, neg_add_cancel]
    · rw [hST_H, neg_add_cancel]
    · rw [hST_H, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, hST_R, neg_zero, zero_add]
  have hA' : A'.IsHermitian := by
    ext a b
    rcases a with ⟨⟩ | u <;> rcases b with ⟨⟩ | w <;>
      simp [A', Matrix.conjTranspose_apply, hsym_B]
  rw [signature_congr_eq (isHermitian_congr Btilde₂ P₂ hBtilde₂)
    (isHermitian_fromBlocks H hH A' hA') hcongr₂]
  rw [signature_fromBlocks H hH A' hA']
  have hsH : signature H hH = 0 := signature_two_by_two_offdiag 2 (2 * B x y) (by norm_num) hH
  rw [hsH, zero_add]
  let A'₀ : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ := Matrix.of fun a b => match a, b with
    | Sum.inl (), Sum.inl () => 0
    | Sum.inl (), Sum.inr u => B x u.1 - B y u.1
    | Sum.inr u, Sum.inl () => B u.1 x - B u.1 y
    | Sum.inr u, Sum.inr w => B u.1 w.1
  have hA'₀ : A'₀.IsHermitian := by
    ext a b
    rcases a with ⟨⟩ | u <;> rcases b with ⟨⟩ | w <;>
      simp [A'₀, Matrix.conjTranspose_apply, hsym_B]
  have hA'_le : signature A' hA' ≤ signature A'₀ hA'₀ := by
    refine signature_mono_of_posSemidef A' A'₀ hA' hA'₀ ?_
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA'₀.sub hA', fun z => ?_⟩
    have hdiff : ∀ a, ((A'₀ - A') *ᵥ z) a = if a = Sum.inl () then 2 * B x y * z (Sum.inl ()) else 0 := by
      intro a
      rcases a with ⟨⟩ | u
      · simp [Matrix.mulVec, dotProduct, A'₀, A', Fintype.sum_sum_type]
      · simp [Matrix.mulVec, dotProduct, A'₀, A', Fintype.sum_sum_type]
    simp only [star_trivial, dotProduct, hdiff, Fintype.sum_sum_type, Finset.univ_unique,
      Finset.sum_singleton, PUnit.default_eq_unit, ↓reduceIte, Sum.inl.injEq, reduceCtorEq,
      mul_zero, Finset.sum_const_zero, add_zero]
    nlinarith [sq_nonneg (z (Sum.inl ()))]
  have hA'₀_diag : ∀ z, A'₀ z z = 0 := by
    intro z
    rcases z with ⟨⟩ | u
    · simp [A'₀]
    · simp [A'₀, hB_diag u.1]
  let projU : Unit ⊕ U → V := fun | Sum.inl () => v | Sum.inr u => u.1
  have hprojU_inj : ∀ a b : Unit ⊕ U, a ≠ Sum.inl () → b ≠ Sum.inl () → projU a = projU b → a = b := by
    intro a b ha hb hEq
    rcases a with ⟨⟩ | u₁
    · exact absurd rfl ha
    · rcases b with ⟨⟩ | u₂
      · exact absurd rfl hb
      · exact congrArg Sum.inr (Subtype.ext hEq)
  have hlift : ∀ {a b : U} (p : (matrixSignedGraph A'₀ hA'₀.isSymm).graph.Walk (Sum.inr a) (Sum.inr b)),
      Sum.inl () ∉ p.support →
      ∃ q : (matrixSignedGraph B hB.isSymm).graph.Walk a.1 b.1,
        q.length = p.length ∧
        walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
          walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign p ∧
        q.support = p.support.map projU ∧
        q.edges = p.edges.map (Sym2.map projU) := by
    have hrec : ∀ {s t : Unit ⊕ U} (p : (matrixSignedGraph A'₀ hA'₀.isSymm).graph.Walk s t),
        Sum.inl () ∉ p.support →
        ∀ (as : U) (bs : U), s = Sum.inr as → t = Sum.inr bs →
        ∃ q : (matrixSignedGraph B hB.isSymm).graph.Walk as.1 bs.1,
          q.length = p.length ∧
          walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
            walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign p ∧
          q.support = p.support.map projU ∧
          q.edges = p.edges.map (Sym2.map projU) := by
      intro s t p
      induction p with
      | nil =>
        intro _ as bs hs ht
        have hEq : as = bs := Sum.inr.inj (hs.symm.trans ht)
        subst hEq
        exact ⟨SimpleGraph.Walk.nil, rfl, rfl, by simp [hs, projU], rfl⟩
      | @cons s₁ s₂ s₃ hadj p ih =>
        intro hnot as bs hs ht
        have hs₂ : ∃ u₂ : U, s₂ = Sum.inr u₂ := by
          cases s₂ with
          | inl u =>
            cases u
            exfalso
            apply hnot
            simp [SimpleGraph.Walk.support_cons]
          | inr u₂ => exact ⟨u₂, rfl⟩
        rcases hs₂ with ⟨u₂, hu₂⟩
        have hnot_p : Sum.inl () ∉ p.support := fun hm =>
          hnot (by simp [SimpleGraph.Walk.support_cons, hm])
        obtain ⟨q', hq'len, hq'sign, hq'supp, hq'edges⟩ := ih hnot_p u₂ bs hu₂ ht
        have hadjB : (matrixSignedGraph B hB.isSymm).graph.Adj as.1 u₂.1 := by
          subst hs; subst hu₂
          refine ⟨fun h => hadj.1 (congrArg Sum.inr (Subtype.ext h)), ?_⟩
          simpa [matrixSignedGraph, matrixGraph, A'₀] using hadj.2
        refine ⟨SimpleGraph.Walk.cons hadjB q', by simp [hq'len], ?_, ?_, ?_⟩
        · subst hs; subst hu₂
          simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
          have h1 : (matrixSignedGraph B hB.isSymm).sign s(as.1, u₂.1) =
              (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(Sum.inr as, Sum.inr u₂) := rfl
          rw [h1]
          exact congrArg _ hq'sign
        · simp [SimpleGraph.Walk.support_cons, hs, projU, hq'supp]
        · subst hs; subst hu₂
          simp [SimpleGraph.Walk.edges_cons, projU, hq'edges]
    intro a b p hnot
    exact hrec p hnot a b rfl rfl
  have hA'₀_noc : MatrixIsNOC A'₀ hA'₀.isSymm := by
    intro z₀ c hc hodd
    let top : Unit ⊕ U := Sum.inl ()
    by_cases htop : top ∈ c.support
    · let c₀ := c.rotate top htop
      have hc₀ : c₀.IsCycle := hc.rotate htop
      have hlen₀ : c₀.length = c.length := SimpleGraph.Walk.length_rotate c top htop
      have hodd₀ : Odd c₀.length := hlen₀.symm ▸ hodd
      have hsign_rot : walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ =
          walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c := by
        have hperm : c₀.edges.Perm c.edges := by
          have h1 : c₀.edges = (c.dropUntil top htop).edges ++ (c.takeUntil top htop).edges := by
            simp [c₀, SimpleGraph.Walk.rotate, SimpleGraph.Walk.edges_append]
          have h2 : c.edges = (c.takeUntil top htop).edges ++ (c.dropUntil top htop).edges := by
            conv_lhs => rw [← SimpleGraph.Walk.take_spec c htop]
            exact SimpleGraph.Walk.edges_append _ _
          rw [h1, h2]
          exact List.perm_append_comm
        simp only [walkSignProd]
        exact (hperm.map _).prod_eq
      have htype_eq : signedCycleType (matrixSignedGraph A'₀ hA'₀.isSymm).sign c =
          signedCycleType (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
        simp [signedCycleType, hlen₀, hsign_rot]
      rw [htype_eq]
      cases hc₀_eq : c₀ with
      | nil => exact absurd hc₀_eq hc₀.ne_nil
      | @cons _ a₁ _ h₁ q =>
        have ha₁ : ∃ w₁ : U, a₁ = Sum.inr w₁ := by
          cases a₁ with
          | inl u => cases u; exact absurd rfl h₁.1
          | inr w₁ => exact ⟨w₁, rfl⟩
        rcases ha₁ with ⟨w₁, rfl⟩
        have hq_pos : 0 < q.length := by
          have h3 := hc₀.three_le_length
          rw [hc₀_eq, SimpleGraph.Walk.length_cons] at h3
          omega
        obtain ⟨a₂, p, h₂_adj, hq_eq⟩ := walk_eq_append_last q hq_pos
        have ha₂ : ∃ w₂ : U, a₂ = Sum.inr w₂ := by
          cases a₂ with
          | inl u => cases u; exact absurd rfl h₂_adj.1
          | inr w₂ => exact ⟨w₂, rfl⟩
        rcases ha₂ with ⟨w₂, rfl⟩
        have h₂ : (matrixSignedGraph A'₀ hA'₀.isSymm).graph.Adj top (Sum.inr w₂) := h₂_adj.symm
        have hc₀_supp : c₀.support.tail.Nodup := hc₀.support_nodup
        rw [hc₀_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at hc₀_supp
        have hq_supp : q.support = p.support ++ [top] := by
          rw [hq_eq, SimpleGraph.Walk.support_append]
          simp
        rw [hq_supp] at hc₀_supp
        have hp_nd : p.support.Nodup := (List.nodup_append.mp hc₀_supp).1
        have htop_not_p : Sum.inl () ∉ p.support := fun hm =>
          (List.nodup_append.mp hc₀_supp).2.2 top hm top (List.mem_singleton_self top) rfl
        obtain ⟨P, hPlen, hPsign, hPsupp, _⟩ := hlift p htop_not_p
        have hP_path : P.IsPath := by
          refine SimpleGraph.Walk.IsPath.mk' ?_
          rw [hPsupp]
          refine List.Nodup.map_on ?_ hp_nd
          intro a ha b hb hEq
          exact hprojU_inj a b (fun h => htop_not_p (h ▸ ha)) (fun h => htop_not_p (h ▸ hb)) hEq
        have hP_avoid : ∀ z ∈ P.support, z ≠ v ∧ z ≠ x ∧ z ≠ y := by
          intro z hz
          rw [hPsupp] at hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rcases w with ⟨⟩ | u
          · exact absurd hw htop_not_p
          · exact u.2
        have hclen : c₀.length = P.length + 2 := by
          rw [hc₀_eq, SimpleGraph.Walk.length_cons, hq_eq, SimpleGraph.Walk.length_append]
          simp [hPlen]
        have hcsign : walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ =
            (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) *
            walkSignProd (matrixSignedGraph B hB.isSymm).sign P *
            (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
          rw [hc₀_eq, hq_eq, hPsign]
          simp only [walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
            SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
            List.prod_cons, List.prod_append, List.prod_nil, mul_one, Sym2.eq_swap]
          ring
        have h1_ne : B x w₁.1 - B y w₁.1 ≠ 0 := by simpa [matrixSignedGraph, matrixGraph, A'₀, top] using h₁.2
        have h2_ne : B x w₂.1 - B y w₂.1 ≠ 0 := by simpa [matrixSignedGraph, matrixGraph, A'₀, top] using h₂.2
        have hcase1 := sign_diff_cases (B x w₁.1) (B y w₁.1) h1_ne
        have hcase2 := sign_diff_cases (B x w₂.1) (B y w₂.1) h2_ne
        have hw12 : w₁.1 ≠ w₂.1 := by
          intro hEq
          have hw : w₁ = w₂ := Subtype.ext hEq
          have h3 : 3 ≤ c₀.length := hc₀.three_le_length
          have hplen : 1 ≤ p.length := by omega
          cases hp : p with
          | nil => simp [hp] at hplen
          | @cons _ z _ hadjp r =>
            subst hw
            have hr_end : Sum.inr w₁ ∈ r.support := SimpleGraph.Walk.end_mem_support r
            rw [hp, SimpleGraph.Walk.support_cons, List.nodup_cons] at hp_nd
            exact hp_nd.1 hr_end
        have h_edge_cycle : ∀ (u₀ : V) (hu₀ : u₀ ∉ P.support)
            (ha : (matrixSignedGraph B hB.isSymm).graph.Adj u₀ w₁.1)
            (hb : (matrixSignedGraph B hB.isSymm).graph.Adj w₂.1 u₀),
            (SimpleGraph.Walk.cons ha (P.append (SimpleGraph.Walk.cons hb SimpleGraph.Walk.nil))).IsCycle := by
          intro u₀ hu₀ ha hb
          refine ⟨⟨⟨?_⟩, fun h => by cases h⟩, ?_⟩
          · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
              SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons]
            refine ⟨?_, ?_⟩
            · intro hm
              rcases List.mem_append.mp hm with hmP | hm2
              · exact hu₀ (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
              · simp only [List.mem_singleton] at hm2
                rcases Sym2.eq_iff.mp hm2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                · exact (matrixSignedGraph B hB.isSymm).graph.ne_of_adj hb h1'.symm
                · exact hw12 h2'
            · rw [List.nodup_append]
              refine ⟨hP_path.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
              intro e' he' e₂ he₂
              simp only [List.mem_singleton] at he₂
              subst he₂
              intro hEq
              subst hEq
              exact hu₀ (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
          · rw [SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_append]
            simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
            rw [List.nodup_append]
            refine ⟨hP_path.support_nodup, List.nodup_singleton _, ?_⟩
            intro a ha' b hb' hEq
            simp only [List.mem_singleton] at hb'
            subst hb'; subst hEq
            exact hu₀ ha'
        rcases hcase1 with ⟨hx1_ne, hx1_s⟩ | ⟨hy1_ne, hy1_s⟩ <;>
          rcases hcase2 with ⟨hx2_ne, hx2_s⟩ | ⟨hy2_ne, hy2_s⟩
        · have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
          have hadj1 : (matrixSignedGraph B hB.isSymm).graph.Adj x w₁.1 := ⟨w₁.2.2.1.symm, hx1_ne⟩
          have hadj2 : (matrixSignedGraph B hB.isSymm).graph.Adj w₂.1 x := ⟨w₂.2.2.1, by rwa [hsym_B]⟩
          let cyc := SimpleGraph.Walk.cons hadj1 (P.append (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil))
          have hcyc : cyc.IsCycle := h_edge_cycle x hx_notP hadj1 hadj2
          have hcyc_len : cyc.length = c₀.length := by simp [cyc, hclen]
          have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
              walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
            rw [hcsign]
            simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
              SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
              List.prod_cons, List.prod_append, List.prod_nil, mul_one]
            have hs1 : (matrixSignedGraph B hB.isSymm).sign s(x, w₁.1) =
                (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
              simpa [matrixSignedGraph, A'₀, top] using hx1_s
            have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, x) =
                (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
              rw [Sym2.eq_swap]
              simpa [matrixSignedGraph, A'₀, top] using hx2_s
            rw [hs1, hs2]; ring
          have hnoc_cyc := hB_noc x cyc hcyc (hcyc_len.symm ▸ hodd₀)
          rw [← hc₀_eq, signedCycleType, ← hcyc_len, ← hcyc_sign]
          exact hnoc_cyc
        · have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
          have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
          have hv_notP : v ∉ P.support := fun hm => (hP_avoid v hm).1 rfl
          have hadj1 : (matrixSignedGraph B hB.isSymm).graph.Adj x w₁.1 := ⟨w₁.2.2.1.symm, hx1_ne⟩
          have hadj2 : (matrixSignedGraph B hB.isSymm).graph.Adj w₂.1 y := ⟨w₂.2.2.2, by rwa [hsym_B]⟩
          have hadj3 : (matrixSignedGraph B hB.isSymm).graph.Adj y v := ⟨hvy.symm, by rw [hsym_B, hB_vy]; norm_num⟩
          have hadj4 : (matrixSignedGraph B hB.isSymm).graph.Adj v x := ⟨hvx, by rw [hB_vx]; norm_num⟩
          let tailW := SimpleGraph.Walk.cons hadj2
            (SimpleGraph.Walk.cons hadj3 (SimpleGraph.Walk.cons hadj4 SimpleGraph.Walk.nil))
          let cyc := SimpleGraph.Walk.cons hadj1 (P.append tailW)
          have hcyc : cyc.IsCycle := by
            refine ⟨⟨⟨?_⟩, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by simp [cyc])⟩, ?_⟩
            · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append, List.nodup_cons]
              refine ⟨?_, ?_⟩
              · intro hm
                rcases List.mem_append.mp hm with hmP | hmt
                · exact hx_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
                · simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                    List.mem_cons, List.not_mem_nil, or_false] at hmt
                  rcases hmt with h | h | h
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                    · exact w₂.2.2.1 h1'.symm
                    · exact hxy h1'
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                    · exact hxy h1'
                    · exact hvx h1'.symm
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                    · exact hvx h1'.symm
                    · exact w₁.2.1 h2'
              · rw [List.nodup_append]
                refine ⟨hP_path.isTrail.edges_nodup, ?_, ?_⟩
                · simp [tailW, w₂.2.1, w₂.2.2.1, w₂.2.2.2, hxy, hvx, hvy, hxy.symm, hvx.symm, hvy.symm, Sym2.eq_swap]
                · intro e' he' e₂ he₂ hEq
                  subst hEq
                  simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                    List.mem_cons, List.not_mem_nil, or_false] at he₂
                  rcases he₂ with rfl | rfl | rfl
                  · exact hy_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
                  · exact hv_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
                  · exact hx_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
            · rw [SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_append]
              simp only [tailW, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
              rw [List.nodup_append]
              refine ⟨hP_path.support_nodup, by simp [hvy.symm, hxy.symm, hvx], ?_⟩
              intro a ha' b hb' hEq
              subst hEq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
              rcases hb' with rfl | rfl | rfl
              · exact hy_notP ha'
              · exact hv_notP ha'
              · exact hx_notP ha'
          have hcyc_len : cyc.length = c₀.length + 2 := by simp [cyc, tailW, hclen]
          have hcyc_odd : Odd cyc.length := by rcases hodd₀ with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
          have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
              - walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
            rw [hcsign]
            simp only [cyc, tailW, walkSignProd, SimpleGraph.Walk.edges_cons,
              SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_nil,
              List.map_cons, List.map_append, List.map_nil,
              List.prod_cons, List.prod_append, List.prod_nil, mul_one]
            have hs1 : (matrixSignedGraph B hB.isSymm).sign s(x, w₁.1) =
                (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
              simpa [matrixSignedGraph, A'₀, top] using hx1_s
            have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, y) =
                -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
              rw [Sym2.eq_swap]
              simpa [matrixSignedGraph, A'₀, top] using hy2_s
            have hs3 : (matrixSignedGraph B hB.isSymm).sign s(y, v) = 1 := by
              simp [matrixSignedGraph, hsym_B y v, hB_vy]
            have hs4 : (matrixSignedGraph B hB.isSymm).sign s(v, x) = 1 := by
              simp [matrixSignedGraph, hB_vx]
            rw [hs1, hs2, hs3, hs4]; ring
          have hnoc_cyc := hB_noc x cyc hcyc hcyc_odd
          rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
          have hdiv : (c₀.length + 2) / 2 = c₀.length / 2 + 1 := by omega
          rw [hdiv, pow_succ] at hnoc_cyc
          rw [← hc₀_eq, signedCycleType]
          linarith
        · have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
          have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
          have hv_notP : v ∉ P.support := fun hm => (hP_avoid v hm).1 rfl
          have hadj1 : (matrixSignedGraph B hB.isSymm).graph.Adj y w₁.1 := ⟨w₁.2.2.2.symm, hy1_ne⟩
          have hadj2 : (matrixSignedGraph B hB.isSymm).graph.Adj w₂.1 x := ⟨w₂.2.2.1, by rwa [hsym_B]⟩
          have hadj3 : (matrixSignedGraph B hB.isSymm).graph.Adj x v := ⟨hvx.symm, by rw [hsym_B, hB_vx]; norm_num⟩
          have hadj4 : (matrixSignedGraph B hB.isSymm).graph.Adj v y := ⟨hvy, by rw [hB_vy]; norm_num⟩
          let tailW := SimpleGraph.Walk.cons hadj2
            (SimpleGraph.Walk.cons hadj3 (SimpleGraph.Walk.cons hadj4 SimpleGraph.Walk.nil))
          let cyc := SimpleGraph.Walk.cons hadj1 (P.append tailW)
          have hcyc : cyc.IsCycle := by
            refine ⟨⟨⟨?_⟩, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by simp [cyc])⟩, ?_⟩
            · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append, List.nodup_cons]
              refine ⟨?_, ?_⟩
              · intro hm
                rcases List.mem_append.mp hm with hmP | hmt
                · exact hy_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
                · simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                    List.mem_cons, List.not_mem_nil, or_false] at hmt
                  rcases hmt with h | h | h
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                    · exact w₂.2.2.2 h1'.symm
                    · exact hxy h1'.symm
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                    · exact hxy h1'.symm
                    · exact hvy h1'.symm
                  · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                    · exact hvy h1'.symm
                    · exact w₁.2.1 h2'
              · rw [List.nodup_append]
                refine ⟨hP_path.isTrail.edges_nodup, ?_, ?_⟩
                · simp [tailW, w₂.2.1, w₂.2.2.1, w₂.2.2.2, hxy, hvx, hvy, hxy.symm, hvx.symm, hvy.symm, Sym2.eq_swap]
                · intro e' he' e₂ he₂ hEq
                  subst hEq
                  simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                    List.mem_cons, List.not_mem_nil, or_false] at he₂
                  rcases he₂ with rfl | rfl | rfl
                  · exact hx_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
                  · exact hv_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
                  · exact hy_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
            · rw [SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_append]
              simp only [tailW, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
              rw [List.nodup_append]
              refine ⟨hP_path.support_nodup, by simp [hvx.symm, hxy, hvy], ?_⟩
              intro a ha' b hb' hEq
              subst hEq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
              rcases hb' with rfl | rfl | rfl
              · exact hx_notP ha'
              · exact hv_notP ha'
              · exact hy_notP ha'
          have hcyc_len : cyc.length = c₀.length + 2 := by simp [cyc, tailW, hclen]
          have hcyc_odd : Odd cyc.length := by rcases hodd₀ with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
          have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
              - walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
            rw [hcsign]
            simp only [cyc, tailW, walkSignProd, SimpleGraph.Walk.edges_cons,
              SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_nil,
              List.map_cons, List.map_append, List.map_nil,
              List.prod_cons, List.prod_append, List.prod_nil, mul_one]
            have hs1 : (matrixSignedGraph B hB.isSymm).sign s(y, w₁.1) =
                -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
              simpa [matrixSignedGraph, A'₀, top] using hy1_s
            have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, x) =
                (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
              rw [Sym2.eq_swap]
              simpa [matrixSignedGraph, A'₀, top] using hx2_s
            have hs3 : (matrixSignedGraph B hB.isSymm).sign s(x, v) = 1 := by
              simp [matrixSignedGraph, hsym_B x v, hB_vx]
            have hs4 : (matrixSignedGraph B hB.isSymm).sign s(v, y) = 1 := by
              simp [matrixSignedGraph, hB_vy]
            rw [hs1, hs2, hs3, hs4]; ring
          have hnoc_cyc := hB_noc y cyc hcyc hcyc_odd
          rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
          have hdiv : (c₀.length + 2) / 2 = c₀.length / 2 + 1 := by omega
          rw [hdiv, pow_succ] at hnoc_cyc
          rw [← hc₀_eq, signedCycleType]
          linarith
        · have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
          have hadj1 : (matrixSignedGraph B hB.isSymm).graph.Adj y w₁.1 := ⟨w₁.2.2.2.symm, hy1_ne⟩
          have hadj2 : (matrixSignedGraph B hB.isSymm).graph.Adj w₂.1 y := ⟨w₂.2.2.2, by rwa [hsym_B]⟩
          let cyc := SimpleGraph.Walk.cons hadj1 (P.append (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil))
          have hcyc : cyc.IsCycle := h_edge_cycle y hy_notP hadj1 hadj2
          have hcyc_len : cyc.length = c₀.length := by simp [cyc, hclen]
          have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
              walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
            rw [hcsign]
            simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
              SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
              List.prod_cons, List.prod_append, List.prod_nil, mul_one]
            have hs1 : (matrixSignedGraph B hB.isSymm).sign s(y, w₁.1) =
                -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
              simpa [matrixSignedGraph, A'₀, top] using hy1_s
            have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, y) =
                -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
              rw [Sym2.eq_swap]
              simpa [matrixSignedGraph, A'₀, top] using hy2_s
            rw [hs1, hs2]; ring
          have hnoc_cyc := hB_noc y cyc hcyc (hcyc_len.symm ▸ hodd₀)
          rw [← hc₀_eq, signedCycleType, ← hcyc_len, ← hcyc_sign]
          exact hnoc_cyc
    · change Sum.inl () ∉ c.support at htop
      cases z₀ with
      | inl u =>
        cases u
        exact absurd (SimpleGraph.Walk.start_mem_support c) htop
      | inr w₀ =>
        obtain ⟨q, hqlen, hqsign, hqsupp, hqedges⟩ := hlift c htop
        have hqcyc : q.IsCycle := by
          refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
          · rw [hqedges]
            refine List.Nodup.map_on ?_ hc.edges_nodup
            intro e₁ he₁ e₂ he₂ hEq
            rcases e₁ with ⟨u₁, v₁⟩
            rcases e₂ with ⟨u₂, v₂⟩
            have hu₁ : u₁ ≠ Sum.inl () := fun h => htop (h ▸ SimpleGraph.Walk.fst_mem_support_of_mem_edges c he₁)
            have hv₁ : v₁ ≠ Sum.inl () := fun h => htop (h ▸ SimpleGraph.Walk.snd_mem_support_of_mem_edges c he₁)
            have hu₂ : u₂ ≠ Sum.inl () := fun h => htop (h ▸ SimpleGraph.Walk.fst_mem_support_of_mem_edges c he₂)
            have hv₂ : v₂ ≠ Sum.inl () := fun h => htop (h ▸ SimpleGraph.Walk.snd_mem_support_of_mem_edges c he₂)
            have hEq' : s(projU u₁, projU v₁) = s(projU u₂, projU v₂) := hEq
            rcases Sym2.eq_iff.mp hEq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [hprojU_inj u₁ u₂ hu₁ hu₂ h1, hprojU_inj v₁ v₂ hv₁ hv₂ h2]
            · rw [hprojU_inj u₁ v₂ hu₁ hv₂ h1, hprojU_inj v₁ u₂ hv₁ hu₂ h2]
              exact Sym2.eq_swap
          · intro hqnil
            have hlen0 : c.length = 0 := by rw [← hqlen, hqnil]; rfl
            cases c with
            | nil => exact hc.ne_nil rfl
            | cons _ _ => simp at hlen0
          · rw [hqsupp, ← List.map_tail]
            refine List.Nodup.map_on ?_ hc.support_nodup
            intro w₁ hw₁ w₂ hw₂ hEq
            exact hprojU_inj w₁ w₂
              (fun h => htop (h ▸ List.mem_of_mem_tail hw₁))
              (fun h => htop (h ▸ List.mem_of_mem_tail hw₂)) hEq
        have hnoc_q := hB_noc w₀.1 q hqcyc (hqlen.symm ▸ hodd)
        rw [signedCycleType, ← hqlen, ← hqsign]
        exact hnoc_q
  have hA'₀_le := ih (Unit ⊕ U) hcard_U A'₀ hA'₀ hA'₀_diag hA'₀_noc
  omega

end SignedGraphs
