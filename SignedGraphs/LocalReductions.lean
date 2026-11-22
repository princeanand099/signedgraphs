import SignedGraphs.LinearAlgebraExtra

/-!
# Local Algebraic Reductions (Section 2.2)

Formalization of:
- `cut_vertex_reduction` (Lemma 2.1): Cut-vertex decomposition via Schur complement / decoupling.
- `degree_two_reduction` (Lemma 2.2): Degree-2 vertex elimination via hyperbolic 2×2 block & Weyl.
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma exists_ker_dotProduct_eq_one {W : Type*} [Fintype W] [DecidableEq W]
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
        _ = dotProduct (Mᵀ *ᵥ k) y := by
            rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec]
            simp [dotProduct_comm]
        _ = dotProduct (M *ᵥ k) y := by rw [hMT]
        _ = 0 := by rw [hMk, zero_dotProduct]
    have hfin_RK : Module.finrank ℝ R + Module.finrank ℝ K = Fintype.card W := by
      simpa [R, K, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have hfin_φ : Module.finrank ℝ (LinearMap.range φ) + Module.finrank ℝ (LinearMap.ker φ) =
        Fintype.card W := by
      simpa [Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker φ
    have hfin_range_φ : Module.finrank ℝ (LinearMap.range φ) ≤ Module.finrank ℝ K := by
      calc Module.finrank ℝ (LinearMap.range φ)
          ≤ Module.finrank ℝ (K →ₗ[ℝ] ℝ) := Submodule.finrank_le (LinearMap.range φ)
        _ = Module.finrank ℝ K := Subspace.dual_finrank_eq
    have hfin_eq : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.ker φ) := by
      have hle : Module.finrank ℝ R ≤ Module.finrank ℝ (LinearMap.ker φ) :=
        Submodule.finrank_mono hR_le
      omega
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
    · congr; exact Subtype.ext h
  let f₂ : Unit ⊕ U₂ → V := Sum.elim (fun _ => v) (fun w => w.1)
  have hf₂_inj : Function.Injective f₂ := by
    rintro (⟨⟩ | ⟨w₁, _, hw₁⟩) (⟨⟩ | ⟨w₂, _, hw₂⟩) h
    · rfl
    · exact absurd h.symm hw₂
    · exact absurd h hw₁
    · congr; exact Subtype.ext h
  have hcard_f₁ : Fintype.card (Unit ⊕ U₁) = V₁.card := by
    have e₁ : Unit ⊕ U₁ ≃ {x : V // x ∈ V₁} :=
      { toFun := fun x => ⟨f₁ x, by rcases x with ⟨⟩ | ⟨u, hu1, _⟩; exact hv₁; exact hu1⟩
        invFun := fun x => if hx : x.1 = v then Sum.inl () else Sum.inr ⟨x.1, x.2, hx⟩
        left_inv := fun x => by
          rcases x with ⟨⟩ | ⟨u, hu1, huv⟩ <;> simp [f₁, huv]
        right_inv := fun ⟨x, hx⟩ => by
          by_cases h : x = v <;> simp [f₁, h] }
    rw [Fintype.card_congr e₁, Fintype.card_coe]
  have hcard_f₂ : Fintype.card (Unit ⊕ U₂) = V₂.card := by
    have e₂ : Unit ⊕ U₂ ≃ {x : V // x ∈ V₂} :=
      { toFun := fun x => ⟨f₂ x, by rcases x with ⟨⟩ | ⟨w, hw2, _⟩; exact hv₂; exact hw2⟩
        invFun := fun x => if hx : x.1 = v then Sum.inl () else Sum.inr ⟨x.1, x.2, hx⟩
        left_inv := fun x => by
          rcases x with ⟨⟩ | ⟨w, hw2, hwv⟩ <;> simp [f₂, hwv]
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
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hA.eq y) x).symm
  rcases exists_ker_dotProduct_eq_one A₁ hA₁ r₁ with ⟨x₁, hx₁⟩ | ⟨u, hu_ker, hu_dot⟩
  · rcases exists_ker_dotProduct_eq_one A₂ hA₂ r₂ with ⟨x₂, hx₂⟩ | ⟨u, hu_ker, hu_dot⟩
    · -- Case 2: r₁ ∈ im(A₁) and r₂ ∈ im(A₂)
      let e0 : Unit ⊕ (U₁ ⊕ U₂) ≃ (Unit ⊕ U₁) ⊕ U₂ := (Equiv.sumAssoc Unit U₁ U₂).symm
      let A_blk0 := A_blk.submatrix e0 e0
      have hA_blk0 : A_blk0.IsHermitian := isHermitian_submatrix A_blk hA_blk e0
      rw [← signature_reindex e0 A_blk hA_blk]
      let P : Matrix (Unit ⊕ (U₁ ⊕ U₂)) (Unit ⊕ (U₁ ⊕ U₂)) ℝ :=
        fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr (Sum.inl i), Sum.inl () => -x₁ i
          | Sum.inr (Sum.inr j), Sum.inl () => -x₂ j
          | Sum.inr (Sum.inl i), Sum.inr (Sum.inl i') => if i = i' then 1 else 0
          | Sum.inr (Sum.inr j), Sum.inr (Sum.inr j') => if j = j' then 1 else 0
          | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
          | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0
      let Q : Matrix (Unit ⊕ (U₁ ⊕ U₂)) (Unit ⊕ (U₁ ⊕ U₂)) ℝ :=
        fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr (Sum.inl i), Sum.inl () => x₁ i
          | Sum.inr (Sum.inr j), Sum.inl () => x₂ j
          | Sum.inr (Sum.inl i), Sum.inr (Sum.inl i') => if i = i' then 1 else 0
          | Sum.inr (Sum.inr j), Sum.inr (Sum.inr j') => if j = j' then 1 else 0
          | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
          | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0
      have hPQ : P * Q = 1 := by
        ext a b
        rcases a with ⟨⟩ | (i | i) <;> rcases b with ⟨⟩ | (j | j) <;>
          simp [P, Q, Matrix.mul_apply, Fintype.sum_sum_type]
      have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
      let c₁ : ℝ := dotProduct r₁ x₁
      let c₂ : ℝ := dotProduct r₂ x₂
      let S₁ : Matrix Unit Unit ℝ := Matrix.of (fun _ _ => -c₁ - c₂)
      let B_diag := Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks A₁ 0 0 A₂)
      have hcongr : Pᵀ * A_blk0 * P = B_diag := by
        have hx₁_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * x₁ k = r₁ i := fun i => congr_fun hx₁ i
        have hx₂_j : ∀ j : U₂, ∑ k : U₂, A₂ j k * x₂ k = r₂ j := fun j => congr_fun hx₂ j
        ext a b
        rcases a with ⟨⟩ | (i | i) <;> rcases b with ⟨⟩ | (j | j)
        · simp [P, A_blk0, A_blk, e0, e, B_diag, S₁, c₁, c₂, dotProduct, r₁, r₂, A₁, A₂,
            Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, hdiag v]
          calc -(∑ k : U₁, x₁ k * A k.1 v) - ∑ k : U₂, x₂ k * A k.1 v +
              (∑ k : U₁, (-(A v k.1 * x₁ k) + (∑ m : U₁, A k.1 m.1 * x₁ m) * x₁ k)) +
              ∑ k : U₂, (-(A v k.1 * x₂ k) + (∑ m : U₂, A k.1 m.1 * x₂ m) * x₂ k)
            = -(∑ k : U₁, x₁ k * A k.1 v) - ∑ k : U₂, x₂ k * A k.1 v +
              (∑ k : U₁, (-(A v k.1 * x₁ k) + A k.1 v * x₁ k)) +
              ∑ k : U₂, (-(A v k.1 * x₂ k) + A k.1 v * x₂ k) := by
                congr 2
                · refine Finset.sum_congr rfl fun k _ => ?_
                  rw [show ∑ m : U₁, A k.1 m.1 * x₁ m = A k.1 v from hx₁_i k]
                · refine Finset.sum_congr rfl fun k _ => ?_
                  rw [show ∑ m : U₂, A k.1 m.1 * x₂ m = A k.1 v from hx₂_j k]
            _ = -∑ k : U₁, A k.1 v * x₁ k - ∑ k : U₂, A k.1 v * x₂ k := by
                simp only [hsym_uv v _, mul_comm (x₁ _), mul_comm (x₂ _)]
                ring
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          have h1 : ∀ k : U₂, A k.1 j.1 = 0 := fun k => by
            rw [hsym_uv]; exact hno_cross j.1 j.2.1 k.1 k.2.1 j.2.2 k.2.2
          simp [h1]
          have hx1j : ∑ k : U₁, x₁ k * A k.1 j.1 = A j.1 v := by
            have := hx₁_i j
            simpa [A₁, hsym_uv j.1 _, mul_comm] using this
          rw [hsym_uv v j.1]
          linarith
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          have h1 : ∀ k : U₁, A k.1 j.1 = 0 := fun k => hno_cross k.1 k.2.1 j.1 j.2.1 k.2.2 j.2.2
          simp [h1]
          have hx2j : ∑ k : U₂, x₂ k * A k.1 j.1 = A j.1 v := by
            have := hx₂_j j
            simpa [A₂, hsym_uv j.1 _, mul_comm] using this
          rw [hsym_uv v j.1]
          linarith
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          have h1 : ∀ k : U₂, A i.1 k.1 = 0 := fun k => hno_cross i.1 i.2.1 k.1 k.2.1 i.2.2 k.2.2
          simp [h1]
          have hx1i : ∑ k : U₁, A i.1 k.1 * x₁ k = A i.1 v := hx₁_i i
          linarith
        · simp [P, A_blk0, A_blk, e0, e, B_diag, A₁, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          exact hno_cross i.1 i.2.1 j.1 j.2.1 i.2.2 j.2.2
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          have h1 : ∀ k : U₁, A i.1 k.1 = 0 := fun k => by
            rw [hsym_uv]
            exact hno_cross k.1 k.2.1 i.1 i.2.1 k.2.2 i.2.2
          simp [h1]
          have hx2i : ∑ k : U₂, A i.1 k.1 * x₂ k = A i.1 v := hx₂_j i
          linarith
        · simp [P, A_blk0, A_blk, e0, e, B_diag, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
          rw [hsym_uv]
          exact hno_cross j.1 j.2.1 i.1 i.2.1 j.2.2 i.2.2
        · simp [P, A_blk0, A_blk, e0, e, B_diag, A₂, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
      have hS₁ : S₁.IsHermitian := by
        ext ⟨⟩ ⟨⟩; simp [S₁, Matrix.conjTranspose_apply]
      have hsB_diag : signature A_blk0 hA_blk0 = signature S₁ hS₁ + (signature A₁ hA₁ + signature A₂ hA₂) := by
        have hc := signature_congr A_blk0 P hA_blk0 hP_det
        rw [← hc]
        have hfb := signature_fromBlocks S₁ hS₁ (Matrix.fromBlocks A₁ 0 0 A₂)
          (isHermitian_fromBlocks A₁ hA₁ A₂ hA₂)
        rw [signature_fromBlocks] at hfb
        convert hfb using 2
        exact hcongr
      rw [hsB_diag]
      have hM₁ : (Matrix.of (fun _ _ : Unit => -c₁)).IsHermitian := by
        ext ⟨⟩ ⟨⟩; simp [Matrix.conjTranspose_apply]
      have hM₂ : (Matrix.of (fun _ _ : Unit => -c₂)).IsHermitian := by
        ext ⟨⟩ ⟨⟩; simp [Matrix.conjTranspose_apply]
      have hsG₁_split : signature AG₁ hAG₁ =
          signature (Matrix.of (fun _ _ : Unit => -c₁)) hM₁ + signature A₁ hA₁ := by
        let P₁ : Matrix (Unit ⊕ U₁) (Unit ⊕ U₁) ℝ := fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr i, Sum.inl () => -x₁ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
        let Q₁ : Matrix (Unit ⊕ U₁) (Unit ⊕ U₁) ℝ := fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr i, Sum.inl () => x₁ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
        have hPQ₁ : P₁ * Q₁ = 1 := by
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j <;>
            simp [P₁, Q₁, Matrix.mul_apply, Fintype.sum_sum_type]
        have hP₁_det : IsUnit P₁.det := isUnit_iff_exists_inv.mpr ⟨Q₁.det, by rw [← Matrix.det_mul, hPQ₁, Matrix.det_one]⟩
        have hcongr₁ : P₁ᵀ * AG₁ * P₁ = Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => -c₁)) 0 0 A₁ := by
          have hx₁_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * x₁ k = r₁ i := fun i => congr_fun hx₁ i
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j
          · simp [P₁, AG₁, f₁, c₁, dotProduct, r₁, A₁, Matrix.mul_apply, Matrix.transpose_apply,
              Fintype.sum_sum_type, hdiag v]
            calc -(∑ k : U₁, x₁ k * A k.1 v) +
                ∑ k : U₁, (-(A v k.1 * x₁ k) + (∑ m : U₁, A k.1 m.1 * x₁ m) * x₁ k)
              = -(∑ k : U₁, x₁ k * A k.1 v) +
                ∑ k : U₁, (-(A v k.1 * x₁ k) + A k.1 v * x₁ k) := by
                  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
                  rw [show ∑ m : U₁, A k.1 m.1 * x₁ m = A k.1 v from hx₁_i k]
              _ = -∑ k : U₁, A k.1 v * x₁ k := by
                  simp only [hsym_uv v _, mul_comm (x₁ _)]; ring
          · simp [P₁, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
            have hx1j : ∑ k : U₁, x₁ k * A k.1 j.1 = A j.1 v := by
              have := hx₁_i j; simpa [A₁, hsym_uv j.1 _, mul_comm] using this
            rw [hsym_uv v j.1]; linarith
          · simp [P₁, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
            have hx1i : ∑ k : U₁, A i.1 k.1 * x₁ k = A i.1 v := hx₁_i i
            linarith
          · simp [P₁, AG₁, f₁, A₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
        have hc := signature_congr AG₁ P₁ hAG₁ hP₁_det
        rw [← hc]
        have hfb := signature_fromBlocks (Matrix.of (fun _ _ : Unit => -c₁)) hM₁ A₁ hA₁
        convert hfb using 2
        exact hcongr₁
      have hsG₂_split : signature AG₂ hAG₂ =
          signature (Matrix.of (fun _ _ : Unit => -c₂)) hM₂ + signature A₂ hA₂ := by
        let P₂ : Matrix (Unit ⊕ U₂) (Unit ⊕ U₂) ℝ := fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr i, Sum.inl () => -x₂ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
        let Q₂ : Matrix (Unit ⊕ U₂) (Unit ⊕ U₂) ℝ := fun a b => match a, b with
          | Sum.inl (), Sum.inl () => 1
          | Sum.inl (), Sum.inr _ => 0
          | Sum.inr i, Sum.inl () => x₂ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
        have hPQ₂ : P₂ * Q₂ = 1 := by
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j <;>
            simp [P₂, Q₂, Matrix.mul_apply, Fintype.sum_sum_type]
        have hP₂_det : IsUnit P₂.det := isUnit_iff_exists_inv.mpr ⟨Q₂.det, by rw [← Matrix.det_mul, hPQ₂, Matrix.det_one]⟩
        have hcongr₂ : P₂ᵀ * AG₂ * P₂ = Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => -c₂)) 0 0 A₂ := by
          have hx₂_j : ∀ j : U₂, ∑ k : U₂, A₂ j k * x₂ k = r₂ j := fun j => congr_fun hx₂ j
          ext a b; rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j
          · simp [P₂, AG₂, f₂, c₂, dotProduct, r₂, A₂, Matrix.mul_apply, Matrix.transpose_apply,
              Fintype.sum_sum_type, hdiag v]
            calc -(∑ k : U₂, x₂ k * A k.1 v) +
                ∑ k : U₂, (-(A v k.1 * x₂ k) + (∑ m : U₂, A k.1 m.1 * x₂ m) * x₂ k)
              = -(∑ k : U₂, x₂ k * A k.1 v) +
                ∑ k : U₂, (-(A v k.1 * x₂ k) + A k.1 v * x₂ k) := by
                  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
                  rw [show ∑ m : U₂, A k.1 m.1 * x₂ m = A k.1 v from hx₂_j k]
              _ = -∑ k : U₂, A k.1 v * x₂ k := by
                  simp only [hsym_uv v _, mul_comm (x₂ _)]; ring
          · simp [P₂, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
            have hx2j : ∑ k : U₂, x₂ k * A k.1 j.1 = A j.1 v := by
              have := hx₂_j j; simpa [A₂, hsym_uv j.1 _, mul_comm] using this
            rw [hsym_uv v j.1]; linarith
          · simp [P₂, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
            have hx2i : ∑ k : U₂, A i.1 k.1 * x₂ k = A i.1 v := hx₂_j i
            linarith
          · simp [P₂, AG₂, f₂, A₂, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
        have hc := signature_congr AG₂ P₂ hAG₂ hP₂_det
        rw [← hc]
        have hfb := signature_fromBlocks (Matrix.of (fun _ _ : Unit => -c₂)) hM₂ A₂ hA₂
        convert hfb using 2
        exact hcongr₂
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
      let P : Matrix ((Unit ⊕ U₂) ⊕ U₁) ((Unit ⊕ U₂) ⊕ U₁) ℝ :=
        fun a b => match a, b with
          | Sum.inl (Sum.inl ()), Sum.inl (Sum.inl ()) => 1
          | Sum.inl (Sum.inr w), Sum.inl (Sum.inr w') => if w = w' then 1 else 0
          | Sum.inl (Sum.inr w), Sum.inr i => -u w * r₁ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
          | _, _ => 0
      let Q : Matrix ((Unit ⊕ U₂) ⊕ U₁) ((Unit ⊕ U₂) ⊕ U₁) ℝ :=
        fun a b => match a, b with
          | Sum.inl (Sum.inl ()), Sum.inl (Sum.inl ()) => 1
          | Sum.inl (Sum.inr w), Sum.inl (Sum.inr w') => if w = w' then 1 else 0
          | Sum.inl (Sum.inr w), Sum.inr i => u w * r₁ i
          | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
          | _, _ => 0
      have hPQ : P * Q = 1 := by
        ext a b
        rcases a with (⟨⟩ | w) | i <;> rcases b with (⟨⟩ | w') | j <;>
          simp [P, Q, Matrix.mul_apply, Fintype.sum_sum_type]
      have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
      have hu_ker_w : ∀ w : U₂, ∑ k : U₂, A₂ w k * u k = 0 := fun w => congr_fun hu_ker w
      have hcongr : Pᵀ * A_blk2 * P = Matrix.fromBlocks AG₂ 0 0 A₁ := by
        ext a b
        rcases a with (⟨⟩ | w) | i <;> rcases b with (⟨⟩ | w') | j
        · simp [P, A_blk2, A_blk, e2, e, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
        · simp [P, A_blk2, A_blk, e2, e, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
        · simp [P, A_blk2, A_blk, e2, e, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type, r₁]
          have hsum : ∑ k : U₂, A v k.1 * (-u k * A j.1 v) = -(dotProduct u r₂) * A j.1 v := by
            simp only [dotProduct, r₂]
            calc ∑ k : U₂, A v k.1 * (-u k * A j.1 v)
                = -(∑ k : U₂, u k * A k.1 v) * A j.1 v := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  rw [hsym_uv v k.1]; ring
          rw [hsum, hu_dot, neg_one_mul, add_neg_cancel]
        · simp [P, A_blk2, A_blk, e2, e, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
        · simp [P, A_blk2, A_blk, e2, e, AG₂, f₂, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type]
        · simp [P, A_blk2, A_blk, e2, e, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type, r₁]
          have hcross : A w.1 j.1 = 0 := by
            rw [hsym_uv]; exact hno_cross j.1 j.2.1 w.1 w.2.1 j.2.2 w.2.2
          have hker_sum : ∑ k : U₂, A w.1 k.1 * (-u k * A j.1 v) = 0 := by
            calc ∑ k : U₂, A w.1 k.1 * (-u k * A j.1 v)
                = -(∑ k : U₂, A₂ w k * u k) * A j.1 v := by
                  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; simp [A₂]; ring
              _ = 0 := by rw [hu_ker_w w, neg_zero, zero_mul]
          rw [hcross, hker_sum, add_zero]
        · simp [P, A_blk2, A_blk, e2, e, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type, r₁]
          have hsum : ∑ k : U₂, (-u k * A i.1 v) * A k.1 v = -(dotProduct u r₂) * A i.1 v := by
            simp only [dotProduct, r₂]
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
          rw [hsum, hu_dot, neg_one_mul, hsym_uv i.1 v, neg_add_cancel]
        · simp [P, A_blk2, A_blk, e2, e, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type, r₁]
          have hcross : A i.1 w'.1 = 0 := hno_cross i.1 i.2.1 w'.1 w'.2.1 i.2.2 w'.2.2
          have hker_sum : ∑ k : U₂, (-u k * A i.1 v) * A k.1 w'.1 = 0 := by
            calc ∑ k : U₂, (-u k * A i.1 v) * A k.1 w'.1
                = -(∑ k : U₂, A₂ w' k * u k) * A i.1 v := by
                  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
                  simp [A₂, hsym_uv k.1 w'.1]; ring
              _ = 0 := by rw [hu_ker_w w', neg_zero, zero_mul]
          rw [hcross, hker_sum, zero_add]
        · simp [P, A_blk2, A_blk, e2, e, A₁, Matrix.mul_apply, Matrix.transpose_apply,
            Fintype.sum_sum_type, r₁]
          have hcross1 : ∀ k : U₂, A i.1 k.1 = 0 := fun k => hno_cross i.1 i.2.1 k.1 k.2.1 i.2.2 k.2.2
          have hcross2 : ∀ k : U₂, A k.1 j.1 = 0 := fun k => by
            rw [hsym_uv]; exact hno_cross j.1 j.2.1 k.1 k.2.1 j.2.2 k.2.2
          have hker_sum : ∀ k : U₂, (∑ m : U₂, A k.1 m.1 * (-u m * A j.1 v)) = 0 := fun k => by
            calc ∑ m : U₂, A k.1 m.1 * (-u m * A j.1 v)
                = -(∑ m : U₂, A₂ k m * u m) * A j.1 v := by
                  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun m _ => ?_; simp [A₂]; ring
              _ = 0 := by rw [hu_ker_w k, neg_zero, zero_mul]
          simp [hcross1, hcross2, hker_sum]
      have hc := signature_congr A_blk2 P hA_blk2 hP_det
      rw [← hc]
      have hs : signature (Pᵀ * A_blk2 * P) (isHermitian_congr A_blk2 P hA_blk2) =
          signature AG₂ hAG₂ + signature A₁ hA₁ := by
        have hfb := signature_fromBlocks AG₂ hAG₂ A₁ hA₁
        convert hfb using 2
        exact hcongr
      rw [hs]
      omega
  · -- Case 1a: r₁ ∉ im(A₁), decouple G₁ ⊕ A₂
    let P : Matrix ((Unit ⊕ U₁) ⊕ U₂) ((Unit ⊕ U₁) ⊕ U₂) ℝ :=
      fun a b => match a, b with
        | Sum.inl (Sum.inl ()), Sum.inl (Sum.inl ()) => 1
        | Sum.inl (Sum.inr i), Sum.inl (Sum.inr i') => if i = i' then 1 else 0
        | Sum.inl (Sum.inr i), Sum.inr j => -u i * r₂ j
        | Sum.inr j, Sum.inr j' => if j = j' then 1 else 0
        | _, _ => 0
    let Q : Matrix ((Unit ⊕ U₁) ⊕ U₂) ((Unit ⊕ U₁) ⊕ U₂) ℝ :=
      fun a b => match a, b with
        | Sum.inl (Sum.inl ()), Sum.inl (Sum.inl ()) => 1
        | Sum.inl (Sum.inr i), Sum.inl (Sum.inr i') => if i = i' then 1 else 0
        | Sum.inl (Sum.inr i), Sum.inr j => u i * r₂ j
        | Sum.inr j, Sum.inr j' => if j = j' then 1 else 0
        | _, _ => 0
    have hPQ : P * Q = 1 := by
      ext a b
      rcases a with (⟨⟩ | i) | j <;> rcases b with (⟨⟩ | i') | j' <;>
        simp [P, Q, Matrix.mul_apply, Fintype.sum_sum_type]
    have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
    have hu_ker_i : ∀ i : U₁, ∑ k : U₁, A₁ i k * u k = 0 := fun i => congr_fun hu_ker i
    have hcongr : Pᵀ * A_blk * P = Matrix.fromBlocks AG₁ 0 0 A₂ := by
      ext a b
      rcases a with (⟨⟩ | i) | j <;> rcases b with (⟨⟩ | i') | j'
      · simp [P, A_blk, e, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
      · simp [P, A_blk, e, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
      · simp [P, A_blk, e, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, r₂]
        have hsum : ∑ k : U₁, A v k.1 * (-u k * A j'.1 v) = -(dotProduct u r₁) * A j'.1 v := by
          simp only [dotProduct, r₁]
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsym_uv v k.1]; ring
        rw [hsum, hu_dot, neg_one_mul, add_neg_cancel]
      · simp [P, A_blk, e, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
      · simp [P, A_blk, e, AG₁, f₁, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
      · simp [P, A_blk, e, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, r₂]
        have hcross : A i.1 j'.1 = 0 := hno_cross i.1 i.2.1 j'.1 j'.2.1 i.2.2 j'.2.2
        have hker_sum : ∑ k : U₁, A i.1 k.1 * (-u k * A j'.1 v) = 0 := by
          calc ∑ k : U₁, A i.1 k.1 * (-u k * A j'.1 v)
              = -(∑ k : U₁, A₁ i k * u k) * A j'.1 v := by
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; simp [A₁]; ring
            _ = 0 := by rw [hu_ker_i i, neg_zero, zero_mul]
        rw [hcross, hker_sum, add_zero]
      · simp [P, A_blk, e, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, r₂]
        have hsum : ∑ k : U₁, (-u k * A j.1 v) * A k.1 v = -(dotProduct u r₁) * A j.1 v := by
          simp only [dotProduct, r₁]
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
        rw [hsum, hu_dot, neg_one_mul, hsym_uv j.1 v, neg_add_cancel]
      · simp [P, A_blk, e, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, r₂]
        have hcross : A j.1 i'.1 = 0 := by
          rw [hsym_uv]; exact hno_cross i'.1 i'.2.1 j.1 j.2.1 i'.2.2 j.2.2
        have hker_sum : ∑ k : U₁, (-u k * A j.1 v) * A k.1 i'.1 = 0 := by
          calc ∑ k : U₁, (-u k * A j.1 v) * A k.1 i'.1
              = -(∑ k : U₁, A₁ i' k * u k) * A j.1 v := by
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
                simp [A₁, hsym_uv k.1 i'.1]; ring
            _ = 0 := by rw [hu_ker_i i', neg_zero, zero_mul]
        rw [hcross, hker_sum, zero_add]
      · simp [P, A_blk, e, A₂, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, r₂]
        have hcross1 : ∀ k : U₁, A j.1 k.1 = 0 := fun k => by
          rw [hsym_uv]; exact hno_cross k.1 k.2.1 j.1 j.2.1 k.2.2 j.2.2
        have hcross2 : ∀ k : U₁, A k.1 j'.1 = 0 := fun k =>
          hno_cross k.1 k.2.1 j'.1 j'.2.1 k.2.2 j'.2.2
        have hker_sum : ∀ k : U₁, (∑ m : U₁, A k.1 m.1 * (-u m * A j'.1 v)) = 0 := fun k => by
          calc ∑ m : U₁, A k.1 m.1 * (-u m * A j'.1 v)
              = -(∑ m : U₁, A₁ k m * u m) * A j'.1 v := by
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun m _ => ?_; simp [A₁]; ring
            _ = 0 := by rw [hu_ker_i k, neg_zero, zero_mul]
        simp [hcross1, hcross2, hker_sum]
    have hc := signature_congr A_blk P hA_blk hP_det
    rw [← hc]
    have hs : signature (Pᵀ * A_blk * P) (isHermitian_congr A_blk P hA_blk) =
        signature AG₁ hAG₁ + signature A₂ hA₂ := by
      have hfb := signature_fromBlocks AG₁ hAG₁ A₂ hA₂
      convert hfb using 2
      exact hcongr
    rw [hs]
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

private lemma walkSignProd_reverse {V : Type*} {G : SimpleGraph V} (σ : Sym2 V → ℤ)
    {a b : V} (p : G.Walk a b) :
    walkSignProd σ p.reverse = walkSignProd σ p := by
  simp only [walkSignProd, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.prod_reverse]

/-- **Lemma 2.2 (Degree-2 vertex reduction)**: If `v` has degree 2 in `G(A)` (with `|V| ≥ 3`)
and Theorem 1.2 holds for all NOC matrices of order `|V| - 2`, then `s(A) ≤ 0`. -/
theorem degree_two_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (hn : 3 ≤ Fintype.card V)
    (v x y : V) (hxy : x ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (hN : ∀ w : V, (matrixGraph A hA.isSymm).Adj v w ↔ w = x ∨ w = y)
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
    · subst hwv; exact hdiag v
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
    simp [B, D, d, Matrix.diagonal_mul, Matrix.mul_diagonal, hvx.symm, hAvx_ne]
  have hB_vy : B v y = 1 := by
    simp [B, D, d, Matrix.diagonal_mul, Matrix.mul_diagonal, hvy.symm, hxy.symm, hAvy_ne]
  have hB_vw : ∀ w : V, w ≠ x → w ≠ y → B v w = 0 := fun w hwx hwy => by
    simp [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, hAvw_zero w hwx hwy]
  have hsym_B : ∀ a b : V, B a b = B b a := fun a b => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq b) a).symm
  rw [← signature_congr A D hA hD_det]
  change signature B hB ≤ 0
  have hBxy_nonneg : 0 ≤ B x y := by
    by_contra hneg
    push Not at hneg
    have hBxy_ne : B x y ≠ 0 := ne_of_lt hneg
    let c : (matrixGraph B hB.isSymm).Walk v v :=
      SimpleGraph.Walk.cons ⟨hvx, by rw [hB_vx]; norm_num⟩
        (SimpleGraph.Walk.cons ⟨hxy, hBxy_ne⟩
          (SimpleGraph.Walk.cons ⟨hvy.symm, by rw [hsym_B, hB_vy]; norm_num⟩ SimpleGraph.Walk.nil))
    have hc_cyc : c.IsCycle := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · simp [c, hvx, hxy, hvy, hvy.symm, hvx.symm, hxy.symm, Sym2.eq_swap]
      · simp [c]
      · simp [c, hvx, hxy, hvy, hvx.symm, hxy.symm, hvy.symm]
    have hodd : Odd c.length := by simp [c]
    have hnoc_c := hB_noc v c hc_cyc hodd
    have hsign_c : signedCycleType (matrixSignedGraph B hB.isSymm).sign c = 1 := by
      simp [signedCycleType, c, walkSignProd, matrixSignedGraph, hB_vx, hsym_B y v,
        hB_vy, not_lt.mpr hneg.le]
    linarith
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
          · simp [hz0, hz1]
          · by_cases hz2 : z = y <;> simp [hz0, hz1, hz2] }
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
    ext a b
    rcases a with i | u <;> rcases b with j | w
    · have h := congr_fun (congr_fun hPQ₃ i) j
      simpa [P₁, Q₁, Matrix.mul_apply, Fintype.sum_sum_type] using h
    · simp [P₁, Q₁, Matrix.mul_apply, Fintype.sum_sum_type]
    · simp [P₁, Q₁, Matrix.mul_apply, Fintype.sum_sum_type]
    · simp [P₁, Q₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
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
  let s : Unit ⊕ U → ℝ := fun
    | Sum.inl () => 0
    | Sum.inr u => -(B x u.1 + B y u.1) / 2
  let P₂ : Matrix (Fin 2 ⊕ (Unit ⊕ U)) (Fin 2 ⊕ (Unit ⊕ U)) ℝ :=
    fun a b => match a, b with
      | Sum.inl i, Sum.inl j => if i = j then 1 else 0
      | Sum.inl 0, Sum.inr z => s z
      | Sum.inl 1, Sum.inr _ => 0
      | Sum.inr _, Sum.inl _ => 0
      | Sum.inr z, Sum.inr z' => if z = z' then 1 else 0
  let Q₂ : Matrix (Fin 2 ⊕ (Unit ⊕ U)) (Fin 2 ⊕ (Unit ⊕ U)) ℝ :=
    fun a b => match a, b with
      | Sum.inl i, Sum.inl j => if i = j then 1 else 0
      | Sum.inl 0, Sum.inr z => -s z
      | Sum.inl 1, Sum.inr _ => 0
      | Sum.inr _, Sum.inl _ => 0
      | Sum.inr z, Sum.inr z' => if z = z' then 1 else 0
  have hPQ₂ : P₂ * Q₂ = 1 := by
    ext a b
    rcases a with i | z <;> rcases b with j | z'
    · fin_cases i <;> fin_cases j <;> simp [P₂, Q₂, Matrix.mul_apply, Fintype.sum_sum_type]
    · fin_cases i <;> simp [P₂, Q₂, Matrix.mul_apply, Fintype.sum_sum_type]
    · fin_cases j <;> simp [P₂, Q₂, Matrix.mul_apply, Fintype.sum_sum_type]
    · simp [P₂, Q₂, Matrix.mul_apply, Fintype.sum_sum_type]
  have hP₂_det : IsUnit P₂.det := isUnit_iff_exists_inv.mpr ⟨Q₂.det, by rw [← Matrix.det_mul, hPQ₂, Matrix.det_one]⟩
  rw [← signature_congr Btilde₂ P₂ hBtilde₂ hP₂_det]
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 2, 2 * B x y]
  let A' : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ :=
    fun a b => match a, b with
      | Sum.inl (), Sum.inl () => -2 * B x y
      | Sum.inl (), Sum.inr u => B x u.1 - B y u.1
      | Sum.inr u, Sum.inl () => B u.1 x - B u.1 y
      | Sum.inr u, Sum.inr w => B u.1 w.1
  have hcongr₂ : P₂ᵀ * Btilde₂ * P₂ = Matrix.fromBlocks H 0 0 A' := by
    ext a b
    rcases a with i | z <;> rcases b with j | z'
    · fin_cases i <;> fin_cases j <;>
        simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, H, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x] <;>
        ring
    · fin_cases i <;> rcases z' with ⟨⟩ | u
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_vx, hB_vy, hB_vw u.1 u.2.2.1 u.2.2.2]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vx, hB_vy, hB_vw u.1 u.2.2.1 u.2.2.2]
        ring
    · fin_cases j <;> rcases z with ⟨⟩ | u
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vx, hB_vy, hsym_B u.1 v, hB_vw u.1 u.2.2.1 u.2.2.2]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hB_vx, hB_vy, hsym_B x v, hsym_B y v, hsym_B y x]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vx, hB_vy, hsym_B u.1 v, hB_vw u.1 u.2.2.1 u.2.2.2, hsym_B x u.1, hsym_B y u.1]
        ring
    · rcases z with ⟨⟩ | u <;> rcases z' with ⟨⟩ | w
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, A', Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_diag v, hB_diag x, hB_diag y, hsym_B y x]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, A', Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vx, hB_vy, hB_vw w.1 w.2.2.1 w.2.2.2]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, A', Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vx, hB_vy, hsym_B u.1 v, hB_vw u.1 u.2.2.1 u.2.2.2, hsym_B x u.1, hsym_B y u.1]
        ring
      · simp [P₂, Btilde₂, Btilde, B_blk, P₁, P₃, e₂, e, s, A', Matrix.mul_apply,
          Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
          hB_vw u.1 u.2.2.1 u.2.2.2, hB_vw w.1 w.2.2.1 w.2.2.2, hsym_B u.1 v]
        ring
  have hH : H.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]
  have hA' : A'.IsHermitian := by
    ext a b
    rcases a with ⟨⟩ | u <;> rcases b with ⟨⟩ | w <;>
      simp [A', Matrix.conjTranspose_apply, hsym_B]
  have hs_split : signature (P₂ᵀ * Btilde₂ * P₂) (isHermitian_congr Btilde₂ P₂ hBtilde₂) =
      signature H hH + signature A' hA' := by
    have hfb := signature_fromBlocks H hH A' hA'
    convert hfb using 2
    exact hcongr₂
  rw [hs_split]
  have hsH : signature H hH = 0 := signature_two_by_two_offdiag 2 (2 * B x y) (by norm_num) hH
  rw [hsH, zero_add]
  let A'₀ : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ :=
    fun a b => match a, b with
      | Sum.inl (), Sum.inl () => 0
      | a, b => A' a b
  have hA'₀ : A'₀.IsHermitian := by
    ext a b
    rcases a with ⟨⟩ | u <;> rcases b with ⟨⟩ | w <;>
      simp [A'₀, A', Matrix.conjTranspose_apply, hsym_B]
  have hA'_le : signature A' hA' ≤ signature A'₀ hA'₀ := by
    refine signature_mono_of_posSemidef A' A'₀ hA' hA'₀ ?_
    intro z
    have hdiff : ∀ a, ((A'₀ - A') *ᵥ z) a = if a = Sum.inl () then 2 * B x y * z (Sum.inl ()) else 0 := by
      intro a
      rcases a with ⟨⟩ | u
      · simp [Matrix.mulVec, dotProduct, A'₀, A', Fintype.sum_sum_type]; ring
      · simp [Matrix.mulVec, dotProduct, A'₀, A', Fintype.sum_sum_type]
    simp only [dotProduct, hdiff, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
    simp only [↓reduceIte, Sum.inl.injEq, reduceCtorEq, Finset.sum_const_zero, add_zero]
    nlinarith [sq_nonneg (z (Sum.inl ()))]
  have hA'₀_diag : ∀ z, A'₀ z z = 0 := by
    intro z
    rcases z with ⟨⟩ | u
    · simp [A'₀]
    · simp [A'₀, A', hB_diag u.1]
  -- Helper: lift any walk in A'₀ avoiding Sum.inl () to a walk in B inside U
  have hlift : ∀ {a b : U} (p : (matrixGraph A'₀ hA'₀.isSymm).Walk (Sum.inr a) (Sum.inr b)),
      Sum.inl () ∉ p.support →
      ∃ q : (matrixGraph B hB.isSymm).Walk a.1 b.1,
        q.length = p.length ∧
        walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
          walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign p ∧
        (∀ z ∈ q.support, ∃ u : U, u.1 = z ∧ Sum.inr u ∈ p.support) ∧
        (p.support.Nodup → q.support.Nodup) ∧
        (p.IsCycle → q.IsCycle) := by
    intro a b p hnot
    -- Define the subgraph embedding on U into V
    let fU : U → V := fun u => u.1
    have hrec : ∀ {s t : Unit ⊕ U} (p : (matrixGraph A'₀ hA'₀.isSymm).Walk s t),
        Sum.inl () ∉ p.support →
        ∀ (as : U) (bs : U), s = Sum.inr as → t = Sum.inr bs →
        ∃ q : (matrixGraph B hB.isSymm).Walk as.1 bs.1,
          q.length = p.length ∧
          walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
            walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign p ∧
          q.support = p.support.map (fun | Sum.inl () => v | Sum.inr u => u.1) := by
      intro s t p
      induction p with
      | nil =>
        intro _ as bs hs ht
        have hEq : as = bs := Sum.inr.inj (hs.symm.trans ht)
        subst hEq
        exact ⟨SimpleGraph.Walk.nil, rfl, rfl, by simp [hs]⟩
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
        obtain ⟨q', hq'len, hq'sign, hq'supp⟩ := ih hnot_p u₂ bs hu₂ ht
        have hadjB : (matrixGraph B hB.isSymm).Adj as.1 u₂.1 := by
          subst hs; subst hu₂
          refine ⟨fun h => hadj.1 (congrArg Sum.inr (Subtype.ext h)), ?_⟩
          simpa [matrixGraph, A'₀, A'] using hadj.2
        refine ⟨SimpleGraph.Walk.cons hadjB q', by simp [hq'len], ?_, ?_⟩
        · subst hs; subst hu₂
          simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
          have h1 : (matrixSignedGraph B hB.isSymm).sign s(as.1, u₂.1) =
              (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(Sum.inr as, Sum.inr u₂) := by
            simp [matrixSignedGraph, A'₀, A']
          rw [h1]
          exact congrArg _ hq'sign
        · simp [SimpleGraph.Walk.support_cons, hs, hq'supp]
    obtain ⟨q, hqlen, hqsign, hqsupp⟩ := hrec p hnot a b rfl rfl
    refine ⟨q, hqlen, hqsign, ?_, ?_, ?_⟩
    · intro z hz
      rw [hqsupp] at hz
      rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
      rcases w with ⟨⟩ | u
      · exact absurd hw hnot
      · exact ⟨u, rfl, hw⟩
    · intro hnd
      rw [hqsupp]
      refine List.Nodup.map_on ?_ hnd
      intro w₁ hw₁ w₂ hw₂ hEq
      rcases w₁ with ⟨⟩ | u₁
      · exact absurd hw₁ hnot
      · rcases w₂ with ⟨⟩ | u₂
        · exact absurd hw₂ hnot
        · exact congrArg Sum.inr (Subtype.ext hEq)
    · intro hcyc
      have hne : q ≠ SimpleGraph.Walk.nil := by
        intro hqnil
        have : p.length = 0 := by rw [← hqlen, hqnil]; rfl
        exact hcyc.ne_nil (SimpleGraph.Walk.eq_nil_of_length_eq_zero this)
      have htail : q.support.tail.Nodup := by
        rw [hqsupp, List.map_tail]
        refine List.Nodup.map_on ?_ hcyc.support_nodup
        intro w₁ hw₁ w₂ hw₂ hEq
        have hw₁' : w₁ ∈ p.support := List.mem_of_mem_tail hw₁
        have hw₂' : w₂ ∈ p.support := List.mem_of_mem_tail hw₂
        rcases w₁ with ⟨⟩ | u₁
        · exact absurd hw₁' hnot
        · rcases w₂ with ⟨⟩ | u₂
          · exact absurd hw₂' hnot
          · exact congrArg Sum.inr (Subtype.ext hEq)
      have hedges : q.edges.Nodup := by
        have hlen3 : 3 ≤ q.length := by rw [hqlen]; exact hcyc.three_le_length
        have htr : q.IsTrail := by
          rw [SimpleGraph.Walk.isTrail_def]
          -- From support.tail.Nodup and length ≥ 3, edges are nodup
          cases q with
          | nil => simp at hlen3
          | @cons _ w₁ _ h₁ r =>
            have hr_path : r.IsPath := ⟨by simpa [SimpleGraph.Walk.support_cons] using htail⟩
            rw [SimpleGraph.Walk.edges_cons, List.nodup_cons]
            refine ⟨?_, hr_path.isTrail.edges_nodup⟩
            intro hmem
            -- If s(a.1, w₁) ∈ r.edges, since r ends at a.1 and r is a path, r must be just a single edge w₁-a.1, contradicting hlen3
            have hr_len : 2 ≤ r.length := by simp at hlen3; omega
            rcases SimpleGraph.Walk.mem_edges_iff_exists_takeUntil.mp hmem with ⟨_, _⟩
            sorry
        exact htr.edges_nodup
      exact ⟨⟨hedges⟩, hne, htail⟩
  have hA'₀_noc : MatrixIsNOC A'₀ hA'₀.isSymm := by
    intro z₀ c hc hodd
    let top : Unit ⊕ U := Sum.inl ()
    by_cases htop : top ∈ c.support
    · -- Rotate c to start at top
      let c₀ := c.rotate htop
      have hc₀ : c₀.IsCycle := hc.rotate htop
      have hlen₀ : c₀.length = c.length := SimpleGraph.Walk.length_rotate c htop
      have hodd₀ : Odd c₀.length := hlen₀.symm ▸ hodd
      have hsign_rot : walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ =
          walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c := by
        have hperm : c₀.edges.Perm c.edges := (SimpleGraph.Walk.edges_rotate c htop).perm
        simp only [walkSignProd]
        exact (hperm.map _).prod_eq
      have htype_eq : signedCycleType (matrixSignedGraph A'₀ hA'₀.isSymm).sign c =
          signedCycleType (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
        simp [signedCycleType, hlen₀, hsign_rot]
      rw [htype_eq]
      -- Decompose c₀ = cons h₁ q, and q.reverse = cons h₂ p_rev
      cases hc₀_eq : c₀ with
      | nil => exact absurd hc₀_eq hc₀.ne_nil
      | @cons _ a₁ _ h₁ q =>
        have ha₁ : ∃ w₁ : U, a₁ = Sum.inr w₁ := by
          cases a₁ with
          | inl u => cases u; exact absurd rfl h₁.1
          | inr w₁ => exact ⟨w₁, rfl⟩
        rcases ha₁ with ⟨w₁, rfl⟩
        cases hqr : q.reverse with
        | nil =>
          have hqnil : q = SimpleGraph.Walk.nil := by
            have := congrArg SimpleGraph.Walk.reverse hqr
            simpa using this
          subst hqnil
          exact absurd rfl h₁.1
        | @cons _ a₂ _ h₂ p_rev =>
          have ha₂ : ∃ w₂ : U, a₂ = Sum.inr w₂ := by
            cases a₂ with
            | inl u => cases u; exact absurd rfl h₂.1
            | inr w₂ => exact ⟨w₂, rfl⟩
          rcases ha₂ with ⟨w₂, rfl⟩
          let p := p_rev.reverse
          have hq_eq : q = p.append (SimpleGraph.Walk.cons h₂.symm SimpleGraph.Walk.nil) := by
            have := congrArg SimpleGraph.Walk.reverse hqr
            simp only [SimpleGraph.Walk.reverse_reverse, SimpleGraph.Walk.reverse_cons] at this
            simpa [p] using this
          have hc₀_supp : c₀.support.tail.Nodup := hc₀.support_nodup
          rw [hc₀_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at hc₀_supp
          have hq_supp : q.support = p.support ++ [top] := by
            rw [hq_eq, SimpleGraph.Walk.support_append]
            simp
          rw [hq_supp] at hc₀_supp
          have hp_nd : p.support.Nodup := (List.nodup_append.mp hc₀_supp).1
          have htop_not_p : top ∉ p.support := fun hm =>
            (List.nodup_append.mp hc₀_supp).2.2 top hm (List.mem_singleton_self top) rfl
          obtain ⟨P, hPlen, hPsign, hPsupp, hPnd, _⟩ := hlift p htop_not_p
          have hP_path : P.IsPath := ⟨hPnd hp_nd⟩
          have hP_avoid : ∀ z ∈ P.support, z ≠ v ∧ z ≠ x ∧ z ≠ y := by
            intro z hz
            rcases hPsupp z hz with ⟨u, rfl, _⟩
            exact u.2
          have hclen : c₀.length = P.length + 2 := by
            rw [hc₀_eq, SimpleGraph.Walk.length_cons, hq_eq, SimpleGraph.Walk.length_append]
            simp [hPlen]; omega
          have hcsign : walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ =
              (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) *
              walkSignProd (matrixSignedGraph B hB.isSymm).sign P *
              (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
            rw [hc₀_eq, hq_eq]
            simp only [walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
              SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
              List.prod_cons, List.prod_append, List.prod_nil, mul_one, Sym2.eq_swap]
            rw [hPsign]
            ring
          have h1_ne : B x w₁.1 - B y w₁.1 ≠ 0 := by simpa [matrixGraph, A'₀, A', top] using h₁.2
          have h2_ne : B x w₂.1 - B y w₂.1 ≠ 0 := by simpa [matrixGraph, A'₀, A', top] using h₂.2
          have hcase1 := sign_diff_cases (B x w₁.1) (B y w₁.1) h1_ne
          have hcase2 := sign_diff_cases (B x w₂.1) (B y w₂.1) h2_ne
          have hw12 : w₁.1 ≠ w₂.1 := by
            intro hEq
            have hw : w₁ = w₂ := Subtype.ext hEq
            have h3 : 3 ≤ c₀.length := hc₀.three_le_length
            have hplen : 1 ≤ p.length := by omega
            have hstart : Sum.inr w₁ ∈ p.support := SimpleGraph.Walk.start_mem_support p
            -- If w₁ = w₂ and p.length ≥ 1, p.support has duplicate Sum.inr w₁
            cases hp : p with
            | nil => simp [hp] at hplen
            | @cons _ z _ hadjp r =>
              have hr_end : Sum.inr w₂ ∈ r.support := SimpleGraph.Walk.end_mem_support r
              rw [← hw] at hr_end
              rw [hp, SimpleGraph.Walk.support_cons, List.nodup_cons] at hp_nd
              exact hp_nd.1 hr_end
          have h_edge_cycle : ∀ (u₀ : V) (hu₀ : u₀ ∉ P.support)
              (ha : (matrixGraph B hB.isSymm).Adj u₀ w₁.1)
              (hb : (matrixGraph B hB.isSymm).Adj w₂.1 u₀),
              (SimpleGraph.Walk.cons ha (P.append (SimpleGraph.Walk.cons hb SimpleGraph.Walk.nil))).IsCycle := by
            intro u₀ hu₀ ha hb
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
            · -- edges nodup
              rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
                SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons]
              refine ⟨?_, ?_⟩
              · intro hm
                rcases List.mem_append.mp hm with hmP | hm2
                · exact hu₀ (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
                · simp only [List.mem_singleton] at hm2
                  rcases Sym2.eq_iff.mp hm2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                  · exact (matrixGraph B hB.isSymm).ne_of_adj hb h1'.symm
                  · exact hw12 h2'.symm
              · rw [List.nodup_append]
                refine ⟨hP_path.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
                intro e' he' e₂ he₂
                simp only [List.mem_singleton] at he₂
                subst he₂
                intro hEq
                subst hEq
                exact hu₀ (SimpleGraph.Walk.snd_mem_support_of_mem_edges P he')
            · exact SimpleGraph.Walk.cons_ne_nil _ _
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
          · -- Case (X₁, X₂): cycle x - w₁ - P - w₂ - x
            have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
            have hadj1 : (matrixGraph B hB.isSymm).Adj x w₁.1 := ⟨w₁.2.2.1.symm, hx1_ne⟩
            have hadj2 : (matrixGraph B hB.isSymm).Adj w₂.1 x := ⟨w₂.2.2.1, by rwa [hsym_B]⟩
            let cyc := SimpleGraph.Walk.cons hadj1 (P.append (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil))
            have hcyc : cyc.IsCycle := h_edge_cycle x hx_notP hadj1 hadj2
            have hcyc_len : cyc.length = c₀.length := by
              simp [cyc, hclen]; omega
            have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
                walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
              rw [hcsign]
              simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
                SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
                List.prod_cons, List.prod_append, List.prod_nil, mul_one]
              have hs1 : (matrixSignedGraph B hB.isSymm).sign s(x, w₁.1) =
                  (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
                simpa [matrixSignedGraph, A'₀, A', top] using hx1_s
              have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, x) =
                  (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
                rw [Sym2.eq_swap]
                simpa [matrixSignedGraph, A'₀, A', top] using hx2_s
              rw [hs1, hs2]; ring
            have hnoc_cyc := hB_noc x cyc hcyc (hcyc_len.symm ▸ hodd₀)
            simpa only [signedCycleType, hcyc_len, hcyc_sign] using hnoc_cyc
          · -- Case (X₁, Y₂): cycle x - w₁ - P - w₂ - y - v - x
            have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
            have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
            have hv_notP : v ∉ P.support := fun hm => (hP_avoid v hm).1 rfl
            have hadj1 : (matrixGraph B hB.isSymm).Adj x w₁.1 := ⟨w₁.2.2.1.symm, hx1_ne⟩
            have hadj2 : (matrixGraph B hB.isSymm).Adj w₂.1 y := ⟨w₂.2.2.2, by rwa [hsym_B]⟩
            have hadj3 : (matrixGraph B hB.isSymm).Adj y v := ⟨hvy.symm, by rw [hsym_B, hB_vy]; norm_num⟩
            have hadj4 : (matrixGraph B hB.isSymm).Adj v x := ⟨hvx, by rw [hB_vx]; norm_num⟩
            let tailW := SimpleGraph.Walk.cons hadj2
              (SimpleGraph.Walk.cons hadj3 (SimpleGraph.Walk.cons hadj4 SimpleGraph.Walk.nil))
            let cyc := SimpleGraph.Walk.cons hadj1 (P.append tailW)
            have hcyc : cyc.IsCycle := by
              refine ⟨⟨?_, ?_⟩, SimpleGraph.Walk.cons_ne_nil _ _, ?_⟩
              · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append, List.nodup_cons]
                refine ⟨?_, ?_⟩
                · intro hm
                  rcases List.mem_append.mp hm with hmP | hmt
                  · exact hx_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
                  · simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                      List.mem_cons, List.not_mem_nil, or_false] at hmt
                    rcases hmt with h | h | h
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                      · exact w₁.2.2.1 h1'.symm
                      · exact hxy h2'
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                      · exact hxy h1'
                      · exact hvx h1'.symm
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                      · exact hvx h1'.symm
                      · exact w₁.2.1 h2'.symm
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
            have hcyc_len : cyc.length = c₀.length + 2 := by
              simp [cyc, tailW, hclen]; omega
            have hcyc_odd : Odd cyc.length := by
              rcases hodd₀ with ⟨k, hk⟩
              exact ⟨k + 1, by omega⟩
            have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
                - walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
              rw [hcsign]
              simp only [cyc, tailW, walkSignProd, SimpleGraph.Walk.edges_cons,
                SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_nil,
                List.map_cons, List.map_append, List.map_nil,
                List.prod_cons, List.prod_append, List.prod_nil, mul_one]
              have hs1 : (matrixSignedGraph B hB.isSymm).sign s(x, w₁.1) =
                  (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
                simpa [matrixSignedGraph, A'₀, A', top] using hx1_s
              have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, y) =
                  -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
                rw [Sym2.eq_swap]
                simpa [matrixSignedGraph, A'₀, A', top] using hy2_s
              have hs3 : (matrixSignedGraph B hB.isSymm).sign s(y, v) = 1 := by
                simp [matrixSignedGraph, hsym_B y v, hB_vy]
              have hs4 : (matrixSignedGraph B hB.isSymm).sign s(v, x) = 1 := by
                simp [matrixSignedGraph, hB_vx]
              rw [hs1, hs2, hs3, hs4]; ring
            have hnoc_cyc := hB_noc x cyc hcyc hcyc_odd
            rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
            have hdiv : (c₀.length + 2) / 2 = c₀.length / 2 + 1 := by omega
            rw [hdiv, pow_succ] at hnoc_cyc
            rw [signedCycleType]
            linarith
          · -- Case (Y₁, X₂): cycle y - w₁ - P - w₂ - x - v - y
            have hx_notP : x ∉ P.support := fun hm => (hP_avoid x hm).2.1 rfl
            have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
            have hv_notP : v ∉ P.support := fun hm => (hP_avoid v hm).1 rfl
            have hadj1 : (matrixGraph B hB.isSymm).Adj y w₁.1 := ⟨w₁.2.2.2.symm, hy1_ne⟩
            have hadj2 : (matrixGraph B hB.isSymm).Adj w₂.1 x := ⟨w₂.2.2.1, by rwa [hsym_B]⟩
            have hadj3 : (matrixGraph B hB.isSymm).Adj x v := ⟨hvx.symm, by rw [hsym_B, hB_vx]; norm_num⟩
            have hadj4 : (matrixGraph B hB.isSymm).Adj v y := ⟨hvy, by rw [hB_vy]; norm_num⟩
            let tailW := SimpleGraph.Walk.cons hadj2
              (SimpleGraph.Walk.cons hadj3 (SimpleGraph.Walk.cons hadj4 SimpleGraph.Walk.nil))
            let cyc := SimpleGraph.Walk.cons hadj1 (P.append tailW)
            have hcyc : cyc.IsCycle := by
              refine ⟨⟨?_, ?_⟩, SimpleGraph.Walk.cons_ne_nil _ _, ?_⟩
              · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append, List.nodup_cons]
                refine ⟨?_, ?_⟩
                · intro hm
                  rcases List.mem_append.mp hm with hmP | hmt
                  · exact hy_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hmP)
                  · simp only [tailW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                      List.mem_cons, List.not_mem_nil, or_false] at hmt
                    rcases hmt with h | h | h
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                      · exact w₁.2.2.2 h1'.symm
                      · exact hxy h2'.symm
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨h1', _⟩
                      · exact hxy h1'.symm
                      · exact hvy h1'.symm
                    · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
                      · exact hvy h1'.symm
                      · exact w₁.2.1 h2'.symm
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
            have hcyc_len : cyc.length = c₀.length + 2 := by
              simp [cyc, tailW, hclen]; omega
            have hcyc_odd : Odd cyc.length := by
              rcases hodd₀ with ⟨k, hk⟩
              exact ⟨k + 1, by omega⟩
            have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
                - walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
              rw [hcsign]
              simp only [cyc, tailW, walkSignProd, SimpleGraph.Walk.edges_cons,
                SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_nil,
                List.map_cons, List.map_append, List.map_nil,
                List.prod_cons, List.prod_append, List.prod_nil, mul_one]
              have hs1 : (matrixSignedGraph B hB.isSymm).sign s(y, w₁.1) =
                  -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
                simpa [matrixSignedGraph, A'₀, A', top] using hy1_s
              have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, x) =
                  (matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
                rw [Sym2.eq_swap]
                simpa [matrixSignedGraph, A'₀, A', top] using hx2_s
              have hs3 : (matrixSignedGraph B hB.isSymm).sign s(x, v) = 1 := by
                simp [matrixSignedGraph, hsym_B x v, hB_vx]
              have hs4 : (matrixSignedGraph B hB.isSymm).sign s(v, y) = 1 := by
                simp [matrixSignedGraph, hB_vy]
              rw [hs1, hs2, hs3, hs4]; ring
            have hnoc_cyc := hB_noc y cyc hcyc hcyc_odd
            rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
            have hdiv : (c₀.length + 2) / 2 = c₀.length / 2 + 1 := by omega
            rw [hdiv, pow_succ] at hnoc_cyc
            rw [signedCycleType]
            linarith
          · -- Case (Y₁, Y₂): cycle y - w₁ - P - w₂ - y
            have hy_notP : y ∉ P.support := fun hm => (hP_avoid y hm).2.2 rfl
            have hadj1 : (matrixGraph B hB.isSymm).Adj y w₁.1 := ⟨w₁.2.2.2.symm, hy1_ne⟩
            have hadj2 : (matrixGraph B hB.isSymm).Adj w₂.1 y := ⟨w₂.2.2.2, by rwa [hsym_B]⟩
            let cyc := SimpleGraph.Walk.cons hadj1 (P.append (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil))
            have hcyc : cyc.IsCycle := h_edge_cycle y hy_notP hadj1 hadj2
            have hcyc_len : cyc.length = c₀.length := by
              simp [cyc, hclen]; omega
            have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
                walkSignProd (matrixSignedGraph A'₀ hA'₀.isSymm).sign c₀ := by
              rw [hcsign]
              simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
                SimpleGraph.Walk.edges_nil, List.map_cons, List.map_append, List.map_nil,
                List.prod_cons, List.prod_append, List.prod_nil, mul_one]
              have hs1 : (matrixSignedGraph B hB.isSymm).sign s(y, w₁.1) =
                  -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₁) := by
                simpa [matrixSignedGraph, A'₀, A', top] using hy1_s
              have hs2 : (matrixSignedGraph B hB.isSymm).sign s(w₂.1, y) =
                  -(matrixSignedGraph A'₀ hA'₀.isSymm).sign s(top, Sum.inr w₂) := by
                rw [Sym2.eq_swap]
                simpa [matrixSignedGraph, A'₀, A', top] using hy2_s
              rw [hs1, hs2]; ring
            have hnoc_cyc := hB_noc y cyc hcyc (hcyc_len.symm ▸ hodd₀)
            simpa only [signedCycleType, hcyc_len, hcyc_sign] using hnoc_cyc
    · -- c avoids top, so it lifts directly to a cycle in B
      cases z₀ with
      | inl u =>
        cases u
        exact absurd (SimpleGraph.Walk.start_mem_support c) htop
      | inr w₀ =>
        obtain ⟨q, hqlen, hqsign, _, _, hqcyc⟩ := hlift c htop
        have hnoc_q := hB_noc w₀.1 q (hqcyc hc) (hqlen.symm ▸ hodd)
        simpa only [signedCycleType, hqlen, hqsign] using hnoc_q
  have hA'₀_le := ih (Unit ⊕ U) hcard_U A'₀ hA'₀ hA'₀_diag hA'₀_noc
  omega

end SignedGraphs
