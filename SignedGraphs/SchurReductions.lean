import SignedGraphs.LinearAlgebraExtra
import SignedGraphs.ParityAndCycles

/-!
# Schur-Complement Reductions for K₄ and Petersen Leaves (Section 5)

Formalization of:
- `k4_signature_nonpos` (Lemma 5.1(1)) and `k4_leaf_reduction` (Lemma 5.1(2)).
- `petersen_signature_nonpos` (Lemma 5.2(1)) and `petersen_leaf_reduction` (Lemma 5.2(2)).
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Lemma 5.1(1)**: Every weighted `(K₄, +1)` NOC matrix has `s(A) ≤ 0`. -/
theorem k4_signature_nonpos (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0)
    (hiso : SwitchingIso (matrixSignedGraph A hA.isSymm) k4SignedGraph) :
    signature A hA ≤ 0 := by
  classical
  rcases hiso with ⟨e, T, hT⟩
  let d : V → ℝ := fun u => if u ∈ T then -1 else 1
  have hd_ne : ∀ u, d u ≠ 0 := fun u => by dsimp [d]; split_ifs <;> norm_num
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun u _ => hd_ne u)
  let B₀ : Matrix V V ℝ := Dᵀ * A * D
  have hB₀ : B₀.IsHermitian := isHermitian_congr A D hA
  let B : Matrix (Fin 4) (Fin 4) ℝ := B₀.submatrix e.symm.toEquiv e.symm.toEquiv
  have hB : B.IsHermitian := isHermitian_submatrix B₀ hB₀ e.symm.toEquiv
  rw [← signature_congr A D hA hD_det, ← signature_reindex e.symm.toEquiv B₀ hB₀]
  change signature B hB ≤ 0
  have hB_diag : ∀ i : Fin 4, B i i = 0 := fun i => by
    simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hdiag]
  have hB_sym : ∀ i j : Fin 4, B i j = B j i := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq i) j).symm
  have hB_pos : ∀ i j : Fin 4, i ≠ j → 0 < B i j := by
    intro i j hij
    have hadjK : k4SignedGraph.graph.Adj i j := hij
    have hadjA : (matrixSignedGraph A hA.isSymm).graph.Adj (e.symm i) (e.symm j) := by
      simpa [e.map_rel_iff] using hadjK
    have hAne : A (e.symm i) (e.symm j) ≠ 0 := hadjA.2
    have hsw := hT (e.symm i) (e.symm j) hadjA
    simp only [k4SignedGraph, matrixSignedGraph, Sym2.lift_mk] at hsw
    have hBij : B i j = d (e.symm i) * A (e.symm i) (e.symm j) * d (e.symm j) := by
      simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [hBij]
    dsimp [d]
    by_cases hi : e.symm i ∈ T <;> by_cases hj : e.symm j ∈ T <;>
      rcases lt_or_gt_of_ne hAne with ha | ha <;>
      simp [hi, hj, ha, not_lt.mpr ha.le] at hsw ⊢ <;> nlinarith
  let a : ℝ := B 0 1
  let b : ℝ := B 0 2
  let c : ℝ := B 1 2
  have ha : 0 < a := hB_pos 0 1 (by decide)
  have hb : 0 < b := hB_pos 0 2 (by decide)
  have hc : 0 < c := hB_pos 1 2 (by decide)
  let ι : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun y i => if h : i.val < 3 then y ⟨i.val, h⟩ else 0
      map_add' := fun y₁ y₂ => by ext i; split_ifs <;> simp
      map_smul' := fun r y => by ext i; split_ifs <;> simp }
  have hι_inj : Function.Injective ι := by
    intro y₁ y₂ h
    ext ⟨i, hi⟩
    have := congrFun h ⟨i, by omega⟩
    simpa [ι, hi] using this
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => a * b * y 0 + a * c * y 1 + b * c * y 2
      map_add' := fun y₁ y₂ => by simp; ring
      map_smul' := fun r y => by simp; ring }
  have hL_surj : Function.Surjective L := by
    intro r
    refine ⟨fun i => if i = 0 then (a * b)⁻¹ * r else 0, ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, Fin.isValue, Fin.one_eq_zero_iff,
      Fin.reduceEq, mul_zero, add_zero]
    have hab : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
    field_simp [hab]
  have hfin_ker : Module.finrank ℝ (LinearMap.ker L) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have hr : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hL_surj
    rw [hr, finrank_top, Module.finrank_self] at h1
    omega
  have hneg_ge : 2 ≤ negInertia B hB := by
    rw [negInertia_eq_sSup]
    refine le_csSup ⟨4, by rintro n ⟨W, rfl, _⟩; simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W⟩ ?_
    refine ⟨(LinearMap.ker L).map ι, ?_, ?_⟩
    · rw [(Submodule.equivMapOfInjective ι hι_inj (LinearMap.ker L)).finrank_eq.symm, hfin_ker]
    · rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      have hLy : a * b * y 0 + a * c * y 1 + b * c * y 2 = 0 := LinearMap.mem_ker.mp hy
      have hquad : dotProduct (ι y) (B *ᵥ ι y) =
          2 * (a * y 0 * y 1 + b * y 0 * y 2 + c * y 1 * y 2) := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four, ι, LinearMap.coe_mk,
          AddHom.coe_mk, hB_diag, hB_sym 1 0, hB_sym 2 0, hB_sym 2 1, a, b, c]
        norm_num
        ring
      rw [hquad]
      have hsum_sq_pos : 0 < (a * b * y 0) ^ 2 + (a * c * y 1) ^ 2 + (b * c * y 2) ^ 2 := by
        have hex : ∃ i : Fin 3, y i ≠ 0 := by
          by_contra hnone; push Not at hnone; exact hy0 (funext hnone)
        rcases hex with ⟨i, hi⟩
        fin_cases i
        · have h0 : a * b * y 0 ≠ 0 := mul_ne_zero (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)) hi
          nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (a * c * y 1), sq_nonneg (b * c * y 2)]
        · have h1 : a * c * y 1 ≠ 0 := mul_ne_zero (mul_ne_zero (ne_of_gt ha) (ne_of_gt hc)) hi
          nlinarith [sq_nonneg (a * b * y 0), sq_pos_of_ne_zero h1, sq_nonneg (b * c * y 2)]
        · have h2 : b * c * y 2 ≠ 0 := mul_ne_zero (mul_ne_zero (ne_of_gt hb) (ne_of_gt hc)) hi
          nlinarith [sq_nonneg (a * b * y 0), sq_nonneg (a * c * y 1), sq_pos_of_ne_zero h2]
      have hid : a * b * c * (2 * (a * y 0 * y 1 + b * y 0 * y 2 + c * y 1 * y 2)) =
          (a * b * y 0 + a * c * y 1 + b * c * y 2) ^ 2 -
            ((a * b * y 0) ^ 2 + (a * c * y 1) ^ 2 + (b * c * y 2) ^ 2) := by ring
      have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
      nlinarith
  have hsum := inertia_sum B hB
  rw [Fintype.card_fin] at hsum
  simp only [signature]
  omega

/-- **Lemma 5.1(2)**: Weighted `(K₄ - xy, +1)` leaf reduction (`|V| - 2`). -/
theorem k4_leaf_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (VH VG₂ : Finset V) (x y : V) (hxy : x ≠ y)
    (hunion : VH ∪ VG₂ = Finset.univ) (hinter : VH ∩ VG₂ = {x, y})
    (hcardH : VH.card = 4)
    (hno_cross : ∀ u ∈ VH, ∀ w ∈ VG₂, u ≠ x → u ≠ y → w ≠ x → w ≠ y → A u w = 0)
    (hH_iso : ∃ (e : Fin 4 ≃ VH),
      (e 0).1 = x ∧ (e 1).1 = y ∧
      A (e 2).1 (e 3).1 ≠ 0 ∧ A (e 0).1 (e 2).1 ≠ 0 ∧ A (e 0).1 (e 3).1 ≠ 0 ∧
      A (e 1).1 (e 2).1 ≠ 0 ∧ A (e 1).1 (e 3).1 ≠ 0)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W = Fintype.card V - 2 →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ z, B z z = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  sorry

/-- **Lemma 5.2(1)**: Every weighted `(Petersen, -1)` NOC matrix has `s(A) ≤ 0`. -/
theorem petersen_signature_nonpos (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0)
    (hiso : SwitchingIso (matrixSignedGraph A hA.isSymm) petersenSignedGraph) :
    signature A hA ≤ 0 := by
  sorry

/-- **Lemma 5.2(2)**: Weighted `(Petersen - xy, -1)` leaf reduction (`|V| - 8` or `|V| - 10`). -/
theorem petersen_leaf_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (VH VG₂ : Finset V) (x y : V) (hxy : x ≠ y)
    (hunion : VH ∪ VG₂ = Finset.univ) (hinter : VH ∩ VG₂ = {x, y})
    (hcardH : VH.card = 10)
    (hno_cross : ∀ u ∈ VH, ∀ w ∈ VG₂, u ≠ x → u ≠ y → w ≠ x → w ≠ y → A u w = 0)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W ≤ Fintype.card V - 8 →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ z, B z z = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  sorry

end SignedGraphs
