import SignedGraphs.LinearAlgebraExtra

/-!
# Explicit Matrix Algebra for Weighted Petersen Graphs (Lemma 5.2)

Contains the explicit finite-dimensional matrix factorizations, inverses, and sign
computations for the 8×8 Petersen interior `A_int = [[0, B], [Bᵀ, C]]` in both
Case 1 (`det B ≠ 0`) and Case 2 (`det B = 0`).
-/

open Matrix

namespace SignedGraphs

/-- The 4×4 bipartite block `B` between `U = (2, 4, 5, 6)` and `W = (3, 7, 8, 9)`
for edge-weight magnitudes `w : Fin 14 → ℝ`. -/
def petersenB (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-w 1, -w 11, 0, 0;
     -w 2, 0, 0, -w 13;
     0, -w 4, -w 7, 0;
     0, 0, -w 5, -w 8]

/-- The 4×4 block `C` on `W = (3, 7, 8, 9)` (edges `3-8` and `7-9`). -/
def petersenC (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -w 12, 0;
     0, 0, 0, -w 6;
     -w 12, 0, 0, 0;
     0, -w 6, 0, 0]

/-- The 4×2 attachment block `R_U` from `U = (2, 4, 5, 6)` to `{0, 1}`. -/
def petersenRU (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![0, -w 0;
     -w 3, 0;
     -w 9, 0;
     0, -w 10]

/-- The 8×8 interior matrix `A_int = [[0, B], [Bᵀ, C]]` on `Fin 4 ⊕ Fin 4`. -/
def petersenAint (w : Fin 14 → ℝ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks 0 (petersenB w) (petersenB w)ᵀ (petersenC w)

/-- The 8×2 attachment matrix `R = [R_U; 0]` on `(Fin 4 ⊕ Fin 4) × Fin 2`. -/
def petersenR (w : Fin 14 → ℝ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 2) ℝ :=
  Matrix.of fun i j => match i with
    | Sum.inl a => petersenRU w a j
    | Sum.inr _ => 0

/-- Explicit determinant `det(B) = w₁w₄w₅w₁₃ - w₂w₇w₈w₁₁`. -/
def petersenDetB (w : Fin 14 → ℝ) : ℝ :=
  w 1 * w 4 * w 5 * w 13 - w 2 * w 7 * w 8 * w 11

/-- Explicit adjugate `adj(B)` satisfying `B * adj(B) = det(B) • 1`. -/
def petersenBadj (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-w 4 * w 5 * w 13,  w 11 * w 7 * w 8,   w 11 * w 5 * w 13,  -w 11 * w 7 * w 13;
      w 2 * w 7 * w 8,  -w 1 * w 7 * w 8,   -w 1 * w 5 * w 13,    w 1 * w 7 * w 13;
     -w 2 * w 4 * w 8,   w 1 * w 4 * w 8,    w 11 * w 2 * w 8,   -w 1 * w 4 * w 13;
      w 2 * w 4 * w 5,  -w 1 * w 4 * w 5,   -w 11 * w 2 * w 5,    w 11 * w 2 * w 7]

/-- Explicit inverse `B⁻¹ = (det B)⁻¹ • adj(B)` (valid when `det B ≠ 0`). -/
def petersenBinv (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (petersenDetB w)⁻¹ • petersenBadj w

/-- Explicit inverse of `A_int` in Case 1 (`det B ≠ 0`). -/
def petersenAintInv (w : Fin 14 → ℝ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks (-(petersenBinv w)ᵀ * petersenC w * petersenBinv w)
    (petersenBinv w)ᵀ (petersenBinv w) 0

/-- The 2×2 Schur complement `M_H = (B⁻¹ R_U)ᵀ C (B⁻¹ R_U)` on `{0, 1}`. -/
def petersenMH (w : Fin 14 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (petersenBinv w * petersenRU w)ᵀ * petersenC w * (petersenBinv w * petersenRU w)

lemma isHermitian_petersenC (w : Fin 14 → ℝ) : (petersenC w).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [petersenC, Matrix.conjTranspose_apply]

lemma petersenC_transpose (w : Fin 14 → ℝ) : (petersenC w)ᵀ = petersenC w := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenC w).eq

lemma isHermitian_petersenAint (w : Fin 14 → ℝ) : (petersenAint w).IsHermitian := by
  change (petersenAint w)ᴴ = petersenAint w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [petersenAint, Matrix.fromBlocks_transpose, petersenC_transpose]

lemma petersenB_mul_Badj (w : Fin 14 → ℝ) :
    petersenB w * petersenBadj w = petersenDetB w • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [petersenB, petersenBadj, petersenDetB, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma petersenBadj_mul_B (w : Fin 14 → ℝ) :
    petersenBadj w * petersenB w = petersenDetB w • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [petersenB, petersenBadj, petersenDetB, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma petersenB_mul_Binv (w : Fin 14 → ℝ) (hdet : petersenDetB w ≠ 0) :
    petersenB w * petersenBinv w = 1 := by
  simp only [petersenBinv, Matrix.mul_smul, petersenB_mul_Badj, smul_smul,
    inv_mul_cancel₀ hdet, one_smul]

lemma petersenBinv_mul_B (w : Fin 14 → ℝ) (hdet : petersenDetB w ≠ 0) :
    petersenBinv w * petersenB w = 1 := by
  simp only [petersenBinv, Matrix.smul_mul, petersenBadj_mul_B, smul_smul,
    inv_mul_cancel₀ hdet, one_smul]

lemma petersenAint_mul_AintInv (w : Fin 14 → ℝ) (hdet : petersenDetB w ≠ 0) :
    petersenAint w * petersenAintInv w = 1 := by
  have h1 : petersenB w * petersenBinv w = 1 := petersenB_mul_Binv w hdet
  have h2 : (petersenB w)ᵀ * (petersenBinv w)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, petersenBinv_mul_B w hdet, Matrix.transpose_one]
  simp only [petersenAint, petersenAintInv, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, h1, h2, Matrix.one_mul, neg_add_cancel,
    Matrix.fromBlocks_one]

/-- Helper: any block matrix `[[0, M], [Mᵀ, 0]]` has signature `0`. -/
lemma signature_offdiag_block_zero {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hH : (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) M Mᵀ 0).IsHermitian) :
    signature (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) M Mᵀ 0) hH = 0 := by
  let D : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := Matrix.fromBlocks 1 0 0 (-1)
  have hD2 : D * D = 1 := by
    simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hD_det : IsUnit D.det :=
    isUnit_iff_exists_inv.mpr ⟨D.det, by rw [← Matrix.det_mul, hD2, Matrix.det_one]⟩
  have hcongr : Dᵀ * Matrix.fromBlocks 0 M Mᵀ 0 * D = -Matrix.fromBlocks 0 M Mᵀ 0 := by
    simp [D, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
  have hs := signature_congr (Matrix.fromBlocks 0 M Mᵀ 0) D hH hD_det
  have hneg_eq : signature (Dᵀ * Matrix.fromBlocks 0 M Mᵀ 0 * D) (isHermitian_congr _ D hH) =
      signature (-Matrix.fromBlocks 0 M Mᵀ 0) (isHermitian_neg _ hH) := by
    congr 1
  rw [hneg_eq, signature_neg] at hs
  omega

/-- Case 1 (`det B ≠ 0`): `s(A_int) = 0`. -/
lemma signature_petersenAint_eq_zero (w : Fin 14 → ℝ) (hdet : petersenDetB w ≠ 0) :
    signature (petersenAint w) (isHermitian_petersenAint w) = 0 := by
  let X : Matrix (Fin 4) (Fin 4) ℝ := -(1 / 2 : ℝ) • ((petersenBinv w)ᵀ * petersenC w)
  let P : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 X 0 1
  let Q : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 (-X) 0 1
  have hPQ : P * Q = 1 := by
    simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hP_det : IsUnit P.det :=
    isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
  have hBT_BinvT : (petersenB w)ᵀ * (petersenBinv w)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, petersenBinv_mul_B w hdet, Matrix.transpose_one]
  have hBinv_B : petersenBinv w * petersenB w = 1 := petersenBinv_mul_B w hdet
  have hXT : Xᵀ = -(1 / 2 : ℝ) • (petersenC w * petersenBinv w) := by
    simp [X, Matrix.transpose_smul, Matrix.transpose_mul, petersenC_transpose]
  have hBT_X : (petersenB w)ᵀ * X = -(1 / 2 : ℝ) • petersenC w := by
    simp [X, Matrix.mul_smul, ← Matrix.mul_assoc, hBT_BinvT]
  have hXT_B : Xᵀ * petersenB w = -(1 / 2 : ℝ) • petersenC w := by
    simp [hXT, Matrix.smul_mul, Matrix.mul_assoc, hBinv_B]
  have hcongr : Pᵀ * petersenAint w * P = Matrix.fromBlocks 0 (petersenB w) (petersenB w)ᵀ 0 := by
    simp only [P, petersenAint, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    congr 1
    rw [hXT_B, hBT_X]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    ring
  have hOffH : (Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) ℝ) (petersenB w) (petersenB w)ᵀ 0).IsHermitian := by
    change (Matrix.fromBlocks 0 (petersenB w) (petersenB w)ᵀ 0)ᴴ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [Matrix.fromBlocks_transpose]
  rw [← signature_congr (petersenAint w) P (isHermitian_petersenAint w) hP_det]
  have hEq : signature (Pᵀ * petersenAint w * P) (isHermitian_congr _ P (isHermitian_petersenAint w)) =
      signature (Matrix.fromBlocks 0 (petersenB w) (petersenB w)ᵀ 0) hOffH := by
    congr 1
  rw [hEq]
  exact signature_offdiag_block_zero (petersenB w) hOffH

/-- In Case 1, `-(Rᵀ A_int⁻¹ R) = M_H`. -/
lemma petersen_schur_eq_MH (w : Fin 14 → ℝ) :
    -((petersenR w)ᵀ * petersenAintInv w * petersenR w) = petersenMH w := by
  have hR : petersenR w = Matrix.fromBlocks (petersenRU w) (0 : Matrix (Fin 4) (Fin 0) ℝ)
      (0 : Matrix (Fin 4) (Fin 2) ℝ) (0 : Matrix (Fin 4) (Fin 0) ℝ) := by
    ext i j; rcases i with a | b <;> rcases j with j | j
    · rfl
    · exact Fin.elim0 j
    · rfl
    · exact Fin.elim0 j
  ext i j
  simp only [petersenMH, petersenAintInv, petersenR, Matrix.neg_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.neg_mul, Matrix.mul_neg]
  simp only [Finset.sum_neg_distrib, neg_neg]
  have h1 : ∀ k : Fin 4, ∑ x : Fin 4,
      (∑ x_1 : Fin 4, petersenRU w x_1 i * ∑ x_2 : Fin 4, petersenBinv w x_2 x_1 * petersenC w x_2 x) *
        petersenBinv w x k * petersenRU w k j =
      ∑ x : Fin 4, (∑ x_2 : Fin 4,
        (∑ x_1 : Fin 4, petersenBinv w x_2 x_1 * petersenRU w x_1 i) * petersenC w x_2 x) *
        (petersenBinv w x k * petersenRU w k j) := by
    intro k
    refine Finset.sum_congr rfl fun x _ => ?_
    have hinner : ∑ x_1 : Fin 4, petersenRU w x_1 i * ∑ x_2 : Fin 4, petersenBinv w x_2 x_1 * petersenC w x_2 x =
        ∑ x_2 : Fin 4, (∑ x_1 : Fin 4, petersenBinv w x_2 x_1 * petersenRU w x_1 i) * petersenC w x_2 x := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x_2 _ => Finset.sum_congr rfl fun x_1 _ => by ring
    rw [hinner]; ring
  calc ∑ x : Fin 4, (∑ x_1 : Fin 4, petersenRU w x_1 i *
        ∑ x_2 : Fin 4, (∑ x_3 : Fin 4, petersenBinv w x_3 x_1 * petersenC w x_3 x_2) * petersenBinv w x_2 x) *
        petersenRU w x j
      = ∑ x : Fin 4, (∑ x_2 : Fin 4,
          (∑ x_1 : Fin 4, petersenRU w x_1 i * ∑ x_3 : Fin 4, petersenBinv w x_3 x_1 * petersenC w x_3 x_2) *
          petersenBinv w x_2 x) * petersenRU w x j := by
        refine Finset.sum_congr rfl fun x _ => ?_
        congr 1
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_2 _ => Finset.sum_congr rfl fun x_1 _ => by ring
    _ = ∑ x : Fin 4, ∑ x_2 : Fin 4,
          (∑ x_1 : Fin 4, petersenRU w x_1 i * ∑ x_3 : Fin 4, petersenBinv w x_3 x_1 * petersenC w x_3 x_2) *
          petersenBinv w x_2 x * petersenRU w x j := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _
    _ = ∑ x : Fin 4, ∑ x_2 : Fin 4,
          (∑ x_3 : Fin 4, (∑ x_1 : Fin 4, petersenBinv w x_3 x_1 * petersenRU w x_1 i) * petersenC w x_3 x_2) *
          (petersenBinv w x_2 x * petersenRU w x j) := by
        refine Finset.sum_congr rfl fun x _ => h1 x
    _ = ∑ x_2 : Fin 4,
          (∑ x_3 : Fin 4, (∑ x_1 : Fin 4, petersenBinv w x_3 x_1 * petersenRU w x_1 i) * petersenC w x_3 x_2) *
          ∑ x : Fin 4, petersenBinv w x_2 x * petersenRU w x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_2 _ => (Finset.mul_sum _ _ _).symm

lemma isHermitian_petersenMH (w : Fin 14 → ℝ) : (petersenMH w).IsHermitian := by
  change (petersenMH w)ᴴ = petersenMH w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [petersenMH, Matrix.transpose_mul, petersenC_transpose, Matrix.mul_assoc]

/-- Exact sign structure of `M_H` in Case 1: `(M_H)₀₀ < 0`, `(M_H)₁₁ < 0`, `(M_H)₀₁ > 0`. -/
lemma petersenMH_signs (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) (hdet : petersenDetB w ≠ 0) :
    petersenMH w 0 0 < 0 ∧ petersenMH w 1 1 < 0 ∧ 0 < petersenMH w 0 1 ∧
      petersenMH w 1 0 = petersenMH w 0 1 := by
  have hsym : petersenMH w 1 0 = petersenMH w 0 1 := by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun (isHermitian_petersenMH w).eq 0) 1)
  let V : Matrix (Fin 4) (Fin 2) ℝ := petersenBadj w * petersenRU w
  have hMH_eq : ∀ i j : Fin 2, petersenMH w i j =
      ((petersenDetB w) ^ 2)⁻¹ * (Vᵀ * petersenC w * V) i j := by
    intro i j
    have h1 : petersenBinv w * petersenRU w = (petersenDetB w)⁻¹ • V := by
      simp [V, petersenBinv, Matrix.smul_mul]
    rw [petersenMH, h1]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_apply,
      smul_eq_mul]
    ring
  have hv00 : V 0 0 = -w 11 * (w 13 * w 5 * w 9 + w 3 * w 7 * w 8) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv10 : V 1 0 = w 1 * (w 13 * w 5 * w 9 + w 3 * w 7 * w 8) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv20 : V 2 0 = -w 8 * (w 1 * w 3 * w 4 + w 11 * w 2 * w 9) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv30 : V 3 0 = w 5 * (w 1 * w 3 * w 4 + w 11 * w 2 * w 9) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv01 : V 0 1 = w 13 * (w 0 * w 4 * w 5 + w 10 * w 11 * w 7) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv11 : V 1 1 = -w 7 * (w 0 * w 2 * w 8 + w 1 * w 10 * w 13) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv21 : V 2 1 = w 4 * (w 0 * w 2 * w 8 + w 1 * w 10 * w 13) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hv31 : V 3 1 = -w 2 * (w 0 * w 4 * w 5 + w 10 * w 11 * w 7) := by
    simp [V, petersenBadj, petersenRU, Matrix.mul_apply, Fin.sum_univ_four]; ring
  have hA : 0 < w 13 * w 5 * w 9 + w 3 * w 7 * w 8 := by positivity
  have hB : 0 < w 1 * w 3 * w 4 + w 11 * w 2 * w 9 := by positivity
  have hC : 0 < w 0 * w 4 * w 5 + w 10 * w 11 * w 7 := by positivity
  have hD : 0 < w 0 * w 2 * w 8 + w 1 * w 10 * w 13 := by positivity
  have hV00_neg : V 0 0 < 0 := by rw [hv00]; nlinarith [hw 11, hA]
  have hV10_pos : 0 < V 1 0 := by rw [hv10]; nlinarith [hw 1, hA]
  have hV20_neg : V 2 0 < 0 := by rw [hv20]; nlinarith [hw 8, hB]
  have hV30_pos : 0 < V 3 0 := by rw [hv30]; nlinarith [hw 5, hB]
  have hV01_pos : 0 < V 0 1 := by rw [hv01]; nlinarith [hw 13, hC]
  have hV11_neg : V 1 1 < 0 := by rw [hv11]; nlinarith [hw 7, hD]
  have hV21_pos : 0 < V 2 1 := by rw [hv21]; nlinarith [hw 4, hD]
  have hV31_neg : V 3 1 < 0 := by rw [hv31]; nlinarith [hw 2, hC]
  have hinv_pos : 0 < ((petersenDetB w) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hdet)
  have hquad : ∀ i j : Fin 2, (Vᵀ * petersenC w * V) i j =
      -w 12 * (V 0 i * V 2 j + V 2 i * V 0 j) - w 6 * (V 1 i * V 3 j + V 3 i * V 1 j) := by
    intro i j
    simp [petersenC, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    ring
  refine ⟨?_, ?_, ?_, hsym⟩
  · rw [hMH_eq 0 0, hquad 0 0]
    have h1 : 0 < V 0 0 * V 2 0 := mul_pos_of_neg_of_neg hV00_neg hV20_neg
    have h2 : 0 < V 1 0 * V 3 0 := mul_pos hV10_pos hV30_pos
    have hneg : -w 12 * (V 0 0 * V 2 0 + V 2 0 * V 0 0) - w 6 * (V 1 0 * V 3 0 + V 3 0 * V 1 0) < 0 := by
      nlinarith [hw 12, hw 6]
    nlinarith
  · rw [hMH_eq 1 1, hquad 1 1]
    have h1 : 0 < V 0 1 * V 2 1 := mul_pos hV01_pos hV21_pos
    have h2 : 0 < V 1 1 * V 3 1 := mul_pos_of_neg_of_neg hV11_neg hV31_neg
    have hneg : -w 12 * (V 0 1 * V 2 1 + V 2 1 * V 0 1) - w 6 * (V 1 1 * V 3 1 + V 3 1 * V 1 1) < 0 := by
      nlinarith [hw 12, hw 6]
    nlinarith
  · rw [hMH_eq 0 1, hquad 0 1]
    have h1 : V 0 0 * V 2 1 < 0 := mul_neg_of_neg_of_pos hV00_neg hV21_pos
    have h2 : V 2 0 * V 0 1 < 0 := mul_neg_of_neg_of_pos hV20_neg hV01_pos
    have h3 : V 1 0 * V 3 1 < 0 := mul_neg_of_pos_of_neg hV10_pos hV31_neg
    have h4 : V 3 0 * V 1 1 < 0 := mul_neg_of_pos_of_neg hV30_pos hV11_neg
    have hpos : 0 < -w 12 * (V 0 0 * V 2 1 + V 2 0 * V 0 1) - w 6 * (V 1 0 * V 3 1 + V 3 0 * V 1 1) := by
      nlinarith [hw 12, hw 6]
    exact mul_pos hinv_pos hpos

/-! ### Case 2 (`det(B) = 0`): Explicit Basis Reduction and 7×7 Interior Signature `-1` -/

/-- Left kernel vector `p ∈ ker(Bᵀ)` with `p 0 = 1`. -/
def petersenP (w : Fin 14 → ℝ) : Fin 4 → ℝ :=
  ![1, -w 1 / w 2, -w 11 / w 4, (w 11 * w 7) / (w 4 * w 5)]

/-- Right kernel vector `q ∈ ker(B)` with `q 0 = 1`. -/
def petersenQ (w : Fin 14 → ℝ) : Fin 4 → ℝ :=
  ![1, -w 1 / w 11, (w 1 * w 4) / (w 11 * w 7), -w 2 / w 13]

/-- Lower-triangular basis matrix `P_U` putting `p` in column `0` and `e₁, e₂, e₃` in columns `1, 2, 3`. -/
def petersenPU (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     petersenP w 1, 1, 0, 0;
     petersenP w 2, 0, 1, 0;
     petersenP w 3, 0, 0, 1]

def petersenPUinv (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     -petersenP w 1, 1, 0, 0;
     -petersenP w 2, 0, 1, 0;
     -petersenP w 3, 0, 0, 1]

/-- Lower-triangular basis matrix `P_W` putting `q` in column `0` and `e₁, e₂, e₃` in columns `1, 2, 3`. -/
def petersenPW (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     petersenQ w 1, 1, 0, 0;
     petersenQ w 2, 0, 1, 0;
     petersenQ w 3, 0, 0, 1]

def petersenPWinv (w : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     -petersenQ w 1, 1, 0, 0;
     -petersenQ w 2, 0, 1, 0;
     -petersenQ w 3, 0, 0, 1]

/-- The 3×3 nonsingular submatrix `B₁` obtained by deleting row 0 and column 0 of `B`. -/
def petersenB1 (w : Fin 14 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -w 13;
     -w 4, -w 7, 0;
     0, -w 5, -w 8]

/-- Explicit inverse `B₁⁻¹` of `petersenB1 w`. -/
def petersenB1inv (w : Fin 14 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(w 7 * w 8) / (w 4 * w 5 * w 13), -1 / w 4, w 7 / (w 4 * w 5);
     (w 8) / (w 5 * w 13), 0, -1 / w 5;
     -1 / w 13, 0, 0]

lemma petersenPU_mul_inv (w : Fin 14 → ℝ) : petersenPU w * petersenPUinv w = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [petersenPU, petersenPUinv, Matrix.mul_apply, Fin.sum_univ_four]

lemma petersenPW_mul_inv (w : Fin 14 → ℝ) : petersenPW w * petersenPWinv w = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [petersenPW, petersenPWinv, Matrix.mul_apply, Fin.sum_univ_four]

lemma petersenB1_mul_inv (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    petersenB1 w * petersenB1inv w = 1 := by
  have h4 : w 4 ≠ 0 := ne_of_gt (hw 4)
  have h5 : w 5 ≠ 0 := ne_of_gt (hw 5)
  have h13 : w 13 ≠ 0 := ne_of_gt (hw 13)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [petersenB1, petersenB1inv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp [h4, h5, h13] <;> ring

lemma petersenB1inv_mul (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    petersenB1inv w * petersenB1 w = 1 := by
  have h4 : w 4 ≠ 0 := ne_of_gt (hw 4)
  have h5 : w 5 ≠ 0 := ne_of_gt (hw 5)
  have h13 : w 13 ≠ 0 := ne_of_gt (hw 13)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [petersenB1, petersenB1inv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp [h4, h5, h13] <;> ring

lemma petersen_PU_B_PW (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k)
    (hdet : petersenDetB w = 0) :
    ∀ i j : Fin 4, ((petersenPU w)ᵀ * petersenB w * petersenPW w) i j =
      match i.val, j.val with
      | 0, _ => 0
      | _, 0 => 0
      | a + 1, b + 1 =>
        if ha : a < 3 then if hb : b < 3 then petersenB1 w ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0 := by
  have h2 : w 2 ≠ 0 := ne_of_gt (hw 2)
  have h4 : w 4 ≠ 0 := ne_of_gt (hw 4)
  have h5 : w 5 ≠ 0 := ne_of_gt (hw 5)
  have h7 : w 7 ≠ 0 := ne_of_gt (hw 7)
  have h11 : w 11 ≠ 0 := ne_of_gt (hw 11)
  have h13 : w 13 ≠ 0 := ne_of_gt (hw 13)
  have hdet' : w 1 * w 4 * w 5 * w 13 = w 2 * w 7 * w 8 * w 11 := by
    unfold petersenDetB at hdet; linarith
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [petersenPU, petersenPW, petersenP, petersenQ, petersenB, petersenB1,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    field_simp [h2, h4, h5, h7, h11, h13] <;> linarith

lemma petersen_qCq_neg (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0 < 0 := by
  have h1 : ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0 =
      -2 * w 12 * (w 1 * w 4 / (w 11 * w 7)) - 2 * w 6 * ((w 1 / w 11) * (w 2 / w 13)) := by
    simp [petersenPW, petersenQ, petersenC, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    ring
  rw [h1]
  have t1 : 0 < 2 * w 12 * (w 1 * w 4 / (w 11 * w 7)) := by
    have := hw 1; have := hw 4; have := hw 7; have := hw 11; have := hw 12; positivity
  have t2 : 0 < 2 * w 6 * ((w 1 / w 11) * (w 2 / w 13)) := by
    have := hw 1; have := hw 2; have := hw 6; have := hw 11; have := hw 13; positivity
  linarith

lemma petersen_alpha_beta (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    0 < ((petersenPU w)ᵀ * petersenRU w) 0 0 ∧ ((petersenPU w)ᵀ * petersenRU w) 0 1 < 0 := by
  have hα : ((petersenPU w)ᵀ * petersenRU w) 0 0 = w 1 * w 3 / w 2 + w 11 * w 9 / w 4 := by
    simp [petersenPU, petersenP, petersenRU, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    ring
  have hβ : ((petersenPU w)ᵀ * petersenRU w) 0 1 = -w 0 - w 10 * (w 11 * w 7 / (w 4 * w 5)) := by
    simp [petersenPU, petersenP, petersenRU, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    ring
  constructor
  · rw [hα]
    have := hw 1; have := hw 2; have := hw 3; have := hw 4; have := hw 9; have := hw 11
    positivity
  · rw [hβ]
    have := hw 0; have := hw 4; have := hw 5; have := hw 7; have := hw 10; have := hw 11
    have ht : 0 < w 10 * (w 11 * w 7 / (w 4 * w 5)) := by positivity
    linarith

/-- The 7×7 complementary interior block `A_int|_S` on `(Fin 3 ⊕ Fin 3) ⊕ Unit`
in the `(e₁..e₃; e₁..e₃; q)` basis of `S`. -/
def petersenC11 (w : Fin 14 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ((petersenPW w)ᵀ * petersenC w * petersenPW w) i.succ j.succ

def petersenC12 (w : Fin 14 → ℝ) : Matrix (Fin 3) Unit ℝ :=
  Matrix.of fun i _ => ((petersenPW w)ᵀ * petersenC w * petersenPW w) i.succ 0

def petersenK (w : Fin 14 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks 0 (petersenB1 w) (petersenB1 w)ᵀ (petersenC11 w)

def petersenKinv (w : Fin 14 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (-(petersenB1inv w)ᵀ * petersenC11 w * petersenB1inv w)
    (petersenB1inv w)ᵀ (petersenB1inv w) 0

def petersenL (w : Fin 14 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) Unit ℝ :=
  Matrix.of fun i _ => match i with
    | Sum.inl _ => 0
    | Sum.inr b => petersenC12 w b ()

def petersenQcqMat (w : Fin 14 → ℝ) : Matrix Unit Unit ℝ :=
  Matrix.of fun _ _ => ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0

def petersenAintS (w : Fin 14 → ℝ) : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ :=
  Matrix.fromBlocks (petersenK w) (petersenL w) (petersenL w)ᵀ (petersenQcqMat w)

lemma isHermitian_petersenC11 (w : Fin 14 → ℝ) : (petersenC11 w).IsHermitian := by
  have hPW := isHermitian_congr (petersenC w) (petersenPW w) (isHermitian_petersenC w)
  ext i j
  have h1 := congr_fun (congr_fun hPW.eq i.succ) j.succ
  simpa [petersenC11, Matrix.conjTranspose_apply] using h1

lemma petersenC11_transpose (w : Fin 14 → ℝ) : (petersenC11 w)ᵀ = petersenC11 w := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenC11 w).eq

lemma isHermitian_petersenK (w : Fin 14 → ℝ) : (petersenK w).IsHermitian := by
  change (petersenK w)ᴴ = petersenK w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [petersenK, Matrix.fromBlocks_transpose, petersenC11_transpose]

lemma isHermitian_petersenAintS (w : Fin 14 → ℝ) : (petersenAintS w).IsHermitian := by
  change (petersenAintS w)ᴴ = petersenAintS w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  have hKT : (petersenK w)ᵀ = petersenK w := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenK w).eq
  have hQT : (petersenQcqMat w)ᵀ = petersenQcqMat w := by
    ext ⟨⟩ ⟨⟩; rfl
  simp [petersenAintS, Matrix.fromBlocks_transpose, hKT, hQT]

lemma petersenK_mul_inv (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    petersenK w * petersenKinv w = 1 := by
  have h1 := petersenB1_mul_inv w hw
  have h2 : (petersenB1 w)ᵀ * (petersenB1inv w)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, petersenB1inv_mul w hw, Matrix.transpose_one]
  simp only [petersenK, petersenKinv, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, h1, h2, Matrix.one_mul, neg_add_cancel,
    Matrix.fromBlocks_one]

lemma signature_petersenK_eq_zero (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    signature (petersenK w) (isHermitian_petersenK w) = 0 := by
  let X : Matrix (Fin 3) (Fin 3) ℝ := -(1 / 2 : ℝ) • ((petersenB1inv w)ᵀ * petersenC11 w)
  let P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ := Matrix.fromBlocks 1 X 0 1
  let Q : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ := Matrix.fromBlocks 1 (-X) 0 1
  have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hP_det : IsUnit P.det :=
    isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
  have hBT_B1invT : (petersenB1 w)ᵀ * (petersenB1inv w)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, petersenB1inv_mul w hw, Matrix.transpose_one]
  have hB1inv_B1 : petersenB1inv w * petersenB1 w = 1 := petersenB1inv_mul w hw
  have hXT : Xᵀ = -(1 / 2 : ℝ) • (petersenC11 w * petersenB1inv w) := by
    simp [X, Matrix.transpose_smul, Matrix.transpose_mul, petersenC11_transpose]
  have hBT_X : (petersenB1 w)ᵀ * X = -(1 / 2 : ℝ) • petersenC11 w := by
    simp [X, Matrix.mul_smul, ← Matrix.mul_assoc, hBT_B1invT]
  have hXT_B : Xᵀ * petersenB1 w = -(1 / 2 : ℝ) • petersenC11 w := by
    simp [hXT, Matrix.smul_mul, Matrix.mul_assoc, hB1inv_B1]
  have hcongr : Pᵀ * petersenK w * P = Matrix.fromBlocks 0 (petersenB1 w) (petersenB1 w)ᵀ 0 := by
    simp only [P, petersenK, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    congr 1
    rw [hXT_B, hBT_X]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    ring
  have hOffH : (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℝ) (petersenB1 w) (petersenB1 w)ᵀ 0).IsHermitian := by
    change (Matrix.fromBlocks 0 (petersenB1 w) (petersenB1 w)ᵀ 0)ᴴ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [Matrix.fromBlocks_transpose]
  rw [← signature_congr (petersenK w) P (isHermitian_petersenK w) hP_det]
  have hEq : signature (Pᵀ * petersenK w * P) (isHermitian_congr _ P (isHermitian_petersenK w)) =
      signature (Matrix.fromBlocks 0 (petersenB1 w) (petersenB1 w)ᵀ 0) hOffH := by congr 1
  rw [hEq]
  exact signature_offdiag_block_zero (petersenB1 w) hOffH

/-- In Case 2, `A_int|_S` is congruent to `diag(K, qᵀ C q)`, hence invertible with `s(A_int|_S) = -1`. -/
lemma petersenAintS_sig_and_inv (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k) :
    signature (petersenAintS w) (isHermitian_petersenAintS w) = -1 ∧
    ∃ M : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ, petersenAintS w * M = 1 := by
  let S : Matrix (Fin 3 ⊕ Fin 3) Unit ℝ := petersenKinv w * petersenL w
  let P : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ := Matrix.fromBlocks 1 (-S) 0 1
  let Q : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ := Matrix.fromBlocks 1 S 0 1
  have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hP_det : IsUnit P.det :=
    isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
  have hKS : petersenK w * S = petersenL w := by
    simp [S, ← Matrix.mul_assoc, petersenK_mul_inv w hw]
  have hST_L : Sᵀ * petersenL w = 0 := by
    have hS_inr : ∀ b : Fin 3, S (Sum.inr b) () = 0 := by
      intro b
      simp [S, petersenKinv, petersenL, Matrix.mul_apply, Fintype.sum_sum_type]
    ext ⟨⟩ ⟨⟩
    simp [petersenL, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, hS_inr]
  have hKT : (petersenK w)ᵀ = petersenK w := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenK w).eq
  have hST_K : Sᵀ * petersenK w = (petersenL w)ᵀ := by
    calc Sᵀ * petersenK w = Sᵀ * (petersenK w)ᵀ := by rw [hKT]
      _ = (petersenK w * S)ᵀ := (Matrix.transpose_mul _ _).symm
      _ = (petersenL w)ᵀ := by rw [hKS]
  have hcongr : Pᵀ * petersenAintS w * P = Matrix.fromBlocks (petersenK w) 0 0 (petersenQcqMat w) := by
    simp only [P, petersenAintS, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_zero, Matrix.transpose_neg, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    congr 1
    · rw [hKS, neg_add_cancel]
    · rw [hST_K, neg_add_cancel]
    · rw [hST_K, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, hST_L, neg_zero, zero_add]
  have hQcq_H : (petersenQcqMat w).IsHermitian := by
    ext ⟨⟩ ⟨⟩; simp [petersenQcqMat, Matrix.conjTranspose_apply]
  have hQcq_neg : ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0 < 0 := petersen_qCq_neg w hw
  have hQcq_sig : signature (petersenQcqMat w) hQcq_H = -1 := by
    have hpos0 : posInertia (petersenQcqMat w) hQcq_H = 0 := by
      rw [posInertia_eq_sSup]
      apply le_antisymm
      · refine csSup_le ⟨0, ⟨⊥, rfl, by intro v hv hv0; exact absurd (Submodule.mem_bot.mp hv) hv0⟩⟩ ?_
        rintro n ⟨W, rfl, hW⟩
        by_contra hpos
        have hWne : W ≠ ⊥ := by
          intro hbot; rw [hbot, finrank_bot] at hpos; omega
        obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
        have hgt := hW v hvW hv0
        have hv_ne : v () ≠ 0 := fun h => hv0 (funext fun ⟨⟩ => h)
        have hq : dotProduct v (petersenQcqMat w *ᵥ v) =
            ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0 * (v ()) ^ 2 := by
          simp [dotProduct, Matrix.mulVec, petersenQcqMat]; ring
        rw [hq] at hgt
        nlinarith [sq_pos_of_ne_zero hv_ne]
      · exact Nat.zero_le _
    have hneg1 : 1 ≤ negInertia (petersenQcqMat w) hQcq_H := by
      rw [negInertia_eq_sSup]
      refine le_csSup ⟨1, by rintro n ⟨W, rfl, _⟩; simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W⟩ ?_
      refine ⟨⊤, by simp [Module.finrank_fintype_fun_eq_card], ?_⟩
      intro v _ hv0
      have hv_ne : v () ≠ 0 := fun h => hv0 (funext fun ⟨⟩ => h)
      have hq : dotProduct v (petersenQcqMat w *ᵥ v) =
          ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0 * (v ()) ^ 2 := by
        simp [dotProduct, Matrix.mulVec, petersenQcqMat]; ring
      rw [hq]
      nlinarith [sq_pos_of_ne_zero hv_ne]
    have hsum := inertia_sum (petersenQcqMat w) hQcq_H
    simp only [Fintype.card_unique] at hsum
    simp only [signature]
    omega
  constructor
  · rw [← signature_congr (petersenAintS w) P (isHermitian_petersenAintS w) hP_det]
    have hEq : signature (Pᵀ * petersenAintS w * P) (isHermitian_congr _ P (isHermitian_petersenAintS w)) =
        signature (Matrix.fromBlocks (petersenK w) 0 0 (petersenQcqMat w))
          (isHermitian_fromBlocks _ (isHermitian_petersenK w) _ hQcq_H) := by congr 1
    rw [hEq, signature_fromBlocks, signature_petersenK_eq_zero w hw, hQcq_sig]
    omega
  · let qVal := ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0
    have hq_ne : qVal ≠ 0 := ne_of_lt hQcq_neg
    let Dinv : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ :=
      Matrix.fromBlocks (petersenKinv w) 0 0 (Matrix.of fun _ _ => qVal⁻¹)
    have hD_mul : Matrix.fromBlocks (petersenK w) 0 0 (petersenQcqMat w) * Dinv = 1 := by
      have hQ1 : petersenQcqMat w * Matrix.of (fun _ _ : Unit => qVal⁻¹) = 1 := by
        ext ⟨⟩ ⟨⟩
        simp [petersenQcqMat, qVal, Matrix.mul_apply, mul_inv_cancel₀ hq_ne]
      simp [Dinv, Matrix.fromBlocks_multiply, petersenK_mul_inv w hw, hQ1, Matrix.fromBlocks_one]
    have hQT_PT : Qᵀ * Pᵀ = 1 := by
      rw [← Matrix.transpose_mul, show P * Q = 1 from hPQ, Matrix.transpose_one]
    refine ⟨P * Dinv * Pᵀ, ?_⟩
    calc petersenAintS w * (P * Dinv * Pᵀ)
        = Qᵀ * (Pᵀ * petersenAintS w * P) * Dinv * Pᵀ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Qᵀ Pᵀ, hQT_PT, Matrix.one_mul]
      _ = Qᵀ * (Matrix.fromBlocks (petersenK w) 0 0 (petersenQcqMat w) * Dinv) * Pᵀ := by
          rw [hcongr, Matrix.mul_assoc Qᵀ]
      _ = Qᵀ * Pᵀ := by rw [hD_mul, Matrix.mul_one]
      _ = 1 := hQT_PT

end SignedGraphs
