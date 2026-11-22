import SignedGraphs.LinearAlgebraExtra

/-!
# Explicit Matrix Algebra for Weighted Petersen Graphs (Lemma 5.2)

Contains the explicit finite-dimensional matrix factorizations, inverses, and sign
computations for the 8×8 Petersen interior `A_int = [[0, B], [Bᵀ, C]]` in both
Case 1 (`det B ≠ 0`) and Case 2 (`det B = 0`).
-/

open Matrix

namespace SignedGraphs

noncomputable section

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
  have h21 : (petersenB w)ᵀ * (-(petersenBinv w)ᵀ * petersenC w * petersenBinv w) +
      petersenC w * petersenBinv w = 0 := by
    calc (petersenB w)ᵀ * (-(petersenBinv w)ᵀ * petersenC w * petersenBinv w) + petersenC w * petersenBinv w
        = -(((petersenB w)ᵀ * (petersenBinv w)ᵀ) * petersenC w * petersenBinv w) + petersenC w * petersenBinv w := by
          simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
      _ = -(petersenC w * petersenBinv w) + petersenC w * petersenBinv w := by
          rw [h2, Matrix.one_mul]
      _ = 0 := neg_add_cancel _
  simp only [petersenAint, petersenAintInv, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, h1, h2, h21, Matrix.fromBlocks_one]

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
  rw [hneg_eq, signature_neg (Matrix.fromBlocks 0 M Mᵀ 0) hH] at hs
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
  have hmid : (petersenR w)ᵀ * petersenAintInv w * petersenR w =
      (petersenRU w)ᵀ * (-(petersenBinv w)ᵀ * petersenC w * petersenBinv w) * petersenRU w := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
      petersenR, Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      petersenAintInv, Matrix.fromBlocks_apply₁₁]
  rw [hmid]
  simp only [petersenMH, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.transpose_mul,
    Matrix.mul_assoc]

lemma isHermitian_petersenMH (w : Fin 14 → ℝ) : (petersenMH w).IsHermitian := by
  change (petersenMH w)ᴴ = petersenMH w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [petersenMH, Matrix.transpose_mul, petersenC_transpose, Matrix.mul_assoc]

set_option maxHeartbeats 600000 in
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
  have hw0 := hw 0; have hw1 := hw 1; have hw2 := hw 2; have hw3 := hw 3
  have hw4 := hw 4; have hw5 := hw 5; have hw7 := hw 7; have hw8 := hw 8
  have hw9 := hw 9; have hw10 := hw 10; have hw11 := hw 11; have hw13 := hw 13
  have hA : 0 < w 13 * w 5 * w 9 + w 3 * w 7 * w 8 := by positivity
  have hB : 0 < w 1 * w 3 * w 4 + w 11 * w 2 * w 9 := by positivity
  have hC : 0 < w 0 * w 4 * w 5 + w 10 * w 11 * w 7 := by positivity
  have hD : 0 < w 0 * w 2 * w 8 + w 1 * w 10 * w 13 := by positivity
  have hV00_neg : V 0 0 < 0 := by rw [hv00]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw11) hA
  have hV10_pos : 0 < V 1 0 := by rw [hv10]; exact mul_pos hw1 hA
  have hV20_neg : V 2 0 < 0 := by rw [hv20]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw8) hB
  have hV30_pos : 0 < V 3 0 := by rw [hv30]; exact mul_pos hw5 hB
  have hV01_pos : 0 < V 0 1 := by rw [hv01]; exact mul_pos hw13 hC
  have hV11_neg : V 1 1 < 0 := by rw [hv11]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw7) hD
  have hV21_pos : 0 < V 2 1 := by rw [hv21]; exact mul_pos hw4 hD
  have hV31_neg : V 3 1 < 0 := by rw [hv31]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw2) hC
  have hinv_pos : 0 < ((petersenDetB w) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hdet)
  have hquad : ∀ i j : Fin 2, (Vᵀ * petersenC w * V) i j =
      -w 12 * (V 0 i * V 2 j + V 2 i * V 0 j) - w 6 * (V 1 i * V 3 j + V 3 i * V 1 j) := by
    intro i j
    simp [petersenC, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
    ring
  have hw6 := hw 6; have hw12 := hw 12
  refine ⟨?_, ?_, ?_, hsym⟩
  · rw [hMH_eq 0 0, hquad 0 0]
    have h1 : 0 < V 0 0 * V 2 0 := mul_pos_of_neg_of_neg hV00_neg hV20_neg
    have h2 : 0 < V 1 0 * V 3 0 := mul_pos hV10_pos hV30_pos
    have h1b : 0 < V 0 0 * V 2 0 + V 2 0 * V 0 0 := by linarith [mul_comm (V 0 0) (V 2 0)]
    have h2b : 0 < V 1 0 * V 3 0 + V 3 0 * V 1 0 := by linarith [mul_comm (V 1 0) (V 3 0)]
    have ht1 : -w 12 * (V 0 0 * V 2 0 + V 2 0 * V 0 0) < 0 := mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw12) h1b
    have ht2 : 0 < w 6 * (V 1 0 * V 3 0 + V 3 0 * V 1 0) := mul_pos hw6 h2b
    exact mul_neg_of_pos_of_neg hinv_pos (by linarith)
  · rw [hMH_eq 1 1, hquad 1 1]
    have h1 : 0 < V 0 1 * V 2 1 := mul_pos hV01_pos hV21_pos
    have h2 : 0 < V 1 1 * V 3 1 := mul_pos_of_neg_of_neg hV11_neg hV31_neg
    have h1b : 0 < V 0 1 * V 2 1 + V 2 1 * V 0 1 := by linarith [mul_comm (V 0 1) (V 2 1)]
    have h2b : 0 < V 1 1 * V 3 1 + V 3 1 * V 1 1 := by linarith [mul_comm (V 1 1) (V 3 1)]
    have ht1 : -w 12 * (V 0 1 * V 2 1 + V 2 1 * V 0 1) < 0 := mul_neg_of_neg_of_pos (neg_lt_zero.mpr hw12) h1b
    have ht2 : 0 < w 6 * (V 1 1 * V 3 1 + V 3 1 * V 1 1) := mul_pos hw6 h2b
    exact mul_neg_of_pos_of_neg hinv_pos (by linarith)
  · rw [hMH_eq 0 1, hquad 0 1]
    have h1 : V 0 0 * V 2 1 < 0 := mul_neg_of_neg_of_pos hV00_neg hV21_pos
    have h2 : V 2 0 * V 0 1 < 0 := mul_neg_of_neg_of_pos hV20_neg hV01_pos
    have h3 : V 1 0 * V 3 1 < 0 := mul_neg_of_pos_of_neg hV10_pos hV31_neg
    have h4 : V 3 0 * V 1 1 < 0 := mul_neg_of_pos_of_neg hV30_pos hV11_neg
    have ht1 : 0 < -w 12 * (V 0 0 * V 2 1 + V 2 0 * V 0 1) := mul_pos_of_neg_of_neg (neg_lt_zero.mpr hw12) (by linarith)
    have ht2 : w 6 * (V 1 0 * V 3 1 + V 3 0 * V 1 1) < 0 := mul_neg_of_pos_of_neg hw6 (by linarith)
    exact mul_pos hinv_pos (by linarith)

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
  have h21 : (petersenB1 w)ᵀ * (-(petersenB1inv w)ᵀ * petersenC11 w * petersenB1inv w) +
      petersenC11 w * petersenB1inv w = 0 := by
    calc (petersenB1 w)ᵀ * (-(petersenB1inv w)ᵀ * petersenC11 w * petersenB1inv w) + petersenC11 w * petersenB1inv w
        = -(((petersenB1 w)ᵀ * (petersenB1inv w)ᵀ) * petersenC11 w * petersenB1inv w) + petersenC11 w * petersenB1inv w := by
          simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
      _ = -(petersenC11 w * petersenB1inv w) + petersenC11 w * petersenB1inv w := by
          rw [h2, Matrix.one_mul]
      _ = 0 := neg_add_cancel _
  simp only [petersenK, petersenKinv, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, h1, h2, h21, Matrix.fromBlocks_one]

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
      · refine csSup_le ⟨0, ⟨⊥, finrank_bot ℝ _, by intro v hv hv0; exact absurd (by simpa using hv) hv0⟩⟩ ?_
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
    rw [hEq, signature_fromBlocks (petersenK w) (isHermitian_petersenK w) (petersenQcqMat w) hQcq_H, signature_petersenK_eq_zero w hw, hQcq_sig]
    omega
  · let qVal := ((petersenPW w)ᵀ * petersenC w * petersenPW w) 0 0
    have hq_ne : qVal ≠ 0 := ne_of_lt hQcq_neg
    let Dinv : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ :=
      Matrix.fromBlocks (petersenKinv w) 0 0 (Matrix.of fun _ _ => qVal⁻¹)
    have hD_mul : Matrix.fromBlocks (petersenK w) 0 0 (petersenQcqMat w) * Dinv = 1 := by
      have hQ1 : petersenQcqMat w * Matrix.of (fun _ _ : Unit => qVal⁻¹) = 1 := by
        ext ⟨⟩ ⟨⟩
        simp only [petersenQcqMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
          Finset.univ_unique, Finset.sum_singleton]
        exact mul_inv_cancel₀ hq_ne
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


/-- Any 2×2 real symmetric matrix with a strictly negative `(0, 0)` entry has `signature ≤ 0`. -/
lemma signature_two_by_two_neg_diag (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian)
    (h00 : M 0 0 < 0) : signature M hM ≤ 0 := by
  have hneg : 1 ≤ negInertia M hM := by
    rw [negInertia_eq_sSup]
    refine le_csSup ⟨2, by rintro n ⟨W, rfl, _⟩; simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W⟩ ?_
    let f : ℝ →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun r i => if i = 0 then r else 0
        map_add' := fun r₁ r₂ => by ext i; fin_cases i <;> simp
        map_smul' := fun c r => by ext i; fin_cases i <;> simp }
    have hf_inj : Function.Injective f := by
      intro r₁ r₂ h
      simpa [f] using congrFun h 0
    refine ⟨LinearMap.range f, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hf_inj, Module.finrank_self]
    · intro v hv hv0
      rcases hv with ⟨r, rfl⟩
      have hr : r ≠ 0 := fun h => hv0 (by ext i; simp [f, h])
      have hq : dotProduct (f r) (M *ᵥ f r) = M 0 0 * r ^ 2 := by
        simp [f, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      rw [hq]
      nlinarith [sq_pos_of_ne_zero hr]
  have hsum := inertia_sum M hM
  rw [Fintype.card_fin] at hsum
  simp only [signature]
  omega

private lemma signature_congr_eq_pa {W : Type*} [Fintype W] [DecidableEq W]
    {M₁ M₂ : Matrix W W ℝ} (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) :
    signature M₁ h₁ = signature M₂ h₂ := by
  subst h; rfl

set_option maxHeartbeats 800000 in
/-- Unified block-matrix signature bound for weighted `(Petersen - xy, -1)` graphs (Lemma 5.2):
handles both Case 1 (`det B ≠ 0`) and Case 2 (`det B = 0`). -/
theorem petersen_block_signature_nonpos
    {U : Type} [Fintype U] [DecidableEq U]
    (w : Fin 14 → ℝ) (hw : ∀ k : Fin 14, 0 < w k)
    (G₂ : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ) (hG₂ : G₂.IsHermitian)
    (hG₂_00 : G₂ (Sum.inl 0) (Sum.inl 0) = 0)
    (B : Matrix ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ℝ)
    (hB : B.IsHermitian)
    (hB_eq : B = Matrix.fromBlocks (petersenAint w)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)ᵀ
      G₂)
    (hcase1 : petersenDetB w ≠ 0 →
      signature (G₂ + Matrix.fromBlocks (petersenMH w) (0 : Matrix (Fin 2) U ℝ) 0 0)
        (hG₂.add (isHermitian_fromBlocks (petersenMH w) (isHermitian_petersenMH w)
          (0 : Matrix U U ℝ) isHermitian_zero)) ≤ 0)
    (hcase2 : signature (G₂.submatrix Sum.inr Sum.inr)
      (isHermitian_submatrix G₂ hG₂ Sum.inr) ≤ 0) :
    signature B hB ≤ 0 := by
  classical
  let Rfull : Matrix (Fin 4 ⊕ Fin 4) (Fin 2 ⊕ U) ℝ :=
    Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0
  by_cases hdet : petersenDetB w ≠ 0
  · -- Case 1: det(B) ≠ 0
    let S : Matrix (Fin 4 ⊕ Fin 4) (Fin 2 ⊕ U) ℝ := petersenAintInv w * Rfull
    let P : Matrix ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ℝ :=
      Matrix.fromBlocks 1 (-S) 0 1
    let Q : Matrix ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ℝ :=
      Matrix.fromBlocks 1 S 0 1
    have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hP_det : IsUnit P.det :=
      isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
    have hAintS : petersenAint w * S = Rfull := by
      simp [S, ← Matrix.mul_assoc, petersenAint_mul_AintInv w hdet]
    have hAintT : (petersenAint w)ᵀ = petersenAint w := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenAint w).eq
    have hST_Aint : Sᵀ * petersenAint w = Rfullᵀ := by
      calc Sᵀ * petersenAint w = Sᵀ * (petersenAint w)ᵀ := by rw [hAintT]
        _ = (petersenAint w * S)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = Rfullᵀ := by rw [hAintS]
    have hSR_eq : -(Sᵀ * Rfull) = Matrix.fromBlocks (petersenMH w) (0 : Matrix (Fin 2) U ℝ) 0 0 := by
      rw [← petersen_schur_eq_MH w]
      have hAintInvT : (petersenAintInv w)ᵀ = petersenAintInv w := by
        have hC := petersenC_transpose w
        simp [petersenAintInv, Matrix.fromBlocks_transpose, Matrix.transpose_mul, hC, Matrix.mul_assoc]
      have hST_R : Sᵀ * Rfull = Rfullᵀ * petersenAintInv w * Rfull := by
        simp [S, Matrix.transpose_mul, hAintInvT, Matrix.mul_assoc]
      rw [hST_R]
      ext a b
      rcases a with i | u <;> rcases b with j | v
      · simp [Rfull, Matrix.mul_apply, Matrix.transpose_apply]
      · simp [Rfull, Matrix.mul_apply, Matrix.transpose_apply]
      · simp [Rfull, Matrix.mul_apply, Matrix.transpose_apply]
      · simp [Rfull, Matrix.mul_apply, Matrix.transpose_apply]
    let Mschur : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ :=
      G₂ + Matrix.fromBlocks (petersenMH w) (0 : Matrix (Fin 2) U ℝ) 0 0
    have hMschur_H : Mschur.IsHermitian :=
      hG₂.add (isHermitian_fromBlocks (petersenMH w) (isHermitian_petersenMH w)
        (0 : Matrix U U ℝ) isHermitian_zero)
    have hcongr : Pᵀ * B * P = Matrix.fromBlocks (petersenAint w) 0 0 Mschur := by
      rw [hB_eq]
      change Pᵀ * Matrix.fromBlocks (petersenAint w) Rfull Rfullᵀ G₂ * P = _
      simp only [P, Mschur, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
        Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      congr 1
      · rw [hAintS, neg_add_cancel]
      · rw [hST_Aint, neg_add_cancel]
      · rw [hST_Aint, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, ← hSR_eq, add_comm]
    rw [← signature_congr B P hB hP_det,
      signature_congr_eq_pa (isHermitian_congr B P hB)
        (isHermitian_fromBlocks _ (isHermitian_petersenAint w) _ hMschur_H) hcongr,
      signature_fromBlocks _ (isHermitian_petersenAint w) _ hMschur_H,
      signature_petersenAint_eq_zero w hdet, zero_add]
    exact hcase1 hdet
  · -- Case 2: det(B) = 0
    push Not at hdet
    let P_int : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
      Matrix.fromBlocks (petersenPU w) 0 0 (petersenPW w)
    let Q_int : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
      Matrix.fromBlocks (petersenPUinv w) 0 0 (petersenPWinv w)
    have hPQ_int : P_int * Q_int = 1 := by
      simp [P_int, Q_int, Matrix.fromBlocks_multiply, petersenPU_mul_inv, petersenPW_mul_inv,
        Matrix.fromBlocks_one]
    let α : ℝ := ((petersenPU w)ᵀ * petersenRU w) 0 0
    let β : ℝ := ((petersenPU w)ᵀ * petersenRU w) 0 1
    have hαβ := petersen_alpha_beta w hw
    have hα_pos : 0 < α := hαβ.1
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, -β; 0, α]
    let Zinv : Matrix (Fin 2) (Fin 2) ℝ := !![1, β / α; 0, 1 / α]
    have hZZinv : Z * Zinv = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Z, Zinv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hα_ne] <;> ring
    let P_ext : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ := Matrix.fromBlocks Z 0 0 1
    let Q_ext : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ := Matrix.fromBlocks Zinv 0 0 1
    have hPQ_ext : P_ext * Q_ext = 1 := by
      simp [P_ext, Q_ext, Matrix.fromBlocks_multiply, hZZinv, Matrix.fromBlocks_one]
    let P₀ : Matrix ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ℝ :=
      Matrix.fromBlocks P_int 0 0 P_ext
    let Q₀ : Matrix ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ((Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U)) ℝ :=
      Matrix.fromBlocks Q_int 0 0 Q_ext
    have hPQ₀ : P₀ * Q₀ = 1 := by
      simp [P₀, Q₀, Matrix.fromBlocks_multiply, hPQ_int, hPQ_ext, Matrix.fromBlocks_one]
    have hP₀_det : IsUnit P₀.det :=
      isUnit_iff_exists_inv.mpr ⟨Q₀.det, by rw [← Matrix.det_mul, hPQ₀, Matrix.det_one]⟩
    let B₂ := P₀ᵀ * B * P₀
    have hB₂ : B₂.IsHermitian := isHermitian_congr B P₀ hB
    rw [← signature_congr B P₀ hB hP₀_det]
    change signature B₂ hB₂ ≤ 0
    have hB₂_blk : B₂ = Matrix.fromBlocks (P_intᵀ * petersenAint w * P_int)
        (P_intᵀ * Rfull * P_ext) (P_extᵀ * Rfullᵀ * P_int) (P_extᵀ * G₂ * P_ext) := by
      dsimp only [B₂]; rw [hB_eq]
      change P₀ᵀ * Matrix.fromBlocks (petersenAint w) Rfull Rfullᵀ G₂ * P₀ = _
      simp [P₀, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
    have hAint_tr : P_intᵀ * petersenAint w * P_int =
        Matrix.fromBlocks 0 ((petersenPU w)ᵀ * petersenB w * petersenPW w)
          ((petersenPW w)ᵀ * (petersenB w)ᵀ * petersenPU w)
          ((petersenPW w)ᵀ * petersenC w * petersenPW w) := by
      simp [P_int, petersenAint, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
        Matrix.mul_assoc]
    have hB₂_sym : ∀ p q, B₂ p q = B₂ q p := fun p q => by
      simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB₂.eq p) q).symm
    have hPU_B_PW := petersen_PU_B_PW w hw hdet
    -- Reindex to Fin 2 ⊕ (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U))
    -- Fin 2: 0 ↦ p̃ = inl (inl 0), 1 ↦ z₁ = inr (inl 0)
    -- S = (Fin 3 ⊕ Fin 3) ⊕ Unit:
    --   inl (inl i) ↦ inl (inl i.succ), inl (inr j) ↦ inl (inr j.succ), inr () ↦ inl (inr 0)
    -- Rem = Unit ⊕ U:
    --   inl () ↦ inr (inl 1), inr u ↦ inr (inr u)
    let e : Fin 2 ⊕ (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ≃ (Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U) :=
      { toFun := fun
          | Sum.inl 0 => Sum.inl (Sum.inl 0)
          | Sum.inl 1 => Sum.inr (Sum.inl 0)
          | Sum.inr (Sum.inl (Sum.inl (Sum.inl i))) => Sum.inl (Sum.inl i.succ)
          | Sum.inr (Sum.inl (Sum.inl (Sum.inr j))) => Sum.inl (Sum.inr j.succ)
          | Sum.inr (Sum.inl (Sum.inr ())) => Sum.inl (Sum.inr 0)
          | Sum.inr (Sum.inr (Sum.inl ())) => Sum.inr (Sum.inl 1)
          | Sum.inr (Sum.inr (Sum.inr u)) => Sum.inr (Sum.inr u)
        invFun := fun
          | Sum.inl (Sum.inl i) =>
            if h : i = 0 then Sum.inl 0
            else Sum.inr (Sum.inl (Sum.inl (Sum.inl (i.pred h))))
          | Sum.inl (Sum.inr j) =>
            if h : j = 0 then Sum.inr (Sum.inl (Sum.inr ()))
            else Sum.inr (Sum.inl (Sum.inl (Sum.inr (j.pred h))))
          | Sum.inr (Sum.inl 0) => Sum.inl 1
          | Sum.inr (Sum.inl 1) => Sum.inr (Sum.inr (Sum.inl ()))
          | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr (Sum.inr u))
        left_inv := fun x => by
          rcases x with i | ((i | j) | ⟨⟩) | (⟨⟩ | u)
          · fin_cases i <;> rfl
          · simp [Fin.succ_ne_zero, Fin.pred_succ]
          · simp [Fin.succ_ne_zero, Fin.pred_succ]
          · rfl
          · rfl
          · rfl
        right_inv := fun x => by
          rcases x with (i | j) | (k | u)
          · by_cases h : i = 0
            · subst h; rfl
            · simp [h, Fin.succ_pred]
          · by_cases h : j = 0
            · subst h; rfl
            · simp [h, Fin.succ_pred]
          · fin_cases k <;> rfl
          · rfl }
    let B₃ := B₂.submatrix e e
    have hB₃ : B₃.IsHermitian := isHermitian_submatrix B₂ hB₂ e
    rw [← signature_reindex e B₂ hB₂]
    change signature B₃ hB₃ ≤ 0
    -- Compute key entries of B₂ for row p̃ = Sum.inl (Sum.inl 0)
    have hRfull_tr : ∀ (a : Fin 4) (j : Fin 2),
        (P_intᵀ * Rfull * P_ext) (Sum.inl a) (Sum.inl j) =
          (((petersenPU w)ᵀ * petersenRU w) * Z) a j := by
      intro a j
      simp only [P_int, P_ext, Rfull, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.mul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type,
        Matrix.of_apply, petersenR, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hRfull_tr_U : ∀ (p : Fin 4 ⊕ Fin 4) (u : U),
        (P_intᵀ * Rfull * P_ext) p (Sum.inr u) = 0 := by
      intro p u
      simp only [P_int, P_ext, Rfull, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.mul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type,
        Matrix.of_apply, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hB₃_00 : B₃ (Sum.inl 0) (Sum.inl 0) = 0 := by
      simp [B₃, e, hB₂_blk, hAint_tr]
    have hB₃_01 : B₃ (Sum.inl 0) (Sum.inl 1) = α := by
      simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
        Matrix.fromBlocks_apply₁₂, hRfull_tr]
      simp [Z, α, β, Matrix.mul_apply, Fin.sum_univ_two]
    have hB₃_11 : B₃ (Sum.inl 1) (Sum.inl 1) = 0 := by
      simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
        Matrix.fromBlocks_apply₂₂, P_ext, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.transpose_one, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      simp [Z, Matrix.transpose_apply, Fin.sum_univ_two, hG₂_00]
    have hB₃_0_inr : ∀ q : ((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U),
        B₃ (Sum.inl 0) (Sum.inr q) = 0 := by
      intro q
      rcases q with ((i | j) | ⟨⟩) | (⟨⟩ | u)
      · simp [B₃, e, hB₂_blk, hAint_tr]
      · simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
          Matrix.fromBlocks_apply₁₁, hAint_tr, Matrix.fromBlocks_apply₁₂]
        exact hPU_B_PW 0 j.succ
      · simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
          Matrix.fromBlocks_apply₁₁, hAint_tr, Matrix.fromBlocks_apply₁₂]
        exact hPU_B_PW 0 0
      · simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
          Matrix.fromBlocks_apply₁₂, hRfull_tr]
        simp [Z, α, β, Matrix.mul_apply, Fin.sum_univ_two]; ring
      · simp only [B₃, Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk,
          Matrix.fromBlocks_apply₁₂]
        exact hRfull_tr_U (Sum.inl 0) u
    -- Step 4: Decouple the top-left 2×2 block H = !![0, α; α, 0]
    let H₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, α; α, 0]
    let R_H : Matrix (Fin 2) (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ℝ := B₃.toBlocks₁₂
    let B_tail : Matrix (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U))
        (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ℝ := B₃.toBlocks₂₂
    have hB₃_sym : ∀ p q, B₃ p q = B₃ q p := fun p q => by
      simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB₃.eq p) q).symm
    have hB₃_eq : B₃ = Matrix.fromBlocks H₂ R_H R_Hᵀ B_tail := by
      ext p q
      rcases p with i | a <;> rcases q with j | b
      · fin_cases i <;> fin_cases j <;>
          simp [H₂, hB₃_00, hB₃_01, hB₃_11, hB₃_sym (Sum.inl 1) (Sum.inl 0)]
      · rfl
      · simp [R_H, Matrix.toBlocks₁₂, hB₃_sym]
      · rfl
    let S_H : Matrix (Fin 2) (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ℝ :=
      Matrix.of fun i q => match i with
        | 0 => R_H 1 q / α
        | 1 => 0
    let P_H := Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) (-S_H) 0
      (1 : Matrix (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ℝ)
    let Q_H := Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) S_H 0
      (1 : Matrix (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) (((Fin 3 ⊕ Fin 3) ⊕ Unit) ⊕ (Unit ⊕ U)) ℝ)
    have hPQ_H : P_H * Q_H = 1 := by simp [P_H, Q_H, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hP_H_det : IsUnit P_H.det :=
      isUnit_iff_exists_inv.mpr ⟨Q_H.det, by rw [← Matrix.det_mul, hPQ_H, Matrix.det_one]⟩
    have hH₂_S : H₂ * S_H = R_H := by
      ext i q
      fin_cases i
      · simp [H₂, S_H, R_H, Matrix.toBlocks₁₂, Matrix.mul_apply, Fin.sum_univ_two, hB₃_0_inr q]
      · simp [H₂, S_H, Matrix.mul_apply, Fin.sum_univ_two, mul_div_cancel₀ _ hα_ne]
    have hSH_R : S_Hᵀ * R_H = 0 := by
      ext p q
      simp [S_H, R_H, Matrix.toBlocks₁₂, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, hB₃_0_inr q]
    have hH₂_H : H₂.IsHermitian := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [H₂, Matrix.conjTranspose_apply]
    have hH₂_T : H₂ᵀ = H₂ := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hH₂_H.eq
    have hSH_H₂ : S_Hᵀ * H₂ = R_Hᵀ := by
      calc S_Hᵀ * H₂ = S_Hᵀ * H₂ᵀ := by rw [hH₂_T]
        _ = (H₂ * S_H)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = R_Hᵀ := by rw [hH₂_S]
    have hB_tail_H : B_tail.IsHermitian := isHermitian_submatrix B₃ hB₃ Sum.inr
    have hcongr_H : P_Hᵀ * B₃ * P_H = Matrix.fromBlocks H₂ 0 0 B_tail := by
      rw [hB₃_eq]
      simp only [P_H, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
        Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      congr 1
      · rw [hH₂_S, neg_add_cancel]
      · rw [hSH_H₂, neg_add_cancel]
      · rw [hSH_H₂, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, hSH_R, neg_zero, zero_add]
    rw [← signature_congr B₃ P_H hB₃ hP_H_det,
      signature_congr_eq_pa (isHermitian_congr B₃ P_H hB₃)
        (isHermitian_fromBlocks H₂ hH₂_H B_tail hB_tail_H) hcongr_H,
      signature_fromBlocks H₂ hH₂_H B_tail hB_tail_H,
      signature_two_by_two_offdiag α 0 hα_ne hH₂_H, zero_add]
    -- Step 5: Decouple S = (Fin 3 ⊕ Fin 3) ⊕ Unit with block petersenAintS w
    have hB_tail_11 : B_tail.toBlocks₁₁ = petersenAintS w := by
      ext s₁ s₂
      rcases s₁ with (i | j) | ⟨⟩ <;> rcases s₂ with (i' | j') | ⟨⟩
      · simp [B_tail, B₃, e, hB₂_blk, hAint_tr, petersenAintS, petersenK]
      · simp only [B_tail, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, B₃,
          Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk, Matrix.fromBlocks_apply₁₁,
          hAint_tr, Matrix.fromBlocks_apply₁₂, petersenAintS, petersenK]
        simpa [Fin.val_succ, i.isLt, j'.isLt] using hPU_B_PW i.succ j'.succ
      · simp only [B_tail, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, B₃,
          Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk, Matrix.fromBlocks_apply₁₁,
          hAint_tr, Matrix.fromBlocks_apply₁₂, petersenAintS, petersenL]
        exact hPU_B_PW i.succ 0
      · simp only [B_tail, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, B₃,
          Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk, Matrix.fromBlocks_apply₁₁,
          hAint_tr, Matrix.fromBlocks_apply₂₁, petersenAintS, petersenK, Matrix.transpose_apply]
        have h1 : ((petersenPW w)ᵀ * (petersenB w)ᵀ * petersenPU w) j.succ i'.succ =
            ((petersenPU w)ᵀ * petersenB w * petersenPW w) i'.succ j.succ := by
          have hT : ((petersenPU w)ᵀ * petersenB w * petersenPW w)ᵀ =
              (petersenPW w)ᵀ * (petersenB w)ᵀ * petersenPU w := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
          rw [← hT]; rfl
        rw [h1]
        simpa [Fin.val_succ, i'.isLt, j.isLt] using hPU_B_PW i'.succ j.succ
      · simp [B_tail, B₃, e, hB₂_blk, hAint_tr, petersenAintS, petersenK, petersenC11]
      · simp [B_tail, B₃, e, hB₂_blk, hAint_tr, petersenAintS, petersenL, petersenC12]
      · simp only [B_tail, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, B₃,
          Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk, Matrix.fromBlocks_apply₁₁,
          hAint_tr, Matrix.fromBlocks_apply₂₁, petersenAintS, petersenL, Matrix.transpose_apply]
        have h1 : ((petersenPW w)ᵀ * (petersenB w)ᵀ * petersenPU w) 0 i'.succ =
            ((petersenPU w)ᵀ * petersenB w * petersenPW w) i'.succ 0 := by
          have hT : ((petersenPU w)ᵀ * petersenB w * petersenPW w)ᵀ =
              (petersenPW w)ᵀ * (petersenB w)ᵀ * petersenPU w := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
          rw [← hT]; rfl
        rw [h1]
        exact hPU_B_PW i'.succ 0
      · simp only [B_tail, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, B₃,
          Matrix.submatrix_apply, e, Equiv.coe_fn_mk, hB₂_blk, Matrix.fromBlocks_apply₁₁,
          hAint_tr, Matrix.fromBlocks_apply₂₂, petersenAintS, petersenL, petersenC12,
          Matrix.transpose_apply]
        have hPW := isHermitian_congr (petersenC w) (petersenPW w) (isHermitian_petersenC w)
        simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hPW.eq j'.succ) 0)
      · simp [B_tail, B₃, e, hB₂_blk, hAint_tr, petersenAintS, petersenQcqMat]
    have hB_tail_12_U : ∀ s (u : U), B_tail.toBlocks₁₂ s (Sum.inr u) = 0 := by
      intro s u
      rcases s with (i | j) | ⟨⟩
      · simpa [B_tail, B₃, e, hB₂_blk] using hRfull_tr_U (Sum.inl i.succ) u
      · simpa [B_tail, B₃, e, hB₂_blk] using hRfull_tr_U (Sum.inr j.succ) u
      · simpa [B_tail, B₃, e, hB₂_blk] using hRfull_tr_U (Sum.inr 0) u
    obtain ⟨hsigS, Minv, hSMinv⟩ := petersenAintS_sig_and_inv w hw
    let R_S := B_tail.toBlocks₁₂
    let M_rem := B_tail.toBlocks₂₂
    have hB_tail_eq : B_tail = Matrix.fromBlocks (petersenAintS w) R_S R_Sᵀ M_rem := by
      ext p q
      rcases p with s₁ | r₁ <;> rcases q with s₂ | r₂
      · exact congr_fun (congr_fun hB_tail_11 s₁) s₂
      · rfl
      · simp [R_S, Matrix.toBlocks₁₂, B_tail, Matrix.toBlocks₂₂, hB₃_sym]
      · rfl
    let S_S := Minv * R_S
    let P_S := Matrix.fromBlocks (1 : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ) (-S_S) 0
      (1 : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ)
    let Q_S := Matrix.fromBlocks (1 : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Unit) ((Fin 3 ⊕ Fin 3) ⊕ Unit) ℝ) S_S 0
      (1 : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ)
    have hPQ_S : P_S * Q_S = 1 := by simp [P_S, Q_S, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hP_S_det : IsUnit P_S.det :=
      isUnit_iff_exists_inv.mpr ⟨Q_S.det, by rw [← Matrix.det_mul, hPQ_S, Matrix.det_one]⟩
    have hAintS_S : petersenAintS w * S_S = R_S := by
      simp [S_S, ← Matrix.mul_assoc, hSMinv]
    have hAintS_T : (petersenAintS w)ᵀ = petersenAintS w := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHermitian_petersenAintS w).eq
    have hSS_AintS : S_Sᵀ * petersenAintS w = R_Sᵀ := by
      calc S_Sᵀ * petersenAintS w = S_Sᵀ * (petersenAintS w)ᵀ := by rw [hAintS_T]
        _ = (petersenAintS w * S_S)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = R_Sᵀ := by rw [hAintS_S]
    let M_final : Matrix (Unit ⊕ U) (Unit ⊕ U) ℝ := M_rem - S_Sᵀ * R_S
    have hcongr_S : P_Sᵀ * B_tail * P_S = Matrix.fromBlocks (petersenAintS w) 0 0 M_final := by
      rw [hB_tail_eq]
      simp only [P_S, M_final, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
        Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      congr 1
      · rw [hAintS_S, neg_add_cancel]
      · rw [hSS_AintS, neg_add_cancel]
      · rw [hSS_AintS, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, sub_eq_neg_add]
    have hM_final_H : M_final.IsHermitian := by
      have h1 := isHermitian_congr B_tail P_S hB_tail_H
      rw [hcongr_S] at h1
      ext a b
      simpa [Matrix.conjTranspose_apply] using
        congr_fun (congr_fun h1.eq (Sum.inr a)) (Sum.inr b)
    rw [← signature_congr B_tail P_S hB_tail_H hP_S_det,
      signature_congr_eq_pa (isHermitian_congr B_tail P_S hB_tail_H)
        (isHermitian_fromBlocks _ (isHermitian_petersenAintS w) _ hM_final_H) hcongr_S,
      signature_fromBlocks _ (isHermitian_petersenAintS w) _ hM_final_H, hsigS]
    -- Step 6: Delete Sum.inl () from M_final via Cauchy interlacing
    have hinter := signature_interlacing_delete_vertex M_final hM_final_H (Sum.inl ())
    let eU : U ≃ {z : Unit ⊕ U // z ≠ Sum.inl ()} :=
      { toFun := fun u => ⟨Sum.inr u, by simp⟩
        invFun := fun ⟨z, hz⟩ => match z with
          | Sum.inl () => absurd rfl hz
          | Sum.inr u => u
        left_inv := fun u => rfl
        right_inv := fun ⟨z, hz⟩ => by rcases z with ⟨⟩ | u; exact absurd rfl hz; rfl }
    have hM_sub : (M_final.submatrix (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1)
        (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1)).submatrix eU eU =
        G₂.submatrix Sum.inr Sum.inr := by
      ext u v
      have hSS_0 : (S_Sᵀ * R_S) (Sum.inr u) (Sum.inr v) = 0 := by
        simp [R_S, Matrix.mul_apply, hB_tail_12_U]
      simp only [Matrix.submatrix_apply, eU, Equiv.coe_fn_mk, M_final, Matrix.sub_apply, hSS_0, sub_zero]
      simp [M_rem, B_tail, B₃, e, hB₂_blk, P_ext, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.mul_apply, Fintype.sum_sum_type]
    have hsig_del : signature (M_final.submatrix (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1)
        (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1))
        (isHermitian_submatrix M_final hM_final_H _) ≤ 0 := by
      rw [← signature_reindex eU _ (isHermitian_submatrix M_final hM_final_H _)]
      rw [signature_congr_eq_pa _ (isHermitian_submatrix G₂ hG₂ Sum.inr) hM_sub]
      exact hcase2
    have hle1 : signature M_final hM_final_H - signature
        (M_final.submatrix (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1)
          (fun x : {z : Unit ⊕ U // z ≠ Sum.inl ()} => x.1))
        (isHermitian_submatrix M_final hM_final_H _) ≤ 1 := (abs_le.mp hinter).2
    omega

end

end SignedGraphs
