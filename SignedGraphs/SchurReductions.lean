import SignedGraphs.LinearAlgebraExtra
import SignedGraphs.ParityAndCycles
import SignedGraphs.PetersenAlgebra

/-!
# Weighted `K₄` and Petersen Schur-Complement Reductions (Section 5)

This file formalizes Section 5:
* Lemma 5.1 (`k4_signature_nonpos`, `k4_leaf_reduction`).
* Lemma 5.2 (`petersen_signature_nonpos`, `petersen_leaf_reduction`),
  including both Case 1 (`det B ≠ 0`) and Case 2 (`det B = 0`).
-/

open Matrix SimpleGraph

namespace SignedGraphs

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma signature_congr_eq' {W : Type*} [Fintype W] [DecidableEq W]
    {M₁ M₂ : Matrix W W ℝ} (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) :
    signature M₁ h₁ = signature M₂ h₂ := by
  subst h; rfl

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
    have hadjA : (matrixSignedGraph A hA.isSymm).graph.Adj (e.symm i) (e.symm j) :=
      e.symm.map_rel_iff.mpr hadjK
    have hAne : A (e.symm i) (e.symm j) ≠ 0 := hadjA.2
    have hsw := hT (e.symm i) (e.symm j) hadjA
    simp only [k4SignedGraph, matrixSignedGraph, Sym2.lift_mk] at hsw
    have hBij : B i j = d (e.symm i) * A (e.symm i) (e.symm j) * d (e.symm j) := by
      simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [hBij]
    have hswR : (d (e.symm i) * d (e.symm j)) *
        (if 0 < A (e.symm i) (e.symm j) then (1 : ℝ) else -1) = 1 := by
      have h1 : (((if e.symm i ∈ T then (-1 : ℤ) else 1) * (if e.symm j ∈ T then -1 else 1) *
          (if 0 < A (e.symm i) (e.symm j) then (1 : ℤ) else -1) : ℤ) : ℝ) = (1 : ℝ) := by
        exact_mod_cast hsw
      push_cast at h1
      convert h1 using 2 <;> dsimp [d] <;> split_ifs <;> norm_num
    by_cases hpos : 0 < A (e.symm i) (e.symm j)
    · rw [if_pos hpos, mul_one] at hswR
      nlinarith
    · have hneg : A (e.symm i) (e.symm j) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hAne
      rw [if_neg hpos] at hswR
      nlinarith
  let a : ℝ := B 0 1
  let b : ℝ := B 0 2
  let c : ℝ := B 1 2
  have ha : 0 < a := hB_pos 0 1 (by decide)
  have hb : 0 < b := hB_pos 0 2 (by decide)
  have hc : 0 < c := hB_pos 1 2 (by decide)
  let ι : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun y i => if h : i.val < 3 then y ⟨i.val, h⟩ else 0
      map_add' := fun y₁ y₂ => by ext i; dsimp; split_ifs <;> simp
      map_smul' := fun r y => by ext i; dsimp; split_ifs <;> simp }
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
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, h10, h20, mul_zero, add_zero]
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
    (x y : V) (hxy : x ≠ y)
    (VH VG₂ : Finset V) (hunion : VH ∪ VG₂ = Finset.univ) (hinter : VH ∩ VG₂ = {x, y})
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
  classical
  rcases hH_iso with ⟨eH, he0, he1, hAuv, hAxu, hAxv, hAyu, hAyv⟩
  let u : V := (eH 2).1
  let v : V := (eH 3).1
  have hu_mem : u ∈ VH := (eH 2).2
  have hv_mem : v ∈ VH := (eH 3).2
  have hux : u ≠ x := fun h => by
    have : eH 2 = eH 0 := Subtype.ext (h.trans he0.symm)
    exact (by decide : (2 : Fin 4) ≠ 0) (eH.injective this)
  have huy : u ≠ y := fun h => by
    have : eH 2 = eH 1 := Subtype.ext (h.trans he1.symm)
    exact (by decide : (2 : Fin 4) ≠ 1) (eH.injective this)
  have hvx : v ≠ x := fun h => by
    have : eH 3 = eH 0 := Subtype.ext (h.trans he0.symm)
    exact (by decide : (3 : Fin 4) ≠ 0) (eH.injective this)
  have hvy : v ≠ y := fun h => by
    have : eH 3 = eH 1 := Subtype.ext (h.trans he1.symm)
    exact (by decide : (3 : Fin 4) ≠ 1) (eH.injective this)
  have huv : u ≠ v := fun h => by
    have : eH 2 = eH 3 := Subtype.ext h
    exact (by decide : (2 : Fin 4) ≠ 3) (eH.injective this)
  have hVH_eq : ∀ w ∈ VH, w = x ∨ w = y ∨ w = u ∨ w = v := by
    intro w hw
    have hi := eH.apply_symm_apply ⟨w, hw⟩
    have hval : (eH (eH.symm ⟨w, hw⟩)).1 = w := congrArg Subtype.val hi
    generalize eH.symm ⟨w, hw⟩ = idx at hval
    fin_cases idx
    · left; exact hval.symm.trans he0
    · right; left; exact hval.symm.trans he1
    · right; right; left; exact hval.symm
    · right; right; right; exact hval.symm
  have hno_u : ∀ w : V, w ≠ x → w ≠ y → w ≠ u → w ≠ v → A u w = 0 := by
    intro w hwx hwy hwu hwv
    have hwG₂ : w ∈ VG₂ := by
      have : w ∈ VH ∪ VG₂ := by rw [hunion]; exact Finset.mem_univ w
      rcases Finset.mem_union.mp this with hwH | hwG
      · rcases hVH_eq w hwH with rfl | rfl | rfl | rfl <;> contradiction
      · exact hwG
    exact hno_cross u hu_mem w hwG₂ hux huy hwx hwy
  have hno_v : ∀ w : V, w ≠ x → w ≠ y → w ≠ u → w ≠ v → A v w = 0 := by
    intro w hwx hwy hwu hwv
    have hwG₂ : w ∈ VG₂ := by
      have : w ∈ VH ∪ VG₂ := by rw [hunion]; exact Finset.mem_univ w
      rcases Finset.mem_union.mp this with hwH | hwG
      · rcases hVH_eq w hwH with rfl | rfl | rfl | rfl <;> contradiction
      · exact hwG
    exact hno_cross v hv_mem w hwG₂ hvx hvy hwx hwy
  let d : V → ℝ := fun w =>
    if w = v then (if 0 < A u v then 1 else -1)
    else if w = x then (if 0 < A x u then 1 else -1)
    else if w = y then (if 0 < A y u then 1 else -1)
    else 1
  have hd_ne : ∀ w, d w ≠ 0 := fun w => by dsimp [d]; split_ifs <;> norm_num
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun w _ => hd_ne w)
  let B : Matrix V V ℝ := Dᵀ * A * D
  have hB : B.IsHermitian := isHermitian_congr A D hA
  have hB_eq : B = Matrix.diagonal d * A * Matrix.diagonal d := by
    simp [B, D, Matrix.diagonal_transpose]
  have hB_diag : ∀ w, B w w = 0 := fun w => by
    simp [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, hdiag w]
  have hsym_B : ∀ a b : V, B a b = B b a := fun a b => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq a) b).symm
  have hB_noc : MatrixIsNOC B hB.isSymm := by
    have hB_sym : (Matrix.diagonal d * A * Matrix.diagonal d).IsSymm := hB_eq ▸ hB.isSymm
    simpa [hB_eq] using matrixIsNOC_diagonal_congr A hA.isSymm hnoc d hd_ne hB_sym
  rw [← signature_congr A D hA hD_det]
  change signature B hB ≤ 0
  have he₀_pos : 0 < B u v := by
    have h1 : B u v = d u * A u v * d v := by
      simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [h1]; dsimp [d]
    rw [if_neg huv, if_neg hux, if_neg huy, if_pos rfl]
    by_cases h : 0 < A u v
    · simp [h]
    · have hlt : A u v < 0 := lt_of_le_of_ne (not_lt.mp h) (by simpa [u, v] using hAuv)
      simp [h]; linarith
  have ha_pos : 0 < B x u := by
    have h1 : B x u = d x * A x u * d u := by
      simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [h1]; dsimp [d]
    rw [if_neg hvx.symm, if_pos rfl, if_neg huv, if_neg hux, if_neg huy]
    by_cases h : 0 < A x u
    · simp [h]
    · have hlt : A x u < 0 := lt_of_le_of_ne (not_lt.mp h) (by simpa [he0, u] using hAxu)
      simp [h]; linarith
  have hc_pos : 0 < B y u := by
    have h1 : B y u = d y * A y u * d u := by
      simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [h1]; dsimp [d]
    rw [if_neg hvy.symm, if_neg hxy.symm, if_pos rfl, if_neg huv, if_neg hux, if_neg huy]
    by_cases h : 0 < A y u
    · simp [h]
    · have hlt : A y u < 0 := lt_of_le_of_ne (not_lt.mp h) (by simpa [he1, u] using hAyu)
      simp [h]; linarith
  have hB_tri_pos : ∀ z : V, z ≠ u → z ≠ v → 0 < B z u → B z v ≠ 0 → 0 < B z v := by
    intro z hzu hzv hBzu hBzv
    by_contra hle
    have hneg : B z v < 0 := lt_of_le_of_ne (not_lt.mp hle) hBzv
    let cyc : (matrixSignedGraph B hB.isSymm).graph.Walk z z :=
      SimpleGraph.Walk.cons ⟨hzu, ne_of_gt hBzu⟩
        (SimpleGraph.Walk.cons ⟨huv, ne_of_gt he₀_pos⟩
          (SimpleGraph.Walk.cons ⟨hzv.symm, by rw [hsym_B]; exact hBzv⟩ SimpleGraph.Walk.nil))
    have hlen_c : cyc.length = 3 := rfl
    have hedges_c : cyc.edges = [s(z, u), s(u, v), s(v, z)] := rfl
    have hsupp_c : cyc.support.tail = [u, v, z] := rfl
    have hcyc : cyc.IsCycle := by
      refine ⟨⟨⟨?_⟩, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by rw [hlen_c]; simp)⟩, ?_⟩
      · rw [hedges_c]
        simp [Sym2.eq_iff, huv, hzu, hzv, hzu.symm, hzv.symm, huv.symm]
      · rw [hsupp_c]
        simp [huv, hzu.symm, hzv.symm]
    have hodd : Odd cyc.length := ⟨1, rfl⟩
    have hnoc_c := hB_noc z cyc hcyc hodd
    have hsign_c : signedCycleType (matrixSignedGraph B hB.isSymm).sign cyc = 1 := by
      rw [signedCycleType, walkSignProd, hlen_c, hedges_c]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        matrixSignedGraph, Sym2.lift_mk, hBzu, he₀_pos, hsym_B v z, not_lt.mpr hneg.le]
      norm_num
    rw [hsign_c] at hnoc_c
    norm_num at hnoc_c
  have hb_pos : 0 < B x v := by
    refine hB_tri_pos x hux.symm hvx.symm ha_pos ?_
    have h1 : B x v = d x * A x v * d v := by
      simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [h1]
    exact mul_ne_zero (mul_ne_zero (hd_ne x) (by simpa [he0, v] using hAxv)) (hd_ne v)
  have hd₀_pos : 0 < B y v := by
    refine hB_tri_pos y huy.symm hvy.symm hc_pos ?_
    have h1 : B y v = d y * A y v * d v := by
      simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [h1]
    exact mul_ne_zero (mul_ne_zero (hd_ne y) (by simpa [he1, v] using hAyv)) (hd_ne v)
  have hB_no_u : ∀ w : V, w ≠ x → w ≠ y → w ≠ u → w ≠ v → B u w = 0 := fun w h1 h2 h3 h4 => by
    simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hno_u w h1 h2 h3 h4]
  have hB_no_v : ∀ w : V, w ≠ x → w ≠ y → w ≠ u → w ≠ v → B v w = 0 := fun w h1 h2 h3 h4 => by
    simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hno_v w h1 h2 h3 h4]
  let W := {w : V // w ≠ u ∧ w ≠ v}
  let e : Fin 2 ⊕ W ≃ V :=
    { toFun := fun
        | Sum.inl 0 => u
        | Sum.inl 1 => v
        | Sum.inr w => w.1
      invFun := fun z =>
        if hzu : z = u then Sum.inl 0
        else if hzv : z = v then Sum.inl 1
        else Sum.inr ⟨z, hzu, hzv⟩
      left_inv := fun z => by
        rcases z with i | ⟨w, hwu, hwv⟩
        · fin_cases i <;> simp [huv.symm]
        · simp [hwu, hwv]
      right_inv := fun z => by
        by_cases hzu : z = u
        · simp [hzu]
        · by_cases hzv : z = v
          · simp [hzu, hzv, huv.symm]
          · simp [hzu, hzv] }
  have hcard_W : Fintype.card W = Fintype.card V - 2 := by
    have hcard_e : 2 + Fintype.card W = Fintype.card V := by
      simpa [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
    omega
  let B_blk := B.submatrix e e
  have hB_blk : B_blk.IsHermitian := isHermitian_submatrix B hB e
  rw [← signature_reindex e B hB]
  let e₀ : ℝ := B u v
  let a : ℝ := B x u
  let b : ℝ := B x v
  let c : ℝ := B y u
  let d₀ : ℝ := B y v
  let A_int : Matrix (Fin 2) (Fin 2) ℝ := !![0, e₀; e₀, 0]
  let R : Matrix (Fin 2) W ℝ := Matrix.of fun i w => match i with
    | 0 => if w.1 = x then a else if w.1 = y then c else 0
    | 1 => if w.1 = x then b else if w.1 = y then d₀ else 0
  let AG₂ : Matrix W W ℝ := B.submatrix Subtype.val Subtype.val
  have hB_blk_eq : B_blk = Matrix.fromBlocks A_int R Rᵀ AG₂ := by
    ext p q
    rcases p with i | w₁ <;> rcases q with j | w₂
    · fin_cases i <;> fin_cases j <;>
        simp [B_blk, e, A_int, e₀, hB_diag u, hB_diag v, hsym_B v u]
    · fin_cases i
      · by_cases hx : w₂.1 = x
        · simp [B_blk, e, R, a, hx, hsym_B u x]
        · by_cases hy : w₂.1 = y
          · simp [B_blk, e, R, c, hx, hy, hxy.symm, hsym_B u y]
          · simp [B_blk, e, R, hx, hy, hB_no_u w₂.1 hx hy w₂.2.1 w₂.2.2]
      · by_cases hx : w₂.1 = x
        · simp [B_blk, e, R, b, hx, hsym_B v x]
        · by_cases hy : w₂.1 = y
          · simp [B_blk, e, R, d₀, hx, hy, hxy.symm, hsym_B v y]
          · simp [B_blk, e, R, hx, hy, hB_no_v w₂.1 hx hy w₂.2.1 w₂.2.2]
    · fin_cases j
      · by_cases hx : w₁.1 = x
        · simp [B_blk, e, R, a, hx]
        · by_cases hy : w₁.1 = y
          · simp [B_blk, e, R, c, hx, hy, hxy.symm]
          · simp [B_blk, e, R, hx, hy, hsym_B w₁.1 u, hB_no_u w₁.1 hx hy w₁.2.1 w₁.2.2]
      · by_cases hx : w₁.1 = x
        · simp [B_blk, e, R, b, hx]
        · by_cases hy : w₁.1 = y
          · simp [B_blk, e, R, d₀, hx, hy, hxy.symm]
          · simp [B_blk, e, R, hx, hy, hsym_B w₁.1 v, hB_no_v w₁.1 hx hy w₁.2.1 w₁.2.2]
    · simp [B_blk, e, AG₂]
  let S : Matrix (Fin 2) W ℝ := Matrix.of fun i w => match i with
    | 0 => (if w.1 = x then b else if w.1 = y then d₀ else 0) / e₀
    | 1 => (if w.1 = x then a else if w.1 = y then c else 0) / e₀
  let P : Matrix (Fin 2 ⊕ W) (Fin 2 ⊕ W) ℝ := Matrix.fromBlocks 1 (-S) 0 1
  let Q : Matrix (Fin 2 ⊕ W) (Fin 2 ⊕ W) ℝ := Matrix.fromBlocks 1 S 0 1
  have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hP_det : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
  rw [← signature_congr B_blk P hB_blk hP_det]
  have he₀_ne : e₀ ≠ 0 := ne_of_gt he₀_pos
  have hAint_S : A_int * S = R := by
    ext i w
    fin_cases i <;> simp [A_int, S, R, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [he₀_ne]
  have hAint_H : A_int.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A_int, Matrix.conjTranspose_apply]
  have hAint_T : A_intᵀ = A_int := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hAint_H.eq
  let A_schur : Matrix W W ℝ := AG₂ - Sᵀ * R
  have hcongr : Pᵀ * B_blk * P = Matrix.fromBlocks A_int 0 0 A_schur := by
    rw [hB_blk_eq]
    simp only [P, A_schur, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hST_Aint : Sᵀ * A_int = Rᵀ := by
      calc Sᵀ * A_int = Sᵀ * A_intᵀ := by rw [hAint_T]
        _ = (A_int * S)ᵀ := (Matrix.transpose_mul A_int S).symm
        _ = Rᵀ := by rw [hAint_S]
    congr 1
    · rw [hAint_S, neg_add_cancel]
    · rw [hST_Aint, neg_add_cancel]
    · rw [hST_Aint, neg_add_cancel, Matrix.zero_mul, neg_zero, zero_add, sub_eq_neg_add]
  have hA_schur_H : A_schur.IsHermitian := by
    have h1 := isHermitian_congr B_blk P hB_blk
    rw [hcongr] at h1
    ext w₁ w₂
    have h2 := congr_fun (congr_fun h1.eq (Sum.inr w₁)) (Sum.inr w₂)
    simpa [Matrix.conjTranspose_apply] using h2
  rw [signature_congr_eq' (isHermitian_congr B_blk P hB_blk)
    (isHermitian_fromBlocks A_int hAint_H A_schur hA_schur_H) hcongr]
  rw [signature_fromBlocks A_int hAint_H A_schur hA_schur_H]
  have hs_int : signature A_int hAint_H = 0 :=
    signature_two_by_two_offdiag e₀ 0 he₀_ne hAint_H
  rw [hs_int, zero_add]
  let μ : ℝ := (a * d₀ + b * c) / e₀
  have hμ_pos : 0 < μ := by
    dsimp [μ]
    exact div_pos (by nlinarith [ha_pos, hb_pos, hc_pos, hd₀_pos]) he₀_pos
  let A' : Matrix W W ℝ := Matrix.of fun w₁ w₂ =>
    if (w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x) then B w₁.1 w₂.1 - μ else B w₁.1 w₂.1
  have hA'_H : A'.IsHermitian := by
    ext w₁ w₂
    simp only [A', Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    by_cases h : (w₂.1 = x ∧ w₁.1 = y) ∨ (w₂.1 = y ∧ w₁.1 = x)
    · have h' : (w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x) := by tauto
      simp [h, h', hsym_B w₂.1 w₁.1]
    · have h' : ¬((w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x)) := by tauto
      simp [h, h', hsym_B w₂.1 w₁.1]
  have hA'_diag : ∀ w : W, A' w w = 0 := by
    intro w
    have hnot : ¬((w.1 = x ∧ w.1 = y) ∨ (w.1 = y ∧ w.1 = x)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hxy (h1.symm.trans h2)
      · exact hxy (h2.symm.trans h1)
    simp [A', hnot, hB_diag w.1]
  have hSR : ∀ w₁ w₂ : W, (Sᵀ * R) w₁ w₂ =
      if w₁.1 = x ∧ w₂.1 = x then 2 * a * b / e₀
      else if w₁.1 = y ∧ w₂.1 = y then 2 * c * d₀ / e₀
      else if (w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x) then μ
      else 0 := by
    intro w₁ w₂
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, S, R, Matrix.of_apply, μ]
    by_cases h1x : w₁.1 = x <;> by_cases h1y : w₁.1 = y <;>
      by_cases h2x : w₂.1 = x <;> by_cases h2y : w₂.1 = y
    all_goals
      first
      | (exfalso; exact hxy (h1x.symm.trans h1y))
      | (exfalso; exact hxy (h2x.symm.trans h2y))
      | (simp [h1x, h1y, h2x, h2y, hxy, hxy.symm]; try ring)
  have hdiff_entry : ∀ w₁ w₂ : W, (A' - A_schur) w₁ w₂ =
      if w₁.1 = x ∧ w₂.1 = x then 2 * a * b / e₀
      else if w₁.1 = y ∧ w₂.1 = y then 2 * c * d₀ / e₀
      else 0 := by
    intro w₁ w₂
    simp only [Matrix.sub_apply, A_schur, AG₂, Matrix.submatrix_apply, A', Matrix.of_apply, hSR]
    by_cases h1x : w₁.1 = x <;> by_cases h1y : w₁.1 = y <;>
      by_cases h2x : w₂.1 = x <;> by_cases h2y : w₂.1 = y
    all_goals
      first
      | (exfalso; exact hxy (h1x.symm.trans h1y))
      | (exfalso; exact hxy (h2x.symm.trans h2y))
      | simp [h1x, h1y, h2x, h2y, hxy, hxy.symm]
  have hWeyl : signature A_schur hA_schur_H ≤ signature A' hA'_H := by
    refine signature_mono_of_posSemidef A_schur A' hA_schur_H hA'_H ?_
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA'_H.sub hA_schur_H, fun z => ?_⟩
    let x' : W := ⟨x, hux.symm, hvx.symm⟩
    let y' : W := ⟨y, huy.symm, hvy.symm⟩
    have hmul : ∀ w₁ : W, ((A' - A_schur) *ᵥ z) w₁ =
        if w₁ = x' then (2 * a * b / e₀) * z x'
        else if w₁ = y' then (2 * c * d₀ / e₀) * z y'
        else 0 := by
      intro w₁
      simp only [Matrix.mulVec, dotProduct, hdiff_entry]
      by_cases h1 : w₁ = x'
      · subst h1
        have hxy' : ¬(x = y) := hxy
        simp only [x', ↓reduceIte, hxy', false_and, true_and]
        rw [Finset.sum_eq_single x']
        · simp [x']
        · intro w₂ _ hw₂
          have : w₂.1 ≠ x := fun h => hw₂ (Subtype.ext h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ x') h
      · by_cases h2 : w₁ = y'
        · subst h2
          simp only [h1, ↓reduceIte, y', hxy.symm, false_and, true_and]
          rw [Finset.sum_eq_single y']
          · simp [y']
          · intro w₂ _ hw₂
            have : w₂.1 ≠ y := fun h => hw₂ (Subtype.ext h)
            simp [this]
          · intro h; exact absurd (Finset.mem_univ y') h
        · have h1x : w₁.1 ≠ x := fun h => h1 (Subtype.ext h)
          have h1y : w₁.1 ≠ y := fun h => h2 (Subtype.ext h)
          simp [h1, h2, h1x, h1y]
    have hxy'_ne : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    have hquad : dotProduct (star z) ((A' - A_schur) *ᵥ z) =
        (2 * a * b / e₀) * (z x') ^ 2 + (2 * c * d₀ / e₀) * (z y') ^ 2 := by
      simp only [dotProduct, star_trivial, hmul]
      have h1 : ∀ w : W, z w * (if w = x' then 2 * a * b / e₀ * z x'
          else if w = y' then 2 * c * d₀ / e₀ * z y' else 0) =
          (if w = x' then (2 * a * b / e₀) * (z x') ^ 2 else 0) +
          (if w = y' then (2 * c * d₀ / e₀) * (z y') ^ 2 else 0) := by
        intro w
        by_cases hwx : w = x'
        · subst hwx; simp [hxy'_ne]; ring
        · by_cases hwy : w = y'
          · subst hwy; simp [hwx]; ring
          · simp [hwx, hwy]
      simp_rw [h1]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_eq_single x']
        · simp
        · intro w _ hw; simp [hw]
        · intro h; exact absurd (Finset.mem_univ x') h
      · rw [Finset.sum_eq_single y']
        · simp
        · intro w _ hw; simp [hw]
        · intro h; exact absurd (Finset.mem_univ y') h
    rw [hquad]
    have h1 : 0 ≤ 2 * a * b / e₀ := div_nonneg (by nlinarith [ha_pos, hb_pos]) he₀_pos.le
    have h2 : 0 ≤ 2 * c * d₀ / e₀ := div_nonneg (by nlinarith [hc_pos, hd₀_pos]) he₀_pos.le
    nlinarith [sq_nonneg (z x'), sq_nonneg (z y')]
  have hA'_noc : MatrixIsNOC A' hA'_H.isSymm := by
    let x' : W := ⟨x, hux.symm, hvx.symm⟩
    let y' : W := ⟨y, huy.symm, hvy.symm⟩
    have hxy'_ne : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    have hlift_avoid : ∀ {p₁ p₂ : W} (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk p₁ p₂),
        s(x', y') ∉ p.edges →
        ∃ q : (matrixSignedGraph B hB.isSymm).graph.Walk p₁.1 p₂.1,
          q.length = p.length ∧
          walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
            walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p ∧
          q.support = p.support.map Subtype.val ∧
          q.edges = p.edges.map (Sym2.map Subtype.val) := by
      intro p₁ p₂ p
      induction p with
      | nil => intro _; exact ⟨SimpleGraph.Walk.nil, rfl, rfl, rfl, rfl⟩
      | @cons s₁ s₂ s₃ hadj r ihr =>
        intro hnot
        have hne_edge : s(s₁, s₂) ≠ s(x', y') := fun h =>
          hnot (by simp [SimpleGraph.Walk.edges_cons, h])
        have hnot_r : s(x', y') ∉ r.edges := fun hm =>
          hnot (by simp [SimpleGraph.Walk.edges_cons, hm])
        have hnot_xy : ¬((s₁.1 = x ∧ s₂.1 = y) ∨ (s₁.1 = y ∧ s₂.1 = x)) := by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hne_edge (by rw [show s₁ = x' from Subtype.ext h1, show s₂ = y' from Subtype.ext h2])
          · exact hne_edge (by rw [show s₁ = y' from Subtype.ext h1, show s₂ = x' from Subtype.ext h2, Sym2.eq_swap])
        have hA'_eq_B : A' s₁ s₂ = B s₁.1 s₂.1 := by simp [A', hnot_xy]
        have hadjB : (matrixSignedGraph B hB.isSymm).graph.Adj s₁.1 s₂.1 :=
          ⟨fun h => hadj.1 (Subtype.ext h), by rw [← hA'_eq_B]; exact hadj.2⟩
        obtain ⟨q', hq'len, hq'sign, hq'supp, hq'edges⟩ := ihr hnot_r
        refine ⟨SimpleGraph.Walk.cons hadjB q', by simp [hq'len], ?_, ?_, ?_⟩
        · simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
          have h1 : (matrixSignedGraph B hB.isSymm).sign s(s₁.1, s₂.1) =
              (matrixSignedGraph A' hA'_H.isSymm).sign s(s₁, s₂) := by
            simp [matrixSignedGraph, hA'_eq_B]
          rw [h1]; exact congrArg _ hq'sign
        · simp [SimpleGraph.Walk.support_cons, hq'supp]
        · simp [SimpleGraph.Walk.edges_cons, hq'edges]
    intro w₀ c hc hodd
    by_cases hedge : s(x', y') ∈ c.edges
    · have hA'_xy_ne : B x y - μ ≠ 0 := by
        have hAdj := SimpleGraph.Walk.adj_of_mem_edges c hedge
        have h2 := hAdj.2
        simpa [matrixSignedGraph, matrixGraph, A', x', y'] using h2
      rcases lt_or_gt_of_ne hA'_xy_ne with hneg | hpos
      · have hx'_mem : x' ∈ c.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c hedge
        let c₀ := c.rotate x' hx'_mem
        have hc₀ : c₀.IsCycle := hc.rotate hx'_mem
        have hlen₀ : c₀.length = c.length := SimpleGraph.Walk.length_rotate c x' hx'_mem
        have hperm₀ : c₀.edges.Perm c.edges := by
          have h1 : c₀.edges = (c.dropUntil x' hx'_mem).edges ++ (c.takeUntil x' hx'_mem).edges := by
            simp [c₀, SimpleGraph.Walk.rotate, SimpleGraph.Walk.edges_append]
          have h2 : c.edges = (c.takeUntil x' hx'_mem).edges ++ (c.dropUntil x' hx'_mem).edges := by
            conv_lhs => rw [← SimpleGraph.Walk.take_spec c hx'_mem]
            exact SimpleGraph.Walk.edges_append _ _
          rw [h1, h2]
          exact List.perm_append_comm
        have hsign₀ : walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c₀ =
            walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c := by
          simp only [walkSignProd]; exact (hperm₀.map _).prod_eq
        have hedge₀ : s(x', y') ∈ c₀.edges := hperm₀.mem_iff.mpr hedge
        have hex_oriented : ∃ (c₁ : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk x' x'),
            c₁.IsCycle ∧ c₁.length = c.length ∧
            walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c₁ =
              walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c ∧
            ∃ (hxy' : (matrixSignedGraph A' hA'_H.isSymm).graph.Adj x' y')
              (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk y' x'),
              c₁ = SimpleGraph.Walk.cons hxy' p := by
          cases hc₀_eq : c₀ with
          | nil => exact absurd hc₀_eq hc₀.ne_nil
          | @cons _ z₁ _ h₁ r =>
            by_cases hz₁ : z₁ = y'
            · subst hz₁
              exact ⟨c₀, hc₀, hlen₀, hsign₀, h₁, r, hc₀_eq⟩
            · have hr_mem : s(x', y') ∈ r.edges := by
                rw [hc₀_eq, SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge₀
                rcases hedge₀ with h | h
                · exfalso
                  rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
                  · exact hz₁ h2.symm
                  · exact h₁.1 h1
                · exact h
              cases hrr : r.reverse with
              | nil =>
                have : r = SimpleGraph.Walk.nil := by
                  have := congrArg SimpleGraph.Walk.reverse hrr; simpa using this
                subst this; exact absurd rfl h₁.1
              | @cons _ z₂ _ h₂' r' =>
                have hnot_x' : x' ∉ r'.support := by
                  have hnd : r.reverse.support.Nodup := by
                    rw [SimpleGraph.Walk.support_reverse, List.nodup_reverse]
                    have htail := hc₀.support_nodup
                    rw [hc₀_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at htail
                    exact htail
                  rw [hrr, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                  exact hnd.1
                have hmem_rr : s(x', y') ∈ r.reverse.edges := by
                  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hr_mem
                rw [hrr, SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem_rr
                have hz₂ : z₂ = y' := by
                  rcases hmem_rr with h | h
                  · rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
                    · exact h2.symm
                    · exact absurd h1 h₂'.1
                  · exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges r' h) hnot_x'
                subst hz₂
                have hc₀_rev : c₀.reverse =
                    SimpleGraph.Walk.cons h₂' (r'.append (SimpleGraph.Walk.cons h₁.symm SimpleGraph.Walk.nil)) := by
                  rw [hc₀_eq, SimpleGraph.Walk.reverse_cons, hrr, SimpleGraph.Walk.cons_append]
                refine ⟨c₀.reverse, hc₀.reverse, by simp [hlen₀], ?_, h₂',
                  r'.append (SimpleGraph.Walk.cons h₁.symm SimpleGraph.Walk.nil), hc₀_rev⟩
                rw [← hsign₀]
                simp [walkSignProd, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.prod_reverse]
        rcases hex_oriented with ⟨c₁, hc₁, hlen₁, hsign₁, hxy', p, hc₁_eq⟩
        have hnot_p : s(x', y') ∉ p.edges := by
          have hed := hc₁.edges_nodup
          rw [hc₁_eq, SimpleGraph.Walk.edges_cons, List.nodup_cons] at hed
          exact hed.1
        have hp_path : p.IsPath := by
          have htail := hc₁.support_nodup
          rw [hc₁_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at htail
          exact SimpleGraph.Walk.IsPath.mk' htail
        obtain ⟨P, hPlen, hPsign, hPsupp, _⟩ := hlift_avoid p hnot_p
        have hP_path : P.IsPath :=
          SimpleGraph.Walk.IsPath.mk' (by rw [hPsupp]; exact hp_path.support_nodup.map Subtype.coe_injective)
        have hu_notP : u ∉ P.support := by
          intro hm; rw [hPsupp, List.mem_map] at hm; rcases hm with ⟨w, _, hw⟩; exact w.2.1 hw
        have hv_notP : v ∉ P.support := by
          intro hm; rw [hPsupp, List.mem_map] at hm; rcases hm with ⟨w, _, hw⟩; exact w.2.2 hw
        have hadj1 : (matrixSignedGraph B hB.isSymm).graph.Adj x u := ⟨hux.symm, ne_of_gt ha_pos⟩
        have hadj2 : (matrixSignedGraph B hB.isSymm).graph.Adj u v := ⟨huv, ne_of_gt he₀_pos⟩
        have hadj3 : (matrixSignedGraph B hB.isSymm).graph.Adj v y := ⟨hvy, by rw [hsym_B]; exact ne_of_gt hd₀_pos⟩
        let cyc : (matrixSignedGraph B hB.isSymm).graph.Walk x x :=
          SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 (SimpleGraph.Walk.cons hadj3 P))
        have hcyc : cyc.IsCycle := by
          refine ⟨⟨⟨?_⟩, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by simp [cyc])⟩, ?_⟩
          · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
              List.nodup_cons, List.nodup_cons, List.nodup_cons]
            refine ⟨?_, ?_, ?_, hP_path.isTrail.edges_nodup⟩
            · intro hm
              rcases List.mem_cons.mp hm with h | hm
              · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact hux h1.symm
                · exact hvx h1.symm
              · rcases List.mem_cons.mp hm with h | hm
                · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                  · exact hvx h1.symm
                  · exact hxy h1
                · exact hu_notP (SimpleGraph.Walk.snd_mem_support_of_mem_edges P hm)
            · intro hm
              rcases List.mem_cons.mp hm with h | hm
              · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact huv h1
                · exact huy h1
              · exact hu_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hm)
            · intro hm
              exact hv_notP (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hm)
          · simp only [cyc, SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_cons]
            exact ⟨by simp [huv, hu_notP], by simp [hv_notP], hP_path.support_nodup⟩
        have hcyc_len : cyc.length = c.length + 2 := by
          have : c₁.length = p.length + 1 := by rw [hc₁_eq, SimpleGraph.Walk.length_cons]
          simp [cyc, hPlen]; omega
        have hcyc_odd : Odd cyc.length := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
        have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
            - walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c := by
          rw [← hsign₁, hc₁_eq]
          simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
          have hs1 : (matrixSignedGraph B hB.isSymm).sign s(x, u) = 1 := by
            simp [matrixSignedGraph, ha_pos]
          have hs2 : (matrixSignedGraph B hB.isSymm).sign s(u, v) = 1 := by
            simp [matrixSignedGraph, he₀_pos]
          have hs3 : (matrixSignedGraph B hB.isSymm).sign s(v, y) = 1 := by
            simp [matrixSignedGraph, hsym_B v y, hd₀_pos]
          have hs_xy : (matrixSignedGraph A' hA'_H.isSymm).sign s(x', y') = -1 := by
            simp [matrixSignedGraph, A', x', y', not_lt.mpr hneg.le]
          rw [hs1, hs2, hs3, hs_xy]
          change 1 * (1 * (1 * walkSignProd (matrixSignedGraph B hB.isSymm).sign P)) =
            -(-1 * walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p)
          rw [hPsign]; ring
        have hnoc_cyc := hB_noc x cyc hcyc hcyc_odd
        rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
        have hdiv : (c.length + 2) / 2 = c.length / 2 + 1 := by omega
        rw [hdiv, pow_succ] at hnoc_cyc
        rw [signedCycleType]
        linarith
      · have hBxy_pos : 0 < B x y := by linarith
        let emb : (matrixSignedGraph A' hA'_H.isSymm).graph ↪g (matrixSignedGraph B hB.isSymm).graph :=
          { toFun := Subtype.val
            inj' := Subtype.coe_injective
            map_rel_iff' := by
              intro w₁ w₂
              constructor
              · rintro ⟨hne, hval⟩
                refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
                by_cases h : (w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x)
                · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · simp [matrixSignedGraph, matrixGraph, A', h1, h2]; exact ne_of_gt hpos
                  · simp [matrixSignedGraph, matrixGraph, A', h1, h2, hsym_B y x]; exact ne_of_gt hpos
                · simpa [matrixSignedGraph, matrixGraph, A', h] using hval
              · rintro ⟨hne, hval⟩
                refine ⟨fun h => hne (Subtype.ext h), ?_⟩
                by_cases h : (w₁.1 = x ∧ w₂.1 = y) ∨ (w₁.1 = y ∧ w₂.1 = x)
                · change B w₁.1 w₂.1 ≠ 0
                  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1, h2]; exact ne_of_gt hBxy_pos
                  · rw [h1, h2, hsym_B y x]; exact ne_of_gt hBxy_pos
                · simpa [matrixSignedGraph, matrixGraph, A', h] using hval }
        let c' : (matrixSignedGraph B hB.isSymm).graph.Walk w₀.1 w₀.1 := c.map emb.toHom
        have hc' : c'.IsCycle := hc.map emb.injective
        have hlen' : c'.length = c.length := SimpleGraph.Walk.length_map emb.toHom c
        have hsign' : ∀ {s t : W} (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk s t),
            walkSignProd (matrixSignedGraph B hB.isSymm).sign (p.map emb.toHom) =
              walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p := by
          intro s t p
          induction p with
          | nil => rfl
          | @cons s₁ s₂ _ _ r ihr =>
            simp only [SimpleGraph.Walk.map_cons, walkSignProd, SimpleGraph.Walk.edges_cons,
              List.map_cons, List.prod_cons]
            have h1 : (matrixSignedGraph B hB.isSymm).sign s(emb.toHom s₁, emb.toHom s₂) =
                (matrixSignedGraph A' hA'_H.isSymm).sign s(s₁, s₂) := by
              change (matrixSignedGraph B hB.isSymm).sign s(s₁.1, s₂.1) = _
              by_cases h : (s₁.1 = x ∧ s₂.1 = y) ∨ (s₁.1 = y ∧ s₂.1 = x)
              · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · simp [matrixSignedGraph, A', h1, h2, hBxy_pos, hpos]
                · simp [matrixSignedGraph, A', h1, h2, hsym_B y x, hBxy_pos, hpos]
              · simp [matrixSignedGraph, A', h]
            rw [h1]
            exact congrArg _ ihr
        have hnoc' := hB_noc w₀.1 c' hc' (hlen'.symm ▸ hodd)
        rw [signedCycleType, ← hlen', ← hsign' c]
        exact hnoc'
    · obtain ⟨q, hqlen, hqsign, hqsupp, hqedges⟩ := hlift_avoid c hedge
      have hqcyc : q.IsCycle := by
        refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
        · rw [hqedges]
          exact hc.edges_nodup.map (Sym2.map.injective Subtype.coe_injective)
        · intro hqnil
          have hlen0 : c.length = 0 := by rw [← hqlen, hqnil]; rfl
          cases c with
          | nil => exact hc.ne_nil rfl
          | cons _ _ => simp at hlen0
        · rw [hqsupp, ← List.map_tail]
          exact hc.support_nodup.map Subtype.coe_injective
      have hnoc_q := hB_noc w₀.1 q hqcyc (hqlen.symm ▸ hodd)
      rw [signedCycleType, ← hqlen, ← hqsign]
      exact hnoc_q
  have hA'_le := ih W hcard_W A' hA'_H hA'_diag hA'_noc
  omega

private lemma petersenGraph_adj_decide (i j : Fin 10) :
    petersenGraph.Adj i j ↔
      i ≠ j ∧
      ((i.val < 5 ∧ j.val < 5 ∧ (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
       (5 ≤ i.val ∧ 5 ≤ j.val ∧
         ((j.val - 5) = ((i.val - 5) + 2) % 5 ∨ (i.val - 5) = ((j.val - 5) + 2) % 5)) ∨
       (i.val < 5 ∧ j.val = i.val + 5) ∨
       (j.val < 5 ∧ i.val = j.val + 5)) := by
  simp only [petersenGraph, SimpleGraph.fromRel_adj]
  tauto

/-- Canonical vertex index in `Fin 10` for the 8 interior vertices `(2,4,5,6; 3,7,8,9)`
and 2 boundary vertices `(0,1)` of `Petersen`. -/
private def petersenIdx : (Fin 4 ⊕ Fin 4) ⊕ Fin 2 → Fin 10
  | Sum.inl (Sum.inl 0) => 2
  | Sum.inl (Sum.inl 1) => 4
  | Sum.inl (Sum.inl 2) => 5
  | Sum.inl (Sum.inl 3) => 6
  | Sum.inl (Sum.inr 0) => 3
  | Sum.inl (Sum.inr 1) => 7
  | Sum.inl (Sum.inr 2) => 8
  | Sum.inl (Sum.inr 3) => 9
  | Sum.inr 0 => 0
  | Sum.inr 1 => 1

private def petersenIdxInv : Fin 10 → (Fin 4 ⊕ Fin 4) ⊕ Fin 2
  | 0 => Sum.inr 0
  | 1 => Sum.inr 1
  | 2 => Sum.inl (Sum.inl 0)
  | 3 => Sum.inl (Sum.inr 0)
  | 4 => Sum.inl (Sum.inl 1)
  | 5 => Sum.inl (Sum.inl 2)
  | 6 => Sum.inl (Sum.inl 3)
  | 7 => Sum.inl (Sum.inr 1)
  | 8 => Sum.inl (Sum.inr 2)
  | 9 => Sum.inl (Sum.inr 3)

private lemma not_petersenGraph_adj (i j : Fin 10)
    (h : ¬ (i ≠ j ∧
      ((i.val < 5 ∧ j.val < 5 ∧ (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
       (5 ≤ i.val ∧ 5 ≤ j.val ∧
         ((j.val - 5) = ((i.val - 5) + 2) % 5 ∨ (i.val - 5) = ((j.val - 5) + 2) % 5)) ∨
       (i.val < 5 ∧ j.val = i.val + 5) ∨
       (j.val < 5 ∧ i.val = j.val + 5)))) : ¬ petersenGraph.Adj i j := by
  rw [petersenGraph_adj_decide]; exact h

private def petersenEquiv : (Fin 4 ⊕ Fin 4) ⊕ Fin 2 ≃ Fin 10 where
  toFun := petersenIdx
  invFun := petersenIdxInv
  left_inv x := by
    rcases x with (i | j) | k
    · fin_cases i <;> rfl
    · fin_cases j <;> rfl
    · fin_cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

set_option maxHeartbeats 800000 in
/-- **Lemma 5.2(1)**: Every weighted `(Petersen, -1)` NOC matrix has `s(A) ≤ 0`. -/
theorem petersen_signature_nonpos (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0)
    (hiso : SwitchingIso (matrixSignedGraph A hA.isSymm) petersenSignedGraph) :
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
  let B : Matrix (Fin 10) (Fin 10) ℝ := B₀.submatrix e.symm.toEquiv e.symm.toEquiv
  have hB : B.IsHermitian := isHermitian_submatrix B₀ hB₀ e.symm.toEquiv
  rw [← signature_congr A D hA hD_det, ← signature_reindex e.symm.toEquiv B₀ hB₀]
  change signature B hB ≤ 0
  have hB_diag : ∀ i : Fin 10, B i i = 0 := fun i => by
    simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hdiag]
  have hB_sym : ∀ i j : Fin 10, B i j = B j i := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq i) j).symm
  have hB_neg : ∀ i j : Fin 10, petersenGraph.Adj i j → B i j < 0 := by
    intro i j hadjP
    have hadjA : (matrixSignedGraph A hA.isSymm).graph.Adj (e.symm i) (e.symm j) :=
      e.symm.map_rel_iff.mpr hadjP
    have hAne : A (e.symm i) (e.symm j) ≠ 0 := hadjA.2
    have hsw := hT (e.symm i) (e.symm j) hadjA
    simp only [petersenSignedGraph, matrixSignedGraph, Sym2.lift_mk] at hsw
    have hBij : B i j = d (e.symm i) * A (e.symm i) (e.symm j) * d (e.symm j) := by
      simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [hBij]
    have hswR : (d (e.symm i) * d (e.symm j)) *
        (if 0 < A (e.symm i) (e.symm j) then (1 : ℝ) else -1) = -1 := by
      have h1 : (((if e.symm i ∈ T then (-1 : ℤ) else 1) * (if e.symm j ∈ T then -1 else 1) *
          (if 0 < A (e.symm i) (e.symm j) then (1 : ℤ) else -1) : ℤ) : ℝ) = (-1 : ℝ) := by
        exact_mod_cast hsw
      push_cast at h1
      convert h1 using 2 <;> dsimp [d] <;> split_ifs <;> norm_num
    by_cases hpos : 0 < A (e.symm i) (e.symm j)
    · rw [if_pos hpos, mul_one] at hswR
      nlinarith
    · have hneg : A (e.symm i) (e.symm j) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hAne
      rw [if_neg hpos] at hswR
      nlinarith
  have hB_zero : ∀ i j : Fin 10, ¬ petersenGraph.Adj i j → B i j = 0 := by
    intro i j hnot
    by_cases hij : i = j
    · subst hij; exact hB_diag i
    · have hnotA : ¬ (matrixSignedGraph A hA.isSymm).graph.Adj (e.symm i) (e.symm j) :=
        fun h => hnot (e.symm.map_rel_iff.mp h)
      have hA0 : A (e.symm i) (e.symm j) = 0 := by
        by_contra hne
        exact hnotA ⟨fun h => hij (e.symm.injective h), hne⟩
      simp [B, B₀, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hA0]
  let w : Fin 14 → ℝ := ![
    -B 1 2, -B 2 3, -B 3 4, -B 4 0, -B 5 7, -B 6 8, -B 7 9,
    -B 8 5, -B 9 6, -B 0 5, -B 1 6, -B 2 7, -B 3 8, -B 4 9]
  have hw : ∀ k : Fin 14, 0 < w k := by
    intro k
    fin_cases k <;> dsimp [w] <;>
      linarith [hB_neg _ _ ((petersenGraph_adj_decide _ _).mpr (by decide))]
  let eFull : (Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ Empty) ≃ Fin 10 :=
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumEmpty (Fin 2) Empty)).trans petersenEquiv
  let B_blk := B.submatrix eFull eFull
  have hB_blk : B_blk.IsHermitian := isHermitian_submatrix B hB eFull
  rw [← signature_reindex eFull B hB]
  let G₂ : Matrix (Fin 2 ⊕ Empty) (Fin 2 ⊕ Empty) ℝ := B_blk.toBlocks₂₂
  have hG₂ : G₂.IsHermitian := isHermitian_submatrix B_blk hB_blk Sum.inr
  have hG₂_00 : G₂ (Sum.inl 0) (Sum.inl 0) = 0 := by
    simpa [G₂, B_blk, eFull, petersenEquiv, petersenIdx] using hB_diag 0
  have hB_blk_eq : B_blk = Matrix.fromBlocks (petersenAint w)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)ᵀ
      G₂ := by
    ext p q
    rcases p with (a | a) | (i | ⟨⟩) <;> rcases q with (b | b) | (j | ⟨⟩)
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenAint] <;>
        exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenAint, petersenB, w] <;>
        first | rfl | exact hB_sym _ _ | exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases j <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenR, petersenRU, w] <;>
        first | rfl | exact hB_sym _ _ | exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenAint, petersenB, w] <;>
        first | rfl | exact hB_sym _ _ | exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenAint, petersenC, w] <;>
        first | rfl | exact hB_sym _ _ | exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases j <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenR] <;>
        exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases i <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenR, petersenRU, w] <;>
        first | rfl | exact hB_sym _ _ | exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · fin_cases i <;> fin_cases b <;>
        simp [B_blk, eFull, petersenEquiv, petersenIdx, petersenR] <;>
        exact hB_zero _ _ (not_petersenGraph_adj _ _ (by decide))
    · rfl
  refine petersen_block_signature_nonpos w hw G₂ hG₂ hG₂_00 B_blk hB_blk hB_blk_eq ?_ ?_
  · intro hdet
    let e₂ : Fin 2 ≃ Fin 2 ⊕ Empty := (Equiv.sumEmpty (Fin 2) Empty).symm
    let M₂ := (G₂ + Matrix.fromBlocks (petersenMH w) (0 : Matrix (Fin 2) Empty ℝ) 0 0).submatrix e₂ e₂
    have hM₂ : M₂.IsHermitian := isHermitian_submatrix _ _ e₂
    rw [← signature_reindex e₂ _ _]
    refine signature_two_by_two_neg_diag M₂ hM₂ ?_
    have h00 : M₂ 0 0 = petersenMH w 0 0 := by
      simp [M₂, e₂, hG₂_00]
    rw [h00]
    exact (petersenMH_signs w hw hdet).1
  · have hsum := inertia_sum (G₂.submatrix Sum.inr Sum.inr) (isHermitian_submatrix G₂ hG₂ Sum.inr)
    rw [Fintype.card_empty] at hsum
    simp only [signature]
    omega

set_option maxHeartbeats 1200000 in
/-- **Lemma 5.2(2)**: Weighted `(Petersen - xy, -1)` leaf reduction (`|V| - 8`). -/
theorem petersen_leaf_reduction (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ u, A u u = 0) (hnoc : MatrixIsNOC A hA.isSymm)
    (x y : V) (hxy : x ≠ y)
    (VH VG₂ : Finset V) (hunion : VH ∪ VG₂ = Finset.univ) (hinter : VH ∩ VG₂ = {x, y})
    (hcardH : VH.card = 10)
    (hno_cross : ∀ u ∈ VH, ∀ w ∈ VG₂, u ≠ x → u ≠ y → w ≠ x → w ≠ y → A u w = 0)
    (hH_iso : ∃ (e : Fin 10 ≃ VH) (T : Finset V),
      (e 0).1 = x ∧ (e 1).1 = y ∧
      ∀ (i j : Fin 10), i ≠ j → ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
        if petersenGraph.Adj i j then
          (if (e i).1 ∈ T then (-1 : ℝ) else 1) * (if (e j).1 ∈ T then -1 else 1) *
            A (e i).1 (e j).1 < 0
        else A (e i).1 (e j).1 = 0)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W ≤ Fintype.card V - 8 →
      ∀ (B : Matrix W W ℝ) (hB : B.IsHermitian),
        (∀ z, B z z = 0) → MatrixIsNOC B hB.isSymm → signature B hB ≤ 0) :
    signature A hA ≤ 0 := by
  classical
  rcases hH_iso with ⟨eH, T, he0, he1, hH_edges⟩
  let d : V → ℝ := fun u => if u ∈ T then -1 else 1
  have hd_ne : ∀ u, d u ≠ 0 := fun u => by dsimp [d]; split_ifs <;> norm_num
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun u _ => hd_ne u)
  let B : Matrix V V ℝ := Dᵀ * A * D
  have hB : B.IsHermitian := isHermitian_congr A D hA
  have hB_eq : B = Matrix.diagonal d * A * Matrix.diagonal d := by
    simp [B, D, Matrix.diagonal_transpose]
  have hB_diag : ∀ u, B u u = 0 := fun u => by
    simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, hdiag u]
  have hsym_B : ∀ a b : V, B a b = B b a := fun a b => by
    simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hB.eq a) b).symm
  have hB_noc : MatrixIsNOC B hB.isSymm := by
    have hB_sym : (Matrix.diagonal d * A * Matrix.diagonal d).IsSymm := hB_eq ▸ hB.isSymm
    simpa [hB_eq] using matrixIsNOC_diagonal_congr A hA.isSymm hnoc d hd_ne hB_sym
  rw [← signature_congr A D hA hD_det]
  change signature B hB ≤ 0
  have hB_entry : ∀ u v : V, B u v = d u * A u v * d v := fun u v => by
    simp [B, D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hB_H_neg : ∀ i j : Fin 10, ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      petersenGraph.Adj i j → B (eH i).1 (eH j).1 < 0 := by
    intro i j hnot01 hadj
    have hne : i ≠ j := hadj.ne
    have h1 := hH_edges i j hne hnot01
    rw [if_pos hadj] at h1
    rw [hB_entry]
    dsimp [d]
    linarith
  have hB_H_zero : ∀ i j : Fin 10, ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      ¬ petersenGraph.Adj i j → B (eH i).1 (eH j).1 = 0 := by
    intro i j hnot01 hnotadj
    by_cases hij : i = j
    · subst hij; exact hB_diag _
    · have h1 := hH_edges i j hij hnot01
      rw [if_neg hnotadj] at h1
      rw [hB_entry, h1]; ring
  have hB_cross : ∀ i : Fin 10, i ≠ 0 → i ≠ 1 → ∀ u : V, u ∉ VH → B (eH i).1 u = 0 := by
    intro i hi0 hi1 u hu
    have huG₂ : u ∈ VG₂ := by
      have : u ∈ VH ∪ VG₂ := by rw [hunion]; exact Finset.mem_univ u
      exact (Finset.mem_union.mp this).resolve_left hu
    have hux : u ≠ x := fun h => hu (h ▸ he0 ▸ (eH 0).2)
    have huy : u ≠ y := fun h => hu (h ▸ he1 ▸ (eH 1).2)
    have hix : (eH i).1 ≠ x := fun h => hi0 (eH.injective (Subtype.ext (h.trans he0.symm)))
    have hiy : (eH i).1 ≠ y := fun h => hi1 (eH.injective (Subtype.ext (h.trans he1.symm)))
    rw [hB_entry, hno_cross (eH i).1 (eH i).2 u huG₂ hix hiy hux huy]; ring
  let w : Fin 14 → ℝ := ![
    -B (eH 1).1 (eH 2).1, -B (eH 2).1 (eH 3).1, -B (eH 3).1 (eH 4).1, -B (eH 4).1 (eH 0).1,
    -B (eH 5).1 (eH 7).1, -B (eH 6).1 (eH 8).1, -B (eH 7).1 (eH 9).1, -B (eH 8).1 (eH 5).1,
    -B (eH 9).1 (eH 6).1, -B (eH 0).1 (eH 5).1, -B (eH 1).1 (eH 6).1, -B (eH 2).1 (eH 7).1,
    -B (eH 3).1 (eH 8).1, -B (eH 4).1 (eH 9).1]
  have hw : ∀ k : Fin 14, 0 < w k := by
    intro k
    fin_cases k <;> dsimp [w] <;>
      linarith [hB_H_neg _ _ (by decide) ((petersenGraph_adj_decide _ _).mpr (by decide))]
  let U := {v : V // v ∉ VH}
  let eFull : (Fin 4 ⊕ Fin 4) ⊕ (Fin 2 ⊕ U) ≃ V :=
    { toFun := fun
        | Sum.inl p => (eH (petersenIdx (Sum.inl p))).1
        | Sum.inr (Sum.inl k) => (eH (petersenIdx (Sum.inr k))).1
        | Sum.inr (Sum.inr u) => u.1
      invFun := fun v =>
        if hv : v ∈ VH then
          match petersenIdxInv (eH.symm ⟨v, hv⟩) with
          | Sum.inl p => Sum.inl p
          | Sum.inr k => Sum.inr (Sum.inl k)
        else Sum.inr (Sum.inr ⟨v, hv⟩)
      left_inv := fun z => by
        rcases z with p | (k | ⟨u, hu⟩)
        · have hm : (eH (petersenIdx (Sum.inl p))).1 ∈ VH := (eH _).2
          simp only [dif_pos hm, Subtype.coe_eta, Equiv.symm_apply_apply]
          have hinv := petersenEquiv.left_inv (Sum.inl p)
          change petersenIdxInv (petersenIdx (Sum.inl p)) = Sum.inl p at hinv
          rw [hinv]
        · have hm : (eH (petersenIdx (Sum.inr k))).1 ∈ VH := (eH _).2
          simp only [dif_pos hm, Subtype.coe_eta, Equiv.symm_apply_apply]
          have hinv := petersenEquiv.left_inv (Sum.inr k)
          change petersenIdxInv (petersenIdx (Sum.inr k)) = Sum.inr k at hinv
          rw [hinv]
        · simp [dif_neg hu]
      right_inv := fun v => by
        by_cases hv : v ∈ VH
        · simp only [dif_pos hv]
          have hinv := petersenEquiv.right_inv (eH.symm ⟨v, hv⟩)
          change petersenIdx (petersenIdxInv (eH.symm ⟨v, hv⟩)) = eH.symm ⟨v, hv⟩ at hinv
          cases hpi : petersenIdxInv (eH.symm ⟨v, hv⟩) with
          | inl p =>
            rw [hpi] at hinv
            simp [hinv]
          | inr k =>
            rw [hpi] at hinv
            simp [hinv]
        · simp [dif_neg hv] }
  have hcard_U : Fintype.card U = Fintype.card V - 10 := by
    have hcard_e : 10 + Fintype.card U = Fintype.card V := by
      have h1 := Fintype.card_congr eFull
      simp only [Fintype.card_sum, Fintype.card_fin] at h1
      omega
    omega
  have hcard_W : Fintype.card (Fin 2 ⊕ U) ≤ Fintype.card V - 8 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have h1 := Fintype.card_congr eFull
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  let B_blk := B.submatrix eFull eFull
  have hB_blk : B_blk.IsHermitian := isHermitian_submatrix B hB eFull
  rw [← signature_reindex eFull B hB]
  let G₂ : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ := B_blk.toBlocks₂₂
  have hG₂ : G₂.IsHermitian := isHermitian_submatrix B_blk hB_blk Sum.inr
  have hG₂_00 : G₂ (Sum.inl 0) (Sum.inl 0) = 0 := by
    simpa [G₂, B_blk, eFull, petersenIdx] using hB_diag (eH 0).1
  have hB_blk_eq : B_blk = Matrix.fromBlocks (petersenAint w)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)
      (Matrix.of fun i z => match z with | Sum.inl j => petersenR w i j | Sum.inr _ => 0)ᵀ
      G₂ := by
    ext p q
    rcases p with (a | a) | (i | u) <;> rcases q with (b | b) | (j | v)
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenAint] <;>
        exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenAint, petersenB, w] <;>
        first | rfl | exact hsym_B _ _ | exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases j <;>
        simp [B_blk, eFull, petersenIdx, petersenR, petersenRU, w] <;>
        first | rfl | exact hsym_B _ _ | exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;>
        (simp [B_blk, eFull, petersenIdx]; exact hB_cross _ (by decide) (by decide) v.1 v.2)
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenAint, petersenB, w] <;>
        first | rfl | exact hsym_B _ _ | exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenAint, petersenC, w] <;>
        first | rfl | exact hsym_B _ _ | exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;> fin_cases j <;>
        simp [B_blk, eFull, petersenIdx, petersenR] <;>
        exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases a <;>
        (simp [B_blk, eFull, petersenIdx]; exact hB_cross _ (by decide) (by decide) v.1 v.2)
    · fin_cases i <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenR, petersenRU, w] <;>
        first | rfl | exact hsym_B _ _ | exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · fin_cases i <;> fin_cases b <;>
        simp [B_blk, eFull, petersenIdx, petersenR] <;>
        exact hB_H_zero _ _ (by decide) (not_petersenGraph_adj _ _ (by decide))
    · rfl
    · rfl
    · fin_cases b <;>
        (simp [B_blk, eFull, petersenIdx]; rw [hsym_B]; exact hB_cross _ (by decide) (by decide) u.1 u.2)
    · fin_cases b <;>
        (simp [B_blk, eFull, petersenIdx]; rw [hsym_B]; exact hB_cross _ (by decide) (by decide) u.1 u.2)
    · rfl
    · rfl
  refine petersen_block_signature_nonpos w hw G₂ hG₂ hG₂_00 B_blk hB_blk hB_blk_eq ?_ ?_
  · intro hdet
    obtain ⟨hm0, hm1, hμ_pos, hmsym⟩ := petersenMH_signs w hw hdet
    let μ : ℝ := petersenMH w 0 1
    let A_schur := G₂ + Matrix.fromBlocks (petersenMH w) (0 : Matrix (Fin 2) U ℝ) 0 0
    have hA_schur_H : A_schur.IsHermitian :=
      hG₂.add (isHermitian_fromBlocks (petersenMH w) (isHermitian_petersenMH w)
        (0 : Matrix U U ℝ) isHermitian_zero)
    let A' : Matrix (Fin 2 ⊕ U) (Fin 2 ⊕ U) ℝ := Matrix.of fun z₁ z₂ =>
      if (z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 1) ∨ (z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 0) then
        G₂ z₁ z₂ + μ
      else G₂ z₁ z₂
    have hG₂_sym : ∀ z₁ z₂, G₂ z₁ z₂ = G₂ z₂ z₁ := fun z₁ z₂ => by
      simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun hG₂.eq z₁) z₂).symm
    have hA'_H : A'.IsHermitian := by
      ext z₁ z₂
      simp only [A', Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
      by_cases h : (z₂ = Sum.inl 0 ∧ z₁ = Sum.inl 1) ∨ (z₂ = Sum.inl 1 ∧ z₁ = Sum.inl 0)
      · have h' : (z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 1) ∨ (z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 0) := by tauto
        simp [h, h', hG₂_sym z₂ z₁]
      · have h' : ¬((z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 1) ∨ (z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 0)) := by tauto
        simp [h, h', hG₂_sym z₂ z₁]
    have hA'_diag : ∀ z : Fin 2 ⊕ U, A' z z = 0 := by
      intro z
      rcases z with i | u
      · fin_cases i <;> simp [A', G₂, B_blk, eFull, petersenIdx, hB_diag]
      · simp [A', G₂, B_blk, eFull, hB_diag]
    have hWeyl : signature A_schur hA_schur_H ≤ signature A' hA'_H := by
      refine signature_mono_of_posSemidef A_schur A' hA_schur_H hA'_H ?_
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hA'_H.sub hA_schur_H, fun z => ?_⟩
      have hdiff : ∀ z₁ z₂ : Fin 2 ⊕ U, (A' - A_schur) z₁ z₂ =
          if z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 0 then -petersenMH w 0 0
          else if z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 1 then -petersenMH w 1 1
          else 0 := by
        intro z₁ z₂
        rcases z₁ with i | u <;> rcases z₂ with j | v
        · fin_cases i <;> fin_cases j <;> simp [A', A_schur, μ, hmsym]
        · simp [A', A_schur]
        · simp [A', A_schur]
        · simp [A', A_schur]
      have hmul : ∀ z₁ : Fin 2 ⊕ U, ((A' - A_schur) *ᵥ z) z₁ =
          if z₁ = Sum.inl 0 then -petersenMH w 0 0 * z (Sum.inl 0)
          else if z₁ = Sum.inl 1 then -petersenMH w 1 1 * z (Sum.inl 1)
          else 0 := by
        intro z₁
        simp only [Matrix.mulVec, dotProduct, hdiff]
        rcases z₁ with i | u
        · fin_cases i
          · simp only [↓reduceIte, true_and, Sum.inl.injEq, zero_ne_one, false_and]
            rw [Finset.sum_eq_single (Sum.inl 0)]
            · simp
            · intro b _ hb; simp [hb]
            · intro h; exact absurd (Finset.mem_univ _) h
          · simp only [Sum.inl.injEq, one_ne_zero, ↓reduceIte, false_and, true_and]
            rw [Finset.sum_eq_single (Sum.inl 1)]
            · simp
            · intro b _ hb; simp [hb]
            · intro h; exact absurd (Finset.mem_univ _) h
        · simp
      have hquad : dotProduct (star z) ((A' - A_schur) *ᵥ z) =
          (-petersenMH w 0 0) * (z (Sum.inl 0)) ^ 2 + (-petersenMH w 1 1) * (z (Sum.inl 1)) ^ 2 := by
        simp only [dotProduct, star_trivial, hmul]
        have h1 : ∀ a : Fin 2 ⊕ U, z a * (if a = Sum.inl 0 then -petersenMH w 0 0 * z (Sum.inl 0)
            else if a = Sum.inl 1 then -petersenMH w 1 1 * z (Sum.inl 1) else 0) =
            (if a = Sum.inl 0 then (-petersenMH w 0 0) * (z (Sum.inl 0)) ^ 2 else 0) +
            (if a = Sum.inl 1 then (-petersenMH w 1 1) * (z (Sum.inl 1)) ^ 2 else 0) := by
          intro a
          rcases a with i | u
          · fin_cases i <;> simp <;> ring
          · simp
        simp_rw [h1]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single (Sum.inl 0)]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [Finset.sum_eq_single (Sum.inl 1)]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; exact absurd (Finset.mem_univ _) h
      rw [hquad]
      nlinarith [sq_nonneg (z (Sum.inl 0)), sq_nonneg (z (Sum.inl 1))]
    let embV : Fin 2 ⊕ U → V := fun z => eFull (Sum.inr z)
    have hembV_inj : Function.Injective embV := fun a b h =>
      Sum.inr.inj (eFull.injective h)
    have hG₂_eq_B : ∀ z₁ z₂ : Fin 2 ⊕ U, G₂ z₁ z₂ = B (embV z₁) (embV z₂) := fun _ _ => rfl
    have hembV_ne_int : ∀ (z : Fin 2 ⊕ U) (i : Fin 10), i ≠ 0 → i ≠ 1 → embV z ≠ (eH i).1 := by
      intro z i hi0 hi1 h
      have h1 : eFull (Sum.inr z) = eFull (Sum.inl (match petersenIdxInv i with | Sum.inl p => p | Sum.inr _ => Sum.inl 0)) := by
        cases hpi : petersenIdxInv i with
        | inl p =>
          have hinv := petersenEquiv.right_inv i
          change petersenIdx (petersenIdxInv i) = i at hinv
          rw [hpi] at hinv
          simpa [eFull, hinv] using h
        | inr k =>
          exfalso
          have hinv := petersenEquiv.right_inv i
          change petersenIdx (petersenIdxInv i) = i at hinv
          rw [hpi] at hinv
          fin_cases k
          · exact hi0 hinv.symm
          · exact hi1 hinv.symm
      exact absurd (eFull.injective h1) (by simp)
    have hA'_noc : MatrixIsNOC A' hA'_H.isSymm := by
      let x' : Fin 2 ⊕ U := Sum.inl 0
      let y' : Fin 2 ⊕ U := Sum.inl 1
      have hlift_avoid : ∀ {p₁ p₂ : Fin 2 ⊕ U}
          (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk p₁ p₂),
          s(x', y') ∉ p.edges →
          ∃ q : (matrixSignedGraph B hB.isSymm).graph.Walk (embV p₁) (embV p₂),
            q.length = p.length ∧
            walkSignProd (matrixSignedGraph B hB.isSymm).sign q =
              walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p ∧
            q.support = p.support.map embV ∧
            q.edges = p.edges.map (Sym2.map embV) := by
        intro p₁ p₂ p
        induction p with
        | nil => intro _; exact ⟨SimpleGraph.Walk.nil, rfl, rfl, rfl, rfl⟩
        | @cons s₁ s₂ s₃ hadj r ihr =>
          intro hnot
          have hne_edge : s(s₁, s₂) ≠ s(x', y') := fun h =>
            hnot (by simp [SimpleGraph.Walk.edges_cons, h])
          have hnot_r : s(x', y') ∉ r.edges := fun hm =>
            hnot (by simp [SimpleGraph.Walk.edges_cons, hm])
          have hnot_xy : ¬((s₁ = Sum.inl 0 ∧ s₂ = Sum.inl 1) ∨ (s₁ = Sum.inl 1 ∧ s₂ = Sum.inl 0)) := by
            rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact hne_edge rfl
            · exact hne_edge Sym2.eq_swap
          have hA'_eq_B : A' s₁ s₂ = B (embV s₁) (embV s₂) := by
            simp [A', hnot_xy, hG₂_eq_B]
          have hadjB : (matrixSignedGraph B hB.isSymm).graph.Adj (embV s₁) (embV s₂) :=
            ⟨fun h => hadj.1 (hembV_inj h), by rw [← hA'_eq_B]; exact hadj.2⟩
          obtain ⟨q', hq'len, hq'sign, hq'supp, hq'edges⟩ := ihr hnot_r
          refine ⟨SimpleGraph.Walk.cons hadjB q', by simp [hq'len], ?_, ?_, ?_⟩
          · simp only [walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
            have h1 : (matrixSignedGraph B hB.isSymm).sign s(embV s₁, embV s₂) =
                (matrixSignedGraph A' hA'_H.isSymm).sign s(s₁, s₂) := by
              simp [matrixSignedGraph, hA'_eq_B]
            rw [h1]; exact congrArg _ hq'sign
          · simp [SimpleGraph.Walk.support_cons, hq'supp]
          · simp [SimpleGraph.Walk.edges_cons, hq'edges]
      intro w₀ c hc hodd
      by_cases hedge : s(x', y') ∈ c.edges
      · have hA'_xy_ne : G₂ x' y' + μ ≠ 0 := by
          have hAdj := SimpleGraph.Walk.adj_of_mem_edges c hedge
          simpa [matrixSignedGraph, matrixGraph, A', x', y'] using hAdj.2
        rcases lt_or_gt_of_ne hA'_xy_ne with hneg | hpos
        · have hBxy_neg : B (embV x') (embV y') < 0 := by
            rw [← hG₂_eq_B]; linarith
          let embG : (matrixSignedGraph A' hA'_H.isSymm).graph ↪g
              (matrixSignedGraph B hB.isSymm).graph :=
            { toFun := embV
              inj' := hembV_inj
              map_rel_iff' := by
                intro z₁ z₂
                constructor
                · rintro ⟨hne, hval⟩
                  refine ⟨fun h => hne (congrArg embV h), ?_⟩
                  by_cases h : (z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 1) ∨ (z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 0)
                  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · simp [matrixSignedGraph, matrixGraph, A']; exact ne_of_lt hneg
                    · simp [matrixSignedGraph, matrixGraph, A', hG₂_sym (Sum.inl 1) (Sum.inl 0)]
                      exact ne_of_lt hneg
                  · simpa [matrixSignedGraph, matrixGraph, A', h, hG₂_eq_B] using hval
                · rintro ⟨hne, hval⟩
                  refine ⟨fun h => hne (hembV_inj h), ?_⟩
                  by_cases h : (z₁ = Sum.inl 0 ∧ z₂ = Sum.inl 1) ∨ (z₁ = Sum.inl 1 ∧ z₂ = Sum.inl 0)
                  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact ne_of_lt hBxy_neg
                    · change B (embV y') (embV x') ≠ 0; rw [hsym_B]; exact ne_of_lt hBxy_neg
                  · simpa [matrixSignedGraph, matrixGraph, A', h, hG₂_eq_B] using hval }
          let c' := c.map embG.toHom
          have hc' : c'.IsCycle := hc.map embG.injective
          have hlen' : c'.length = c.length := SimpleGraph.Walk.length_map embG.toHom c
          have hsign' : ∀ {s t : Fin 2 ⊕ U} (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk s t),
              walkSignProd (matrixSignedGraph B hB.isSymm).sign (p.map embG.toHom) =
                walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p := by
            intro s t p
            induction p with
            | nil => rfl
            | @cons s₁ s₂ _ _ r ihr =>
              simp only [SimpleGraph.Walk.map_cons, walkSignProd, SimpleGraph.Walk.edges_cons,
                List.map_cons, List.prod_cons]
              have h1 : (matrixSignedGraph B hB.isSymm).sign s(embG.toHom s₁, embG.toHom s₂) =
                  (matrixSignedGraph A' hA'_H.isSymm).sign s(s₁, s₂) := by
                change (matrixSignedGraph B hB.isSymm).sign s(embV s₁, embV s₂) = _
                by_cases h : (s₁ = Sum.inl 0 ∧ s₂ = Sum.inl 1) ∨ (s₁ = Sum.inl 1 ∧ s₂ = Sum.inl 0)
                · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · simp [matrixSignedGraph, A', not_lt.mpr hBxy_neg.le, not_lt.mpr hneg.le]
                  · simp [matrixSignedGraph, A', hsym_B (embV y') (embV x'),
                      hG₂_sym (Sum.inl 1) (Sum.inl 0), not_lt.mpr hBxy_neg.le, not_lt.mpr hneg.le]
                · simp [matrixSignedGraph, A', h, hG₂_eq_B]
              rw [h1]; exact congrArg _ ihr
          have hnoc' := hB_noc (embV w₀) c' hc' (hlen'.symm ▸ hodd)
          rw [signedCycleType, ← hlen', ← hsign' c]
          exact hnoc'
        · have hx'_mem : x' ∈ c.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c hedge
          let c₀ := c.rotate x' hx'_mem
          have hc₀ : c₀.IsCycle := hc.rotate hx'_mem
          have hlen₀ : c₀.length = c.length := SimpleGraph.Walk.length_rotate c x' hx'_mem
          have hperm₀ : c₀.edges.Perm c.edges := by
            have h1 : c₀.edges = (c.dropUntil x' hx'_mem).edges ++ (c.takeUntil x' hx'_mem).edges := by
              simp [c₀, SimpleGraph.Walk.rotate, SimpleGraph.Walk.edges_append]
            have h2 : c.edges = (c.takeUntil x' hx'_mem).edges ++ (c.dropUntil x' hx'_mem).edges := by
              conv_lhs => rw [← SimpleGraph.Walk.take_spec c hx'_mem]
              exact SimpleGraph.Walk.edges_append _ _
            rw [h1, h2]; exact List.perm_append_comm
          have hsign₀ : walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c₀ =
              walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c := by
            simp only [walkSignProd]; exact (hperm₀.map _).prod_eq
          have hedge₀ : s(x', y') ∈ c₀.edges := hperm₀.mem_iff.mpr hedge
          have hex_oriented : ∃ (c₁ : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk x' x'),
              c₁.IsCycle ∧ c₁.length = c.length ∧
              walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c₁ =
                walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c ∧
              ∃ (hxy' : (matrixSignedGraph A' hA'_H.isSymm).graph.Adj x' y')
                (p : (matrixSignedGraph A' hA'_H.isSymm).graph.Walk y' x'),
                c₁ = SimpleGraph.Walk.cons hxy' p := by
            cases hc₀_eq : c₀ with
            | nil => exact absurd hc₀_eq hc₀.ne_nil
            | @cons _ z₁ _ h₁ r =>
              by_cases hz₁ : z₁ = y'
              · subst hz₁; exact ⟨c₀, hc₀, hlen₀, hsign₀, h₁, r, hc₀_eq⟩
              · have hr_mem : s(x', y') ∈ r.edges := by
                  rw [hc₀_eq, SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge₀
                  rcases hedge₀ with h | h
                  · exfalso
                    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
                    · exact hz₁ h2.symm
                    · exact h₁.1 h1
                  · exact h
                cases hrr : r.reverse with
                | nil =>
                  have : r = SimpleGraph.Walk.nil := by
                    have := congrArg SimpleGraph.Walk.reverse hrr; simpa using this
                  subst this; exact absurd rfl h₁.1
                | @cons _ z₂ _ h₂' r' =>
                  have hnot_x' : x' ∉ r'.support := by
                    have hnd : r.reverse.support.Nodup := by
                      rw [SimpleGraph.Walk.support_reverse, List.nodup_reverse]
                      have htail := hc₀.support_nodup
                      rw [hc₀_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at htail
                      exact htail
                    rw [hrr, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
                    exact hnd.1
                  have hmem_rr : s(x', y') ∈ r.reverse.edges := by
                    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hr_mem
                  rw [hrr, SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem_rr
                  have hz₂ : z₂ = y' := by
                    rcases hmem_rr with h | h
                    · rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
                      · exact h2.symm
                      · exact absurd h1 h₂'.1
                    · exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges r' h) hnot_x'
                  subst hz₂
                  have hc₀_rev : c₀.reverse =
                      SimpleGraph.Walk.cons h₂' (r'.append (SimpleGraph.Walk.cons h₁.symm SimpleGraph.Walk.nil)) := by
                    rw [hc₀_eq, SimpleGraph.Walk.reverse_cons, hrr, SimpleGraph.Walk.cons_append]
                  refine ⟨c₀.reverse, hc₀.reverse, by simp [hlen₀], ?_, h₂',
                    r'.append (SimpleGraph.Walk.cons h₁.symm SimpleGraph.Walk.nil), hc₀_rev⟩
                  rw [← hsign₀]
                  simp [walkSignProd, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.prod_reverse]
          rcases hex_oriented with ⟨c₁, hc₁, hlen₁, hsign₁, hxy', p, hc₁_eq⟩
          have hnot_p : s(x', y') ∉ p.edges := by
            have hed := hc₁.edges_nodup
            rw [hc₁_eq, SimpleGraph.Walk.edges_cons, List.nodup_cons] at hed
            exact hed.1
          have hp_path : p.IsPath := by
            have htail := hc₁.support_nodup
            rw [hc₁_eq, SimpleGraph.Walk.support_cons, List.tail_cons] at htail
            exact SimpleGraph.Walk.IsPath.mk' htail
          obtain ⟨P, hPlen, hPsign, hPsupp, _⟩ := hlift_avoid p hnot_p
          have hP_path : P.IsPath :=
            SimpleGraph.Walk.IsPath.mk' (by rw [hPsupp]; exact hp_path.support_nodup.map hembV_inj)
          have hnotP : ∀ i : Fin 10, i ≠ 0 → i ≠ 1 → (eH i).1 ∉ P.support := by
            intro i hi0 hi1 hm
            rw [hPsupp, List.mem_map] at hm
            rcases hm with ⟨z, _, hz⟩
            exact hembV_ne_int z i hi0 hi1 hz
          have heH_ne : ∀ i j : Fin 10, i ≠ j → (eH i).1 ≠ (eH j).1 := fun i j hij h =>
            hij (eH.injective (Subtype.ext h))
          have hE : ∀ i j : Fin 10, ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
              petersenGraph.Adj i j → (matrixSignedGraph B hB.isSymm).graph.Adj (eH i).1 (eH j).1 :=
            fun i j hnot hadj => ⟨heH_ne i j hadj.ne, ne_of_lt (hB_H_neg i j hnot hadj)⟩
          have ha1 := hE 0 5 (by decide) ((petersenGraph_adj_decide 0 5).mpr (by decide))
          have ha2 := hE 5 8 (by decide) ((petersenGraph_adj_decide 5 8).mpr (by decide))
          have ha3 := hE 8 3 (by decide) ((petersenGraph_adj_decide 8 3).mpr (by decide))
          have ha4 := hE 3 4 (by decide) ((petersenGraph_adj_decide 3 4).mpr (by decide))
          have ha5 := hE 4 9 (by decide) ((petersenGraph_adj_decide 4 9).mpr (by decide))
          have ha6 := hE 9 6 (by decide) ((petersenGraph_adj_decide 9 6).mpr (by decide))
          have ha7 := hE 6 1 (by decide) ((petersenGraph_adj_decide 6 1).mpr (by decide))
          let cyc : (matrixSignedGraph B hB.isSymm).graph.Walk (eH 0).1 (eH 0).1 :=
            SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons ha2 (SimpleGraph.Walk.cons ha3
              (SimpleGraph.Walk.cons ha4 (SimpleGraph.Walk.cons ha5 (SimpleGraph.Walk.cons ha6
                (SimpleGraph.Walk.cons ha7 P))))))
          have hcyc_supp_nd : cyc.support.tail.Nodup := by
            simp only [cyc, SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_cons,
              List.mem_cons, not_or]
            refine ⟨⟨heH_ne 5 8 (by decide), heH_ne 5 3 (by decide), heH_ne 5 4 (by decide),
              heH_ne 5 9 (by decide), heH_ne 5 6 (by decide), hnotP 5 (by decide) (by decide)⟩,
              ⟨heH_ne 8 3 (by decide), heH_ne 8 4 (by decide), heH_ne 8 9 (by decide),
              heH_ne 8 6 (by decide), hnotP 8 (by decide) (by decide)⟩,
              ⟨heH_ne 3 4 (by decide), heH_ne 3 9 (by decide), heH_ne 3 6 (by decide),
              hnotP 3 (by decide) (by decide)⟩,
              ⟨heH_ne 4 9 (by decide), heH_ne 4 6 (by decide), hnotP 4 (by decide) (by decide)⟩,
              ⟨heH_ne 9 6 (by decide), hnotP 9 (by decide) (by decide)⟩,
              hnotP 6 (by decide) (by decide), hP_path.support_nodup⟩
          have hcyc : cyc.IsCycle := by
            have htrail : cyc.IsTrail := by
              refine ⟨?_⟩
              have hnotE : ∀ (a b : Fin 10), b ≠ 0 → b ≠ 1 → s((eH a).1, (eH b).1) ∉ P.edges :=
                fun a b hb0 hb1 hm => hnotP b hb0 hb1 (SimpleGraph.Walk.snd_mem_support_of_mem_edges P hm)
              have hnotE1 : ∀ (a b : Fin 10), a ≠ 0 → a ≠ 1 → s((eH a).1, (eH b).1) ∉ P.edges :=
                fun a b ha0 ha1 hm => hnotP a ha0 ha1 (SimpleGraph.Walk.fst_mem_support_of_mem_edges P hm)
              simp only [cyc, SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons, not_or]
              refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hnotE 0 5 (by decide) (by decide)⟩,
                ⟨?_, ?_, ?_, ?_, ?_, hnotE1 5 8 (by decide) (by decide)⟩,
                ⟨?_, ?_, ?_, ?_, hnotE1 8 3 (by decide) (by decide)⟩,
                ⟨?_, ?_, ?_, hnotE1 3 4 (by decide) (by decide)⟩,
                ⟨?_, ?_, hnotE1 4 9 (by decide) (by decide)⟩,
                ⟨?_, hnotE1 9 6 (by decide) (by decide)⟩,
                hnotE1 6 1 (by decide) (by decide), hP_path.isTrail.edges_nodup⟩
              all_goals
                intro h
                rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  exact heH_ne _ _ (by decide) (by first | exact h1 | exact h2 | exact h1.symm | exact h2.symm)
            exact ⟨⟨htrail, fun h => absurd (congrArg SimpleGraph.Walk.length h) (by simp [cyc])⟩,
              hcyc_supp_nd⟩
          have hcyc_len : cyc.length = c.length + 6 := by
            have : c₁.length = p.length + 1 := by rw [hc₁_eq, SimpleGraph.Walk.length_cons]
            simp [cyc, hPlen]; omega
          have hcyc_odd : Odd cyc.length := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 3, by omega⟩
          have hsign_neg : ∀ i j : Fin 10, ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
              petersenGraph.Adj i j → (matrixSignedGraph B hB.isSymm).sign s((eH i).1, (eH j).1) = -1 := by
            intro i j hnot hadj
            simp [matrixSignedGraph, not_lt.mpr (hB_H_neg i j hnot hadj).le]
          have hcyc_sign : walkSignProd (matrixSignedGraph B hB.isSymm).sign cyc =
              - walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign c := by
            rw [← hsign₁, hc₁_eq]
            simp only [cyc, walkSignProd, SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons]
            rw [hsign_neg 0 5 (by decide) ((petersenGraph_adj_decide 0 5).mpr (by decide)),
              hsign_neg 5 8 (by decide) ((petersenGraph_adj_decide 5 8).mpr (by decide)),
              hsign_neg 8 3 (by decide) ((petersenGraph_adj_decide 8 3).mpr (by decide)),
              hsign_neg 3 4 (by decide) ((petersenGraph_adj_decide 3 4).mpr (by decide)),
              hsign_neg 4 9 (by decide) ((petersenGraph_adj_decide 4 9).mpr (by decide)),
              hsign_neg 9 6 (by decide) ((petersenGraph_adj_decide 9 6).mpr (by decide)),
              hsign_neg 6 1 (by decide) ((petersenGraph_adj_decide 6 1).mpr (by decide))]
            have hs_xy : (matrixSignedGraph A' hA'_H.isSymm).sign s(x', y') = 1 := by
              simp [matrixSignedGraph, A', x', y', hpos]
            rw [hs_xy]
            change (-1) * ((-1) * ((-1) * ((-1) * ((-1) * ((-1) * ((-1) *
              walkSignProd (matrixSignedGraph B hB.isSymm).sign P)))))) =
              -(1 * walkSignProd (matrixSignedGraph A' hA'_H.isSymm).sign p)
            rw [hPsign]; ring
          have hnoc_cyc := hB_noc (eH 0).1 cyc hcyc hcyc_odd
          rw [signedCycleType, hcyc_len, hcyc_sign] at hnoc_cyc
          have hdiv : (c.length + 6) / 2 = c.length / 2 + 3 := by omega
          rw [hdiv, pow_add] at hnoc_cyc
          have hm3 : (-1 : ℤ) ^ 3 = -1 := by decide
          rw [hm3] at hnoc_cyc
          rw [signedCycleType]
          linarith
      · obtain ⟨q, hqlen, hqsign, hqsupp, hqedges⟩ := hlift_avoid c hedge
        have hqcyc : q.IsCycle := by
          refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
          · rw [hqedges]
            exact hc.edges_nodup.map (Sym2.map.injective hembV_inj)
          · intro hqnil
            have hlen0 : c.length = 0 := by rw [← hqlen, hqnil]; rfl
            cases c with
            | nil => exact hc.ne_nil rfl
            | cons _ _ => simp at hlen0
          · rw [hqsupp, ← List.map_tail]
            exact hc.support_nodup.map hembV_inj
        have hnoc_q := hB_noc (embV w₀) q hqcyc (hqlen.symm ▸ hodd)
        rw [signedCycleType, ← hqlen, ← hqsign]
        exact hnoc_q
    have hA'_le := ih (Fin 2 ⊕ U) hcard_W A' hA'_H hA'_diag hA'_noc
    exact le_trans hWeyl hA'_le
  · have hU_le : Fintype.card U ≤ Fintype.card V - 8 := by omega
    have hU_diag : ∀ u : U, (G₂.submatrix Sum.inr Sum.inr) u u = 0 := fun u => hB_diag u.1
    have hU_noc : MatrixIsNOC (G₂.submatrix Sum.inr Sum.inr)
        (isHermitian_submatrix G₂ hG₂ Sum.inr).isSymm := by
      have hEq : G₂.submatrix Sum.inr Sum.inr = B.submatrix Subtype.val Subtype.val := rfl
      rw [hEq]
      exact matrixIsNOC_submatrix_injective B hB.isSymm hB_noc Subtype.val Subtype.coe_injective
    exact ih U hU_le (G₂.submatrix Sum.inr Sum.inr) (isHermitian_submatrix G₂ hG₂ Sum.inr) hU_diag hU_noc

end SignedGraphs
