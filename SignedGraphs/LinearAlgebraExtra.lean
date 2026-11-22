import SignedGraphs.LinearAlgebra

/-!
# Block-Diagonal, Reindexing, and NOC Preservation Lemmas

Auxiliary matrix-signature and NOC-preservation lemmas shared by
`LocalReductions.lean` and `SchurReductions.lean`.
-/

open Matrix SimpleGraph

namespace SignedGraphs

section MatrixHelpers

lemma isHermitian_fromBlocks {U W : Type*} [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (A : Matrix U U ℝ) (hA : A.IsHermitian)
    (B : Matrix W W ℝ) (hB : B.IsHermitian) :
    (Matrix.fromBlocks A 0 0 B).IsHermitian := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hA.eq i) j
  · simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply]
  · simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hB.eq i) j

theorem signature_reindex {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (e : W ≃ V) (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    signature (A.submatrix e e) (isHermitian_submatrix A hA e) = signature A hA := by
  let φ : (W → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
    { toFun := fun x v => x (e.symm v)
      invFun := fun y w => y (e w)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => by ext w; simp
      right_inv := fun y => by ext v; simp }
  have hquad : ∀ x : W → ℝ,
      dotProduct (φ x) (A *ᵥ φ x) = dotProduct x ((A.submatrix e e) *ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, φ,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Equiv.sum_comp e (fun v => x (e.symm v) * ∑ u : V, A v u * x (e.symm u))]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.symm_apply_apply]
    congr 1
    rw [← Equiv.sum_comp e (fun u => A (e w) u * x (e.symm u))]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp
  have hpos : posInertia (A.submatrix e e) (isHermitian_submatrix A hA e) = posInertia A hA := by
    rw [posInertia_eq_sSup, posInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨U, rfl, hU⟩
      refine ⟨U.map φ.toLinearMap, LinearEquiv.finrank_map_eq φ U, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      rw [hquad x]
      exact hU x hx hx0
    · rintro ⟨U, rfl, hU⟩
      refine ⟨U.map φ.symm.toLinearMap, LinearEquiv.finrank_map_eq φ.symm U, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [← hquad (φ.symm y), LinearEquiv.apply_symm_apply]
      exact hU y hy hy0
  have hneg : negInertia (A.submatrix e e) (isHermitian_submatrix A hA e) = negInertia A hA := by
    rw [negInertia_eq_sSup, negInertia_eq_sSup]
    congr 1; ext n; constructor
    · rintro ⟨U, rfl, hU⟩
      refine ⟨U.map φ.toLinearMap, LinearEquiv.finrank_map_eq φ U, ?_⟩
      rintro y hy hy0
      rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
      rw [hquad x]
      exact hU x hx hx0
    · rintro ⟨U, rfl, hU⟩
      refine ⟨U.map φ.symm.toLinearMap, LinearEquiv.finrank_map_eq φ.symm U, ?_⟩
      rintro x hx hx0
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      rw [← hquad (φ.symm y), LinearEquiv.apply_symm_apply]
      exact hU y hy hy0
  simp only [signature, hpos, hneg]

private lemma finrank_coordSub {V : Type*} [Fintype V] (P : V → Prop) [DecidablePred P] :
    Module.finrank ℝ (Submodule.pi Set.univ fun i : V => if P i then (⊤ : Submodule ℝ ℝ) else ⊥) =
      (Finset.univ.filter P).card := by
  classical
  let e : (Submodule.pi Set.univ fun i : V => if P i then (⊤ : Submodule ℝ ℝ) else ⊥) ≃ₗ[ℝ]
      ({i : V // P i} → ℝ) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun z => ⟨fun i => if h : P i then z ⟨i, h⟩ else 0, by
        intro i _
        by_cases h : P i
        · simp [h]
        · simp [h]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => by
        ext i
        by_cases h : P i
        · simp [h]
        · have hx := x.2 i trivial
          simp [h] at hx
          simp [h, hx]
      right_inv := fun z => by
        ext ⟨i, hi⟩
        simp [hi] }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

private lemma posInertia_diagonal {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℝ) (hD : (Matrix.diagonal d).IsHermitian) :
    posInertia (Matrix.diagonal d) hD = (Finset.univ.filter fun i : V => 0 < d i).card := by
  classical
  rw [posInertia_eq_sSup]
  let S := { n : ℕ | ∃ W : Submodule ℝ (V → ℝ),
    Module.finrank ℝ W = n ∧ ∀ x ∈ W, x ≠ 0 → 0 < dotProduct x ((Matrix.diagonal d) *ᵥ x) }
  have hquad : ∀ x : V → ℝ, dotProduct x ((Matrix.diagonal d) *ᵥ x) = ∑ i : V, d i * (x i) ^ 2 := by
    intro x
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hbdd : BddAbove S := ⟨Fintype.card V, by
    rintro n ⟨W, rfl, _⟩
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W⟩
  let Wpos : Submodule ℝ (V → ℝ) :=
    Submodule.pi Set.univ fun i : V => if 0 < d i then ⊤ else ⊥
  let Wnonpos : Submodule ℝ (V → ℝ) :=
    Submodule.pi Set.univ fun i : V => if ¬ (0 < d i) then ⊤ else ⊥
  have hmem : (Finset.univ.filter fun i : V => 0 < d i).card ∈ S := by
    refine ⟨Wpos, finrank_coordSub (fun i => 0 < d i), fun y hy hy0 => ?_⟩
    rw [hquad]
    have hy_zero : ∀ i, ¬ (0 < d i) → y i = 0 := by
      intro i hi
      have := hy i trivial
      simp [hi] at this
      exact this
    have hex : ∃ i, 0 < d i ∧ y i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
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
    rw [hquad] at hpos
    have hle : ∑ i : V, d i * (y i) ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : 0 < d i
      · have hmemi := hyN i trivial
        simp [hi] at hmemi
        simp [hmemi]
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (sq_nonneg _)
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W Wnonpos
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hle_card : Module.finrank ℝ (W ⊔ Wnonpos) ≤ Fintype.card V := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le (W ⊔ Wnonpos)
  have hnonpos_card : Module.finrank ℝ Wnonpos = (Finset.univ.filter fun i : V => ¬ (0 < d i)).card :=
    finrank_coordSub (fun i => ¬ (0 < d i))
  have hpart : (Finset.univ.filter fun i : V => 0 < d i).card +
      (Finset.univ.filter fun i : V => ¬ (0 < d i)).card = Fintype.card V := by
    rw [Finset.card_filter_add_card_filter_not]
  omega

private lemma negInertia_diagonal {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℝ) (hD : (Matrix.diagonal d).IsHermitian) :
    negInertia (Matrix.diagonal d) hD = (Finset.univ.filter fun i : V => d i < 0).card := by
  have hnegD : (Matrix.diagonal (-d)).IsHermitian := by
    rw [Matrix.diagonal_neg]
    exact isHermitian_neg _ hD
  have hpos_neg : posInertia (Matrix.diagonal (-d)) hnegD =
      (Finset.univ.filter fun i : V => 0 < -d i).card := posInertia_diagonal (-d) hnegD
  have hcard : (Finset.univ.filter fun i : V => 0 < -d i).card =
      (Finset.univ.filter fun i : V => d i < 0).card := by
    congr 1; ext i; simp [neg_pos]
  rw [← hcard, ← hpos_neg]
  rw [negInertia_eq_sSup, posInertia_eq_sSup]
  congr 1; ext n; constructor
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W, rfl, fun x hx hx0 => ?_⟩
    have := hW x hx hx0
    simpa [Matrix.diagonal_neg, Matrix.neg_mulVec, dotProduct_neg] using this
  · rintro ⟨W, rfl, hW⟩
    refine ⟨W, rfl, fun x hx hx0 => ?_⟩
    have := hW x hx hx0
    simpa [Matrix.diagonal_neg, Matrix.neg_mulVec, dotProduct_neg] using this

theorem signature_fromBlocks {U W : Type*} [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (A : Matrix U U ℝ) (hA : A.IsHermitian)
    (B : Matrix W W ℝ) (hB : B.IsHermitian) :
    signature (Matrix.fromBlocks A 0 0 B) (isHermitian_fromBlocks A hA B hB) =
      signature A hA + signature B hB := by
  let U₁ : Matrix U U ℝ := (hA.eigenvectorUnitary : Matrix U U ℝ)
  let U₂ : Matrix W W ℝ := (hB.eigenvectorUnitary : Matrix W W ℝ)
  have hU₁_left : U₁ᵀ * U₁ = 1 := by
    have h : star U₁ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hU₂_left : U₂ᵀ * U₂ = 1 := by
    have h : star U₂ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hB.eigenvectorUnitary.prop
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hU₁_det : IsUnit U₁.det := by
    refine isUnit_of_mul_eq_one U₁.det U₁.det ?_
    calc U₁.det * U₁.det = U₁ᵀ.det * U₁.det := by rw [Matrix.det_transpose]
      _ = (U₁ᵀ * U₁).det := by rw [← Matrix.det_mul]
      _ = 1 := by rw [hU₁_left, Matrix.det_one]
  have hU₂_det : IsUnit U₂.det := by
    refine isUnit_of_mul_eq_one U₂.det U₂.det ?_
    calc U₂.det * U₂.det = U₂ᵀ.det * U₂.det := by rw [Matrix.det_transpose]
      _ = (U₂ᵀ * U₂).det := by rw [← Matrix.det_mul]
      _ = 1 := by rw [hU₂_left, Matrix.det_one]
  let P : Matrix (U ⊕ W) (U ⊕ W) ℝ := Matrix.fromBlocks U₁ 0 0 U₂
  have hP_left : Pᵀ * P = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        ← Matrix.mul_apply, hU₁_left, hU₂_left]
  have hP_det : IsUnit P.det := by
    refine isUnit_of_mul_eq_one P.det P.det ?_
    calc P.det * P.det = Pᵀ.det * P.det := by rw [Matrix.det_transpose]
      _ = (Pᵀ * P).det := by rw [← Matrix.det_mul]
      _ = 1 := by rw [hP_left, Matrix.det_one]
  have hspec₁ : U₁ᵀ * A * U₁ = Matrix.diagonal hA.eigenvalues := by
    have h := hA.spectral_theorem
    change A = U₁ * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U₁ at h
    have hstar : star U₁ = U₁ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial U₁
    rw [hstar] at h
    have hAeq : A = U₁ * Matrix.diagonal hA.eigenvalues * U₁ᵀ := by simpa using h
    calc U₁ᵀ * A * U₁ = U₁ᵀ * (U₁ * Matrix.diagonal hA.eigenvalues * U₁ᵀ) * U₁ := by rw [hAeq]
      _ = (U₁ᵀ * U₁) * Matrix.diagonal hA.eigenvalues * (U₁ᵀ * U₁) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal hA.eigenvalues := by rw [hU₁_left, Matrix.one_mul, Matrix.mul_one]
  have hspec₂ : U₂ᵀ * B * U₂ = Matrix.diagonal hB.eigenvalues := by
    have h := hB.spectral_theorem
    change B = U₂ * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star U₂ at h
    have hstar : star U₂ = U₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial U₂
    rw [hstar] at h
    have hBeq : B = U₂ * Matrix.diagonal hB.eigenvalues * U₂ᵀ := by simpa using h
    calc U₂ᵀ * B * U₂ = U₂ᵀ * (U₂ * Matrix.diagonal hB.eigenvalues * U₂ᵀ) * U₂ := by rw [hBeq]
      _ = (U₂ᵀ * U₂) * Matrix.diagonal hB.eigenvalues * (U₂ᵀ * U₂) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal hB.eigenvalues := by rw [hU₂_left, Matrix.one_mul, Matrix.mul_one]
  let d : U ⊕ W → ℝ := Sum.elim hA.eigenvalues hB.eigenvalues
  have hP_congr : Pᵀ * Matrix.fromBlocks A 0 0 B * P = Matrix.diagonal d := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have h := congr_fun (congr_fun hspec₁ i) j
      simpa [P, d, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Matrix.diagonal_apply] using h
    · simp [P, d, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Matrix.diagonal_apply]
    · simp [P, d, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Matrix.diagonal_apply]
    · have h := congr_fun (congr_fun hspec₂ i) j
      simpa [P, d, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Matrix.diagonal_apply] using h
  have hD : (Matrix.diagonal d).IsHermitian := by
    rw [← hP_congr]
    exact isHermitian_congr _ P (isHermitian_fromBlocks A hA B hB)
  have hD₁ : (Matrix.diagonal hA.eigenvalues).IsHermitian := by
    rw [← hspec₁]
    exact isHermitian_congr A U₁ hA
  have hD₂ : (Matrix.diagonal hB.eigenvalues).IsHermitian := by
    rw [← hspec₂]
    exact isHermitian_congr B U₂ hB
  have hsAB : signature (Matrix.fromBlocks A 0 0 B) (isHermitian_fromBlocks A hA B hB) =
      signature (Matrix.diagonal d) hD := by
    have hc := signature_congr (Matrix.fromBlocks A 0 0 B) P (isHermitian_fromBlocks A hA B hB) hP_det
    simpa [hP_congr] using hc.symm
  have hsA : signature A hA = signature (Matrix.diagonal hA.eigenvalues) hD₁ := by
    have hc := signature_congr A U₁ hA hU₁_det
    simpa [hspec₁] using hc.symm
  have hsB : signature B hB = signature (Matrix.diagonal hB.eigenvalues) hD₂ := by
    have hc := signature_congr B U₂ hB hU₂_det
    simpa [hspec₂] using hc.symm
  rw [hsAB, hsA, hsB]
  simp only [signature, posInertia_diagonal, negInertia_diagonal]
  have hcard_pos : (Finset.univ.filter fun k : U ⊕ W => 0 < d k).card =
      (Finset.univ.filter fun i : U => 0 < hA.eigenvalues i).card +
      (Finset.univ.filter fun j : W => 0 < hB.eigenvalues j).card := by
    rw [← Finset.card_image_of_injective _ Sum.inl_injective,
        ← Finset.card_image_of_injective _ Sum.inr_injective,
        ← Finset.card_union_of_disjoint]
    · congr 1; ext k; rcases k with i | j <;> simp [d]
    · rw [Finset.disjoint_left]
      rintro _ h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, h⟩
      cases h
  have hcard_neg : (Finset.univ.filter fun k : U ⊕ W => d k < 0).card =
      (Finset.univ.filter fun i : U => hA.eigenvalues i < 0).card +
      (Finset.univ.filter fun j : W => hB.eigenvalues j < 0).card := by
    rw [← Finset.card_image_of_injective _ Sum.inl_injective,
        ← Finset.card_image_of_injective _ Sum.inr_injective,
        ← Finset.card_union_of_disjoint]
    · congr 1; ext k; rcases k with i | j <;> simp [d]
    · rw [Finset.disjoint_left]
      rintro _ h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, h⟩
      cases h
  rw [hcard_pos, hcard_neg]
  omega

lemma signature_one_by_one_le_one (c : ℝ)
    (hM : (fun _ _ : Unit => c).IsHermitian) :
    signature (fun _ _ : Unit => c) hM ≤ 1 := by
  have hpos : posInertia (fun _ _ : Unit => c) hM ≤ 1 := by
    rw [posInertia_eq_sSup]
    refine csSup_le ⟨0, ⊥, finrank_bot ℝ (Unit → ℝ), fun x hx hx0 => absurd (Submodule.mem_bot.mp hx) hx0⟩ ?_
    rintro n ⟨W, rfl, _⟩
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W
  simp only [signature]
  omega

lemma signature_one_by_one_nonpos (c : ℝ) (hc : c ≤ 0)
    (hM : (fun _ _ : Unit => c).IsHermitian) :
    signature (fun _ _ : Unit => c) hM ≤ 0 := by
  have hpos : posInertia (fun _ _ : Unit => c) hM = 0 := by
    rw [posInertia_eq_sSup]
    refine le_antisymm (csSup_le ⟨0, ⊥, finrank_bot ℝ (Unit → ℝ), fun x hx hx0 =>
        absurd (Submodule.mem_bot.mp hx) hx0⟩ ?_) (Nat.zero_le _)
    rintro n ⟨W, rfl, hW⟩
    by_cases hbot : W = ⊥
    · simp [hbot]
    · obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
        by_contra hnone
        push_neg at hnone
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        exact Submodule.mem_bot.mpr (hnone x hx)
      have hgt := hW x hxW hx0
      have hle : dotProduct x ((fun _ _ : Unit => c) *ᵥ x) ≤ 0 := by
        simp only [dotProduct, Matrix.mulVec, Finset.univ_unique, Finset.sum_singleton]
        nlinarith [sq_nonneg (x ())]
      linarith
  simp only [signature, hpos]
  omega

lemma signature_one_by_one_le_zero_iff (c : ℝ)
    (hM : (fun _ _ : Unit => c).IsHermitian) :
    signature (fun _ _ : Unit => c) hM ≤ 0 → c ≤ 0 := by
  intro hs
  by_contra hc
  push_neg at hc
  have hpos : 1 ≤ posInertia (fun _ _ : Unit => c) hM := by
    rw [posInertia_eq_sSup]
    refine le_csSup ⟨1, by rintro n ⟨W, rfl, _⟩; simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W⟩ ?_
    refine ⟨⊤, by simp [Module.finrank_fintype_fun_eq_card], fun x _ hx0 => ?_⟩
    have hx : x () ≠ 0 := fun h => hx0 (by ext ⟨⟩; exact h)
    simp only [dotProduct, Matrix.mulVec, Finset.univ_unique, Finset.sum_singleton]
    nlinarith [sq_pos_of_ne_zero hx]
  have hneg : negInertia (fun _ _ : Unit => c) hM = 0 := by
    rw [negInertia_eq_sSup]
    refine le_antisymm (csSup_le ⟨0, ⊥, finrank_bot ℝ (Unit → ℝ), fun x hx hx0 =>
        absurd (Submodule.mem_bot.mp hx) hx0⟩ ?_) (Nat.zero_le _)
    rintro n ⟨W, rfl, hW⟩
    by_cases hbot : W = ⊥
    · simp [hbot]
    · obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
        by_contra hnone; push_neg at hnone; apply hbot
        rw [eq_bot_iff]; intro x hx; exact Submodule.mem_bot.mpr (hnone x hx)
      have hlt := hW x hxW hx0
      have hge : 0 ≤ dotProduct x ((fun _ _ : Unit => c) *ᵥ x) := by
        simp only [dotProduct, Matrix.mulVec, Finset.univ_unique, Finset.sum_singleton]
        nlinarith [sq_nonneg (x ())]
      linarith
  simp only [signature, hneg] at hs
  omega

lemma signature_two_by_two_offdiag (b c : ℝ) (hb : b ≠ 0)
    (hH : (!![0, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) :
    signature (!![0, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) hH = 0 := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, b; b, 0]
  have hJ : J.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.conjTranspose_apply]
  let k : ℝ := c / (2 * b)
  let C : Matrix (Fin 2) (Fin 2) ℝ := !![1, k; 0, 1]
  have hC_det : IsUnit C.det := by
    have hdet : C.det = 1 := by simp [C, Matrix.det_fin_two]
    rw [hdet]
    exact isUnit_one
  have hcongr : Cᵀ * J * C = !![0, b; b, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, J, k, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    field_simp [hb]
    ring
  have hsJ : signature J hJ = 0 := by
    refine signature_eq_zero_of_bipartite J hJ (fun i => by fin_cases i <;> simp [J]) ?_
    refine ⟨id, fun {u v} huv => ?_⟩
    exact huv.1
  have hc := signature_congr J C hJ hC_det
  simpa [hcongr, hsJ] using hc

lemma matrixIsNOC_submatrix_injective {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (A : Matrix V V ℝ) (hA : A.Symmetric) (hnoc : MatrixIsNOC A hA)
    (f : W → V) (hf : Function.Injective f)
    (hAf : (A.submatrix f f).Symmetric) :
    MatrixIsNOC (A.submatrix f f) hAf := by
  intro w c hc hodd
  let emb : matrixGraph (A.submatrix f f) hAf ↪g matrixGraph A hA :=
    { toFun := f
      inj' := hf
      map_rel_iff' := by
        intro a b
        simp [matrixGraph, hf.ne_iff] }
  let c' : (matrixGraph A hA).Walk (f w) (f w) := c.map emb.toHom
  have hc' : c'.IsCycle := hc.map emb.injective
  have hodd' : Odd c'.length := by simpa [c'] using hodd
  have hsign : walkSignProd (matrixSign A) c' = walkSignProd (matrixSign (A.submatrix f f)) c := by
    clear hc hodd hc' hodd'
    induction c with
    | nil => simp [c', walkSignProd]
    | @cons u x v h p ih =>
      simp only [c', SimpleGraph.Walk.map_cons, walkSignProd, SimpleGraph.Walk.edges_cons,
        List.map_cons, List.prod_cons]
      have h1 : matrixSign A s(emb u, emb x) = matrixSign (A.submatrix f f) s(u, x) := by
        simp [matrixSign, emb]
      rw [h1]
      congr 1
      exact ih
  have hnoc' := hnoc (f w) c' hc' hodd'
  simpa [signedCycleType, c', hsign] using hnoc'

lemma matrixIsNOC_diagonal_congr {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.Symmetric) (hnoc : MatrixIsNOC A hA)
    (d : V → ℝ) (hd : ∀ u, d u ≠ 0)
    (hB : (Matrix.diagonal d * A * Matrix.diagonal d).Symmetric) :
    MatrixIsNOC (Matrix.diagonal d * A * Matrix.diagonal d) hB := by
  let B := Matrix.diagonal d * A * Matrix.diagonal d
  let emb : matrixGraph B hB ↪g matrixGraph A hA :=
    { toFun := id
      inj' := Function.injective_id
      map_rel_iff' := by
        intro a b
        simp [matrixGraph, B, Matrix.diagonal_mul, Matrix.mul_diagonal, hd a, hd b] }
  let S : Set V := {u : V | d u < 0}
  intro v c hc hodd
  let c' : (matrixGraph A hA).Walk v v := c.map emb.toHom
  have hc' : c'.IsCycle := hc.map emb.injective
  have hodd' : Odd c'.length := by simpa [c'] using hodd
  have hsign : walkSignProd (matrixSign B) c = walkSignProd (switchSign S (matrixSign A)) c' := by
    clear hc hodd hc' hodd'
    induction c with
    | nil => simp [c', walkSignProd]
    | @cons u x w h p ih =>
      simp only [c', SimpleGraph.Walk.map_cons, walkSignProd, SimpleGraph.Walk.edges_cons,
        List.map_cons, List.prod_cons]
      have hux : A u x ≠ 0 := h.2 |> fun hb => by
        simpa [B, Matrix.diagonal_mul, Matrix.mul_diagonal, hd u, hd x] using hb
      have h1 : matrixSign B s(u, x) = switchSign S (matrixSign A) s(emb u, emb x) := by
        simp only [emb, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, id_eq,
          switchSign, Sym2.lift_mk, matrixSign, B, Matrix.diagonal_mul, Matrix.mul_diagonal, S,
          Set.mem_setOf_eq]
        have hdu : d u < 0 ∨ 0 < d u := lt_or_gt_of_ne (hd u)
        have hdx : d x < 0 ∨ 0 < d x := lt_or_gt_of_ne (hd x)
        have hAx : A u x < 0 ∨ 0 < A u x := lt_or_gt_of_ne hux
        rcases hdu with hu | hu <;> rcases hdx with hx | hx <;> rcases hAx with ha | ha
        · have hpos : 0 < d u * A u x * d x := by nlinarith
          simp [hpos, hu, hx, not_lt.mpr ha.le]
        · have hneg : ¬ (0 < d u * A u x * d x) := by nlinarith
          simp [hneg, hu, hx, ha]
        · have hneg : ¬ (0 < d u * A u x * d x) := by nlinarith
          simp [hneg, hu, not_lt.mpr hx.le, not_lt.mpr ha.le]
        · have hpos : 0 < d u * A u x * d x := by nlinarith
          simp [hpos, hu, not_lt.mpr hx.le, ha]
        · have hneg : ¬ (0 < d u * A u x * d x) := by nlinarith
          simp [hneg, not_lt.mpr hu.le, hx, not_lt.mpr ha.le]
        · have hpos : 0 < d u * A u x * d x := by nlinarith
          simp [hpos, not_lt.mpr hu.le, hx, ha]
        · have hpos : 0 < d u * A u x * d x := by nlinarith
          simp [hpos, not_lt.mpr hu.le, not_lt.mpr hx.le, not_lt.mpr ha.le]
        · have hneg : ¬ (0 < d u * A u x * d x) := by nlinarith
          simp [hneg, not_lt.mpr hu.le, not_lt.mpr hx.le, ha]
      rw [h1, ih]
  rw [signedCycleType, hsign, walkSignProd_switch]
  simpa [signedCycleType, c'] using hnoc v c' hc' hodd'

end MatrixHelpers

end SignedGraphs
