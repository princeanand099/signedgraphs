import SignedGraphs.LocalReductions
import SignedGraphs.SchurReductions
import SignedGraphs.SPQR
import SignedGraphs.GraphTools
import SignedGraphs.Classification
import SignedGraphs.BipartiteLeaves
import SignedGraphs.Challenge

/-!
# Proofs of Theorem 1.2 and Corollary 1.3 (Section 6)

Combines Sections 2–5 via the SPQR-tree decomposition to prove `theorem_1_2`
and `corollary_1_3`.
-/

open Matrix SimpleGraph

namespace SignedGraphs

section Theorem12Helpers

private lemma signature_eq_of_eq_mat {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    signature A hA = signature B hB := by
  subst h; rfl

private lemma signature_zero_of_bipartite_local {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (hdiag : ∀ u, A u u = 0)
    (hbip : (matrixGraph A hA.isSymm).IsBipartite) :
    signature A hA = 0 := by
  rcases hbip with ⟨f⟩
  let d : V → ℝ := fun u => if f u = 0 then 1 else -1
  let D : Matrix V V ℝ := Matrix.diagonal d
  have hd_ne : ∀ u, d u ≠ 0 := fun u => by dsimp [d]; split_ifs <;> norm_num
  have hD_det : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun u _ => hd_ne u)
  have hneg : Dᵀ * A * D = -A := by
    ext u v
    simp only [D, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.neg_apply]
    by_cases huv : u = v
    · subst huv; simp [hdiag u]
    · by_cases hAuv : A u v = 0
      · simp [hAuv]
      · have hadj : (matrixGraph A hA.isSymm).Adj u v := ⟨huv, hAuv⟩
        have hcol : f u ≠ f v := f.valid hadj
        have hmul : d u * d v = -1 := by
          dsimp [d]
          fin_cases hfu : f u <;> fin_cases hfv : f v <;> simp_all
        calc
          d u * A u v * d v = (d u * d v) * A u v := by ring
          _ = -A u v := by rw [hmul]; ring
  have h1 : signature (Dᵀ * A * D) (isHermitian_congr A D hA) = signature A hA :=
    signature_congr A D hA hD_det
  have h2 : signature (Dᵀ * A * D) (isHermitian_congr A D hA) =
      signature (-A) (isHermitian_neg A hA) :=
    signature_eq_of_eq_mat _ _ hneg
  have h3 : signature (-A) (isHermitian_neg A hA) = -signature A hA :=
    signature_neg A hA
  omega

private lemma walk_exits_finset_last {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (S : Finset V) {a b : V} (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ (u v : V), u ∈ S ∧ v ∉ S ∧ G.Adj u v ∧
      ∃ q : G.Walk a v,
        (∀ x ∈ q.support, x ∈ p.support) ∧
        (∀ x ∈ q.support, x ≠ v → x ∈ S) := by
  induction p with
  | nil => exact absurd ha hb
  | @cons x y z hadj r ih =>
    by_cases hy : y ∈ S
    · obtain ⟨u, v, hu, hv, huv, q, hq_sub, hq_in⟩ := ih hy hb
      refine ⟨u, v, hu, hv, huv, SimpleGraph.Walk.cons hadj q, ?_, ?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · exact Or.inl rfl
        · exact Or.inr (hq_sub w hw)
      · intro w hw hne
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ha
        · exact hq_in w hw hne
    · refine ⟨x, y, ha, hy, hadj, SimpleGraph.Walk.cons hadj .nil, ?_, ?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact SimpleGraph.Walk.start_mem_support _
        · simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support]
      · intro w hw hne
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ha
        · exact absurd rfl hne

private def liftWalkToInduce {V : Type*} {G : SimpleGraph V} (S : Set V) :
    ∀ {a b : V} (p : G.Walk a b),
      (∀ x ∈ p.support, x ∈ S) →
      (ha : a ∈ S) → (hb : b ∈ S) →
      (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons hadj r, hsub, _, hb =>
    let hv : _ ∈ S := hsub _ (by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
    .cons hadj (liftWalkToInduce S r (fun x hx => hsub x (by simp [SimpleGraph.Walk.support_cons, hx])) hv hb)

private lemma liftWalkToInduce_mem_support {V : Type*} {G : SimpleGraph V} (S : Set V)
    {a b : V} (p : G.Walk a b) (hsub : ∀ x ∈ p.support, x ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (w : S) :
    w ∈ (liftWalkToInduce S p hsub ha hb).support ↔ w.1 ∈ p.support := by
  induction p with
  | nil =>
    simp [liftWalkToInduce, Subtype.ext_iff]
  | cons hadj r ih =>
    simp only [liftWalkToInduce, SimpleGraph.Walk.support_cons, List.mem_cons, Subtype.ext_iff]
    rw [ih]

private def petersenAut_of_fun (f g : Fin 10 → Fin 10)
    (hfg : ∀ i, f (g i) = i) (hgf : ∀ i, g (f i) = i)
    (hadj : ∀ i j, petersenGraph.Adj (f i) (f j) ↔ petersenGraph.Adj i j) :
    petersenGraph ≃g petersenGraph where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  map_rel_iff' := hadj _ _

private def pRotFun : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
private def pRotInv : Fin 10 → Fin 10 := ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8]
private def pReflFun : Fin 10 → Fin 10 := ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7]
private def pSpokeFun : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]
private def pSpokeInv : Fin 10 → Fin 10 := ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6]
private def pInnerFun : Fin 10 → Fin 10 := ![4, 3, 2, 7, 9, 0, 8, 1, 5, 6]
private def pInnerInv : Fin 10 → Fin 10 := ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4]

private def pRot : petersenGraph ≃g petersenGraph :=
  petersenAut_of_fun pRotFun pRotInv (by decide) (by decide) (by decide)

private def pRefl : petersenGraph ≃g petersenGraph :=
  petersenAut_of_fun pReflFun pReflFun (by decide) (by decide) (by decide)

private def pSpoke : petersenGraph ≃g petersenGraph :=
  petersenAut_of_fun pSpokeFun pSpokeInv (by decide) (by decide) (by decide)

private def pInner : petersenGraph ≃g petersenGraph :=
  petersenAut_of_fun pInnerFun pInnerInv (by decide) (by decide) (by decide)

private def pRotPow : ℕ → (petersenGraph ≃g petersenGraph)
  | 0 => SimpleGraph.Iso.refl
  | k + 1 => (pRotPow k).trans pRot

private lemma petersenGraph_edge_transitive (a b : Fin 10) (hab : petersenGraph.Adj a b) :
    ∃ φ : petersenGraph ≃g petersenGraph, φ a = 0 ∧ φ b = 1 := by
  let rotBase (k : ℕ) : petersenGraph ≃g petersenGraph := pRotPow ((5 - k % 5) % 5)
  by_cases ha : a.val < 5
  · by_cases hb : b.val < 5
    · by_cases h1 : b.val = (a.val + 1) % 5
      · refine ⟨rotBase a.val, ?_, ?_⟩ <;>
        (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun,
          SimpleGraph.Iso.refl])
      · refine ⟨(rotBase b.val).trans pRefl, ?_, ?_⟩ <;>
        (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun, pRefl, pReflFun,
          SimpleGraph.Iso.refl, petersenGraph_adj_decide])
    · refine ⟨(rotBase a.val).trans pSpoke, ?_, ?_⟩ <;>
      (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun, pSpoke, pSpokeFun,
        SimpleGraph.Iso.refl, petersenGraph_adj_decide])
  · by_cases hb : b.val < 5
    · refine ⟨((rotBase b.val).trans pSpoke).trans pRefl, ?_, ?_⟩ <;>
      (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun, pSpoke, pSpokeFun,
        pRefl, pReflFun, SimpleGraph.Iso.refl, petersenGraph_adj_decide])
    · by_cases h1 : (b.val - 5) = ((a.val - 5) + 2) % 5
      · refine ⟨(rotBase (a.val - 5)).trans pInner, ?_, ?_⟩ <;>
        (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun, pInner, pInnerFun,
          SimpleGraph.Iso.refl, petersenGraph_adj_decide])
      · refine ⟨((rotBase (b.val - 5)).trans pInner).trans pRefl, ?_, ?_⟩ <;>
        (fin_cases a <;> fin_cases b <;> simp_all [rotBase, pRotPow, pRot, pRotFun, pInner, pInnerFun,
          pRefl, pReflFun, SimpleGraph.Iso.refl, petersenGraph_adj_decide])

private lemma k4_pair_equiv (a b : Fin 4) (hab : a ≠ b) :
    ∃ φ : Fin 4 ≃ Fin 4, φ a = 0 ∧ φ b = 1 := by
  let φ₁ : Fin 4 ≃ Fin 4 := Equiv.swap a 0
  have hb₁ : φ₁ b ≠ 0 := by
    intro h
    have : φ₁ b = φ₁ a := by simp [φ₁, h]
    exact hab (φ₁.injective this).symm
  let φ₂ : Fin 4 ≃ Fin 4 := Equiv.swap (φ₁ b) 1
  refine ⟨φ₁.trans φ₂, ?_, ?_⟩
  · simp only [Equiv.trans_apply, φ₁, Equiv.swap_apply_left, φ₂]
    exact Equiv.swap_apply_of_ne_of_ne hb₁.symm (by decide)
  · simp only [Equiv.trans_apply, φ₂, Equiv.swap_apply_left]

private lemma path_concat_three_isPath {V : Type*} {G : SimpleGraph V} {a₁ b₁ b₂ a₂ : V}
    (p₁ : G.Walk a₁ b₁) (r : G.Walk b₁ b₂) (p₂ : G.Walk a₂ b₂)
    (hp₁ : p₁.IsPath) (hr : r.IsPath) (hp₂ : p₂.IsPath)
    (hdisj12 : Disjoint p₁.support.toFinset p₂.support.toFinset)
    (hdisj1r : ∀ x ∈ p₁.support, x ≠ b₁ → x ∉ r.support)
    (hdisj2r : ∀ x ∈ p₂.support, x ≠ b₂ → x ∉ r.support) :
    ((p₁.append r).append p₂.reverse).IsPath := by
  classical
  rw [SimpleGraph.Walk.isPath_def]
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append]
  have hr_cons : r.support = b₁ :: r.support.tail := by cases r <;> simp
  have hp2_cons : p₂.reverse.support = b₂ :: p₂.reverse.support.tail := by
    cases h : p₂.reverse <;> simp
  have h1r : (p₁.support ++ r.support.tail).Nodup := by
    rw [List.nodup_append]
    refine ⟨hp₁.support_nodup, ?_, ?_⟩
    · have hnd := hr.support_nodup
      rw [hr_cons, List.nodup_cons] at hnd
      exact hnd.2
    · intro x hx y hy hxy
      subst hxy
      have hnd := hr.support_nodup
      rw [hr_cons, List.nodup_cons] at hnd
      have hne : x ≠ b₁ := fun h => hnd.1 (h ▸ hy)
      have hxr : x ∈ r.support := by rw [hr_cons]; exact List.mem_cons_of_mem _ hy
      exact hdisj1r x hx hne hxr
  rw [List.nodup_append]
  refine ⟨h1r, ?_, ?_⟩
  · have hnd := hp₂.reverse.support_nodup
    rw [hp2_cons, List.nodup_cons] at hnd
    exact hnd.2
  · intro x hx y hy hxy
    subst hxy
    have hnd := hp₂.reverse.support_nodup
    rw [hp2_cons, List.nodup_cons] at hnd
    have hne : x ≠ b₂ := fun h => hnd.1 (h ▸ hy)
    have hxp2 : x ∈ p₂.support := by
      have : x ∈ p₂.reverse.support := by rw [hp2_cons]; exact List.mem_cons_of_mem _ hy
      rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
    rw [List.mem_append] at hx
    rcases hx with hxp1 | hxr
    · exact Finset.disjoint_left.mp hdisj12 (List.mem_toFinset.mpr hxp1) (List.mem_toFinset.mpr hxp2)
    · have hxr' : x ∈ r.support := by rw [hr_cons]; exact List.mem_cons_of_mem _ hxr
      exact hdisj2r x hxp2 hne hxr'

/-- In a 2-connected graph `G` with an R-leaf decomposition `d`, `G₂ = G[VG₂]` has at least one
simple `(x, y)`-path. -/
private lemma exists_path_in_G₂ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (d : RLeafDecomp G) :
    let hx : d.x ∈ (d.VG₂ : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
    let hy : d.y ∈ (d.VG₂ : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
    ∃ q : (G.induce (d.VG₂ : Set V)).Walk ⟨d.x, hx⟩ ⟨d.y, hy⟩, q.IsPath := by
  classical
  have hx_mem : d.x ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  have hy_mem : d.y ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  let G₂ : SimpleGraph d.VG₂ := G.induce (d.VG₂ : Set V)
  have hG₂_int : (d.VG₂ \ {d.x, d.y}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff]
    have hle : ({d.x, d.y} ∩ d.VG₂).card ≤ 2 :=
      le_trans (Finset.card_le_card Finset.inter_subset_left) (by rw [Finset.card_pair d.hxy])
    have := d.hcardG₂
    omega
  rcases hG₂_int with ⟨z, hz_int⟩
  have hz_G₂ : z ∈ d.VG₂ := (Finset.mem_sdiff.mp hz_int).1
  have hz_nxy : z ≠ d.x ∧ z ≠ d.y := by
    have := (Finset.mem_sdiff.mp hz_int).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact this
  have hreach_x : G₂.Reachable ⟨z, hz_G₂⟩ ⟨d.x, hx_mem⟩ := by
    have hz_ny : z ∈ ({d.y}ᶜ : Set V) := hz_nxy.2
    have hx_ny : d.x ∈ ({d.y}ᶜ : Set V) := d.hxy
    obtain ⟨P⟩ := h2conn d.y ⟨z, hz_ny⟩ ⟨d.x, hx_ny⟩
    let f := (SimpleGraph.Embedding.induce ({d.y}ᶜ : Set V)).toHom
    have hy_nP : d.y ∉ (P.map f).support := by
      intro hm
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
      rcases hm with ⟨w, _, hw⟩
      exact w.2 hw.symm
    have hx_nint : d.x ∉ d.VG₂ \ {d.x, d.y} := fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    obtain ⟨u, v, hu_int, hv_nint, huv, q, hq_sub, hq_in⟩ :=
      walk_exits_finset_last (d.VG₂ \ {d.x, d.y}) (P.map f) hz_int hx_nint
    have hv_xy : v = d.x ∨ v = d.y := by
      by_contra hnot
      push Not at hnot
      have hv_nG₂ : v ∉ d.VG₂ := fun hm => hv_nint (Finset.mem_sdiff.mpr ⟨hm, by simp [hnot.1, hnot.2]⟩)
      have hv_VH : v ∈ d.VH := by
        have : v ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp this with h1 | h2
        · exact h1
        · exact absurd h2 hv_nG₂
      have hu_G₂ : u ∈ d.VG₂ := (Finset.mem_sdiff.mp hu_int).1
      have hu_nxy : u ≠ d.x ∧ u ≠ d.y := by
        have := (Finset.mem_sdiff.mp hu_int).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        exact this
      exact d.hno_cross v hv_VH u hu_G₂ hnot.1 hnot.2 hu_nxy.1 hu_nxy.2 huv.symm
    have hv_eq_x : v = d.x := by
      rcases hv_xy with rfl | rfl
      · rfl
      · exact absurd (hq_sub d.y (SimpleGraph.Walk.end_mem_support q)) hy_nP
    subst hv_eq_x
    have hq_G₂ : ∀ w ∈ q.support, w ∈ (d.VG₂ : Set V) := by
      intro w hw
      by_cases hwx : w = d.x
      · exact hwx ▸ hx_mem
      · exact (Finset.mem_sdiff.mp (hq_in w hw hwx)).1
    exact ⟨liftWalkToInduce (d.VG₂ : Set V) q hq_G₂ hz_G₂ hx_mem⟩
  have hreach_y : G₂.Reachable ⟨z, hz_G₂⟩ ⟨d.y, hy_mem⟩ := by
    have hz_nx : z ∈ ({d.x}ᶜ : Set V) := hz_nxy.1
    have hy_nx : d.y ∈ ({d.x}ᶜ : Set V) := d.hxy.symm
    obtain ⟨P⟩ := h2conn d.x ⟨z, hz_nx⟩ ⟨d.y, hy_nx⟩
    let f := (SimpleGraph.Embedding.induce ({d.x}ᶜ : Set V)).toHom
    have hx_nP : d.x ∉ (P.map f).support := by
      intro hm
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
      rcases hm with ⟨w, _, hw⟩
      exact w.2 hw.symm
    have hy_nint : d.y ∉ d.VG₂ \ {d.x, d.y} := fun hm => (Finset.mem_sdiff.mp hm).2 (by simp)
    obtain ⟨u, v, hu_int, hv_nint, huv, q, hq_sub, hq_in⟩ :=
      walk_exits_finset_last (d.VG₂ \ {d.x, d.y}) (P.map f) hz_int hy_nint
    have hv_xy : v = d.x ∨ v = d.y := by
      by_contra hnot
      push Not at hnot
      have hv_nG₂ : v ∉ d.VG₂ := fun hm => hv_nint (Finset.mem_sdiff.mpr ⟨hm, by simp [hnot.1, hnot.2]⟩)
      have hv_VH : v ∈ d.VH := by
        have : v ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp this with h1 | h2
        · exact h1
        · exact absurd h2 hv_nG₂
      have hu_G₂ : u ∈ d.VG₂ := (Finset.mem_sdiff.mp hu_int).1
      have hu_nxy : u ≠ d.x ∧ u ≠ d.y := by
        have := (Finset.mem_sdiff.mp hu_int).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        exact this
      exact d.hno_cross v hv_VH u hu_G₂ hnot.1 hnot.2 hu_nxy.1 hu_nxy.2 huv.symm
    have hv_eq_y : v = d.y := by
      rcases hv_xy with rfl | rfl
      · exact absurd (hq_sub d.x (SimpleGraph.Walk.end_mem_support q)) hx_nP
      · rfl
    subst hv_eq_y
    have hq_G₂ : ∀ w ∈ q.support, w ∈ (d.VG₂ : Set V) := by
      intro w hw
      by_cases hwy : w = d.y
      · exact hwy ▸ hy_mem
      · exact (Finset.mem_sdiff.mp (hq_in w hw hwy)).1
    exact ⟨liftWalkToInduce (d.VG₂ : Set V) q hq_G₂ hz_G₂ hy_mem⟩
  obtain ⟨w⟩ := hreach_x.symm.trans hreach_y
  exact ⟨w.toPath.1, w.toPath.2⟩

/-- In a 2-connected graph `G` with an R-leaf decomposition `d`, if `G₂ = G[VG₂]` is non-bipartite,
then `G₂` contains both an even and an odd simple `(x, y)`-path. -/
private lemma two_parity_paths_of_nonbipartite_G₂ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected)
    (d : RLeafDecomp G)
    (hnonbip : ¬ (G.induce (d.VG₂ : Set V)).IsBipartite) :
    let hx : d.x ∈ (d.VG₂ : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
    let hy : d.y ∈ (d.VG₂ : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
    ∃ (q_even q_odd : (G.induce (d.VG₂ : Set V)).Walk ⟨d.x, hx⟩ ⟨d.y, hy⟩),
      q_even.IsPath ∧ q_odd.IsPath ∧ Even q_even.length ∧ Odd q_odd.length := by
  classical
  have hx_mem : d.x ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  have hy_mem : d.y ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  let G₂ : SimpleGraph d.VG₂ := G.induce (d.VG₂ : Set V)
  let x₂ : d.VG₂ := ⟨d.x, hx_mem⟩
  let y₂ : d.VG₂ := ⟨d.y, hy_mem⟩
  have hxy₂ : x₂ ≠ y₂ := fun h => d.hxy (congrArg Subtype.val h)
  have hodd_ex : ∃ (v : d.VG₂) (c : G₂.Walk v v), c.IsCycle ∧ Odd c.length := by
    by_contra hno
    push Not at hno
    apply hnonbip
    apply isBipartite_of_no_odd_cycle
    intro v c hc
    exact Nat.not_odd_iff_even.mp (hno v c hc)
  rcases hodd_ex with ⟨v₀, c, hc, hc_odd⟩
  let A_set : Finset d.VG₂ := {x₂, y₂}
  let B_set : Finset d.VG₂ := c.support.toFinset
  have hA_card : 2 ≤ A_set.card := by rw [Finset.card_pair hxy₂]
  have hB_card : 2 ≤ B_set.card := by
    have hsub : c.support.tail.toFinset ⊆ B_set := by
      intro z hz
      rw [List.mem_toFinset] at hz ⊢
      exact List.mem_of_mem_tail hz
    have hcard_tail : c.support.tail.toFinset.card = c.length := by
      rw [List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
        SimpleGraph.Walk.length_support]
      omega
    have hlen3 : 3 ≤ c.length := hc.three_le_length
    have := Finset.card_le_card hsub
    omega
  have hno_cut : ∀ v : d.VG₂, ∃ a ∈ A_set, ∃ b ∈ B_set, ∃ p : G₂.Walk a b, v ∉ p.support := by
    intro v
    have hB_erase : (B_set.erase v).Nonempty := by
      rw [← Finset.card_pos]
      by_cases hv : v ∈ B_set
      · rw [Finset.card_erase_of_mem hv]; omega
      · rw [Finset.erase_eq_of_notMem hv]; omega
    rcases hB_erase with ⟨b, hb_er⟩
    have hbv : b ≠ v := (Finset.mem_erase.mp hb_er).1
    have hb_B : b ∈ B_set := (Finset.mem_erase.mp hb_er).2
    by_cases hbA : b ∈ A_set
    · exact ⟨b, hbA, b, hb_B, .nil, by simp [hbv.symm]⟩
    · have hb_nxy : b.1 ≠ d.x ∧ b.1 ≠ d.y := by
        simp only [A_set, Finset.mem_insert, Finset.mem_singleton, not_or, Subtype.ext_iff] at hbA
        exact hbA
      have hb_int : b.1 ∈ d.VG₂ \ {d.x, d.y} :=
        Finset.mem_sdiff.mpr ⟨b.2, by simp [hb_nxy.1, hb_nxy.2]⟩
      have hH_int : (d.VH \ {d.x, d.y}).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff]
        have hle : ({d.x, d.y} ∩ d.VH).card ≤ 2 :=
          le_trans (Finset.card_le_card Finset.inter_subset_left) (by rw [Finset.card_pair d.hxy])
        have := d.hcardH
        omega
      rcases hH_int with ⟨h, hh_int⟩
      have hh_VH : h ∈ d.VH := (Finset.mem_sdiff.mp hh_int).1
      have hh_nxy : h ≠ d.x ∧ h ≠ d.y := by
        have := (Finset.mem_sdiff.mp hh_int).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        exact this
      have hh_nG₂ : h ∉ d.VG₂ := by
        intro hhG₂
        have : h ∈ d.VH ∩ d.VG₂ := Finset.mem_inter.mpr ⟨hh_VH, hhG₂⟩
        rw [d.hinter] at this
        simp [hh_nxy.1, hh_nxy.2] at this
      have hh_ne_v : h ∈ ({v.1}ᶜ : Set V) := fun heq => hh_nG₂ (heq ▸ v.2)
      have hb_ne_v : b.1 ∈ ({v.1}ᶜ : Set V) := fun heq => hbv (Subtype.ext heq)
      obtain ⟨P⟩ := h2conn v.1 ⟨b.1, hb_ne_v⟩ ⟨h, hh_ne_v⟩
      let f := (SimpleGraph.Embedding.induce ({v.1}ᶜ : Set V)).toHom
      have hv_nP : v.1 ∉ (P.map f).support := by
        intro hmem
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hmem
        rcases hmem with ⟨w, _, hw⟩
        exact w.2 hw.symm
      have hh_nint : h ∉ d.VG₂ \ {d.x, d.y} := fun hm => hh_nG₂ (Finset.mem_sdiff.mp hm).1
      obtain ⟨u, a₀, hu_int, ha₀_nint, hua₀, q, hq_sub, hq_in⟩ :=
        walk_exits_finset_last (d.VG₂ \ {d.x, d.y}) (P.map f) hb_int hh_nint
      have ha₀_xy : a₀ = d.x ∨ a₀ = d.y := by
        by_contra hnot
        push Not at hnot
        have ha₀_nG₂ : a₀ ∉ d.VG₂ := fun hmem => ha₀_nint (Finset.mem_sdiff.mpr ⟨hmem, by simp [hnot.1, hnot.2]⟩)
        have ha₀_VH : a₀ ∈ d.VH := by
          have : a₀ ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
          rcases Finset.mem_union.mp this with h1 | h2
          · exact h1
          · exact absurd h2 ha₀_nG₂
        have hu_G₂ : u ∈ d.VG₂ := (Finset.mem_sdiff.mp hu_int).1
        have hu_nxy : u ≠ d.x ∧ u ≠ d.y := by
          have := (Finset.mem_sdiff.mp hu_int).2
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
          exact this
        exact d.hno_cross a₀ ha₀_VH u hu_G₂ hnot.1 hnot.2 hu_nxy.1 hu_nxy.2 hua₀.symm
      have ha₀_G₂ : a₀ ∈ (d.VG₂ : Set V) := by
        rcases ha₀_xy with rfl | rfl
        · exact hx_mem
        · exact hy_mem
      have hq_G₂ : ∀ w ∈ q.support, w ∈ (d.VG₂ : Set V) := by
        intro w hw
        by_cases hwa : w = a₀
        · exact hwa ▸ ha₀_G₂
        · exact (Finset.mem_sdiff.mp (hq_in w hw hwa)).1
      let q_lift : G₂.Walk b ⟨a₀, ha₀_G₂⟩ := liftWalkToInduce (d.VG₂ : Set V) q hq_G₂ b.2 ha₀_G₂
      refine ⟨⟨a₀, ha₀_G₂⟩, ?_, b, hb_B, q_lift.reverse, ?_⟩
      · simp only [A_set, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact ha₀_xy
      · intro hv_mem
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv_mem
        have hv_q : v.1 ∈ q.support := (liftWalkToInduce_mem_support _ q hq_G₂ b.2 ha₀_G₂ v).mp hv_mem
        exact hv_nP (hq_sub v.1 hv_q)
  obtain ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, ha_ne, _, hp₁, hp₂, hdisj12, hint1, hint2⟩ :=
    two_disjoint_paths_between_sets _ G₂ A_set B_set rfl hA_card hB_card hno_cut
  have htrim1 : ∃ (b₁' : d.VG₂) (p₁' : G₂.Walk a₁ b₁'),
      b₁' ∈ B_set ∧ p₁'.IsPath ∧
      (∀ x ∈ p₁'.support, x ∈ p₁.support) ∧
      (∀ x ∈ p₁'.support, x ≠ b₁' → x ∉ B_set) := by
    by_cases h1 : a₁ ∈ B_set
    · exact ⟨a₁, .nil, h1, SimpleGraph.Walk.IsPath.nil,
        fun x hx => by simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; subst hx; exact SimpleGraph.Walk.start_mem_support _,
        fun x hx hne => by simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; exact absurd hx hne⟩
    · refine ⟨b₁, p₁, hb₁, hp₁, fun _ hx => hx, fun x hx hxb => ?_⟩
      by_cases hxa : x = a₁
      · exact hxa ▸ h1
      · exact (hint1 x hx hxa hxb).2
  have htrim2 : ∃ (b₂' : d.VG₂) (p₂' : G₂.Walk a₂ b₂'),
      b₂' ∈ B_set ∧ p₂'.IsPath ∧
      (∀ x ∈ p₂'.support, x ∈ p₂.support) ∧
      (∀ x ∈ p₂'.support, x ≠ b₂' → x ∉ B_set) := by
    by_cases h2 : a₂ ∈ B_set
    · exact ⟨a₂, .nil, h2, SimpleGraph.Walk.IsPath.nil,
        fun x hx => by simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; subst hx; exact SimpleGraph.Walk.start_mem_support _,
        fun x hx hne => by simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; exact absurd hx hne⟩
    · refine ⟨b₂, p₂, hb₂, hp₂, fun _ hx => hx, fun x hx hxb => ?_⟩
      by_cases hxa : x = a₂
      · exact hxa ▸ h2
      · exact (hint2 x hx hxa hxb).2
  rcases htrim1 with ⟨b₁', p₁', hb₁', hp₁', hsub1, hout1⟩
  rcases htrim2 with ⟨b₂', p₂', hb₂', hp₂', hsub2, hout2⟩
  have hdisj12' : Disjoint p₁'.support.toFinset p₂'.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Finset.disjoint_left.mp hdisj12
      (List.mem_toFinset.mpr (hsub1 x (List.mem_toFinset.mp hx1)))
      (List.mem_toFinset.mpr (hsub2 x (List.mem_toFinset.mp hx2)))
  have hb_ne' : b₁' ≠ b₂' := by
    intro heq
    exact Finset.disjoint_left.mp hdisj12'
      (List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support p₁'))
      (List.mem_toFinset.mpr (heq ▸ SimpleGraph.Walk.end_mem_support p₂'))
  obtain ⟨r₁, r₂, hr₁, hr₂, hr_len, hr_supp, _, _⟩ :=
    cycle_arcs_of_mem c hc (List.mem_toFinset.mp hb₁') (List.mem_toFinset.mp hb₂') hb_ne'
  let w₁ : G₂.Walk a₁ a₂ := (p₁'.append r₁).append p₂'.reverse
  let w₂ : G₂.Walk a₁ a₂ := (p₁'.append r₂).append p₂'.reverse
  have hw₁ : w₁.IsPath :=
    path_concat_three_isPath p₁' r₁ p₂' hp₁' hr₁ hp₂' hdisj12'
      (fun x hx hne hxr => hout1 x hx hne (List.mem_toFinset.mpr ((hr_supp x).mp (Or.inl hxr))))
      (fun x hx hne hxr => hout2 x hx hne (List.mem_toFinset.mpr ((hr_supp x).mp (Or.inl hxr))))
  have hw₂ : w₂.IsPath :=
    path_concat_three_isPath p₁' r₂ p₂' hp₁' hr₂ hp₂' hdisj12'
      (fun x hx hne hxr => hout1 x hx hne (List.mem_toFinset.mpr ((hr_supp x).mp (Or.inr hxr))))
      (fun x hx hne hxr => hout2 x hx hne (List.mem_toFinset.mpr ((hr_supp x).mp (Or.inr hxr))))
  have hsum_odd : Odd (w₁.length + w₂.length) := by
    have hl1 : w₁.length = p₁'.length + r₁.length + p₂'.length := by
      simp [w₁, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    have hl2 : w₂.length = p₁'.length + r₂.length + p₂'.length := by
      simp [w₂, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    rcases hc_odd with ⟨k, hk⟩
    refine ⟨p₁'.length + p₂'.length + k, ?_⟩
    omega
  simp only [A_set, Finset.mem_insert, Finset.mem_singleton] at ha₁ ha₂
  rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl
  · exact absurd rfl ha_ne
  · by_cases he1 : Even w₁.length
    · have ho2 : Odd w₂.length := by
        rcases he1 with ⟨a, ha⟩; rcases hsum_odd with ⟨b, hb⟩; exact ⟨b - a, by omega⟩
      exact ⟨w₁, w₂, hw₁, hw₂, he1, ho2⟩
    · have ho1 : Odd w₁.length := Nat.not_even_iff_odd.mp he1
      have he2 : Even w₂.length := by
        rcases ho1 with ⟨a, ha⟩; rcases hsum_odd with ⟨b, hb⟩; exact ⟨b - a, by omega⟩
      exact ⟨w₂, w₁, hw₂, hw₁, he2, ho1⟩
  · by_cases he1 : Even w₁.length
    · have ho2 : Odd w₂.length := by
        rcases he1 with ⟨a, ha⟩; rcases hsum_odd with ⟨b, hb⟩; exact ⟨b - a, by omega⟩
      exact ⟨w₁.reverse, w₂.reverse, hw₁.reverse, hw₂.reverse,
        by simpa using he1, by simpa using ho2⟩
    · have ho1 : Odd w₁.length := Nat.not_even_iff_odd.mp he1
      have he2 : Even w₂.length := by
        rcases ho1 with ⟨a, ha⟩; rcases hsum_odd with ⟨b, hb⟩; exact ⟨b - a, by omega⟩
      exact ⟨w₂.reverse, w₁.reverse, hw₂.reverse, hw₁.reverse,
        by simpa using he2, by simpa using ho1⟩
  · exact absurd rfl ha_ne

private lemma walkModFourWeight_map_of_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (σG : Sym2 V → ℤ) (σH : Sym2 W → ℤ)
    (hσ : ∀ e ∈ G.edgeSet, σG e = σH (e.map φ))
    {u v : V} (p : G.Walk u v) :
    walkModFourWeight σH (p.map φ) = walkModFourWeight σG p := by
  induction p with
  | nil => simp [walkModFourWeight]
  | @cons a b c hadj r ih =>
    simp only [SimpleGraph.Walk.map_cons, walkModFourWeight, SimpleGraph.Walk.edges_cons,
      List.map_cons, List.sum_cons] at ih ⊢
    have h1 : σG s(a, b) = σH s(φ a, φ b) := hσ s(a, b) hadj
    have hw : modFourWeight σH s(φ a, φ b) = modFourWeight σG s(a, b) := by
      unfold modFourWeight; rw [h1]
    rw [hw, ih]

private lemma walk_edge_incident_end_eq_last {V : Type*} {G : SimpleGraph V} {w a b : V}
    (r : G.Walk w a) (hnd : r.support.Nodup) (he : s(a, b) ∈ r.edges) :
    ∃ r_rev_tail : G.Walk b w, ∃ hab : G.Adj a b, r.reverse = SimpleGraph.Walk.cons hab r_rev_tail := by
  have hmem_rev : s(a, b) ∈ r.reverse.edges := by
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact he
  cases hr : r.reverse with
  | nil =>
    rw [hr] at hmem_rev; simp at hmem_rev
  | @cons _ u _ hau r₂ =>
    rw [hr, SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem_rev
    have hnd_rev : r.reverse.support.Nodup := by
      rw [SimpleGraph.Walk.support_reverse]; exact hnd.reverse
    rw [hr, SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd_rev
    rcases hmem_rev with heq | hin
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact ⟨r₂, hau, rfl⟩
      · exact absurd rfl (G.ne_of_adj hau)
    · have ha_in : a ∈ r₂.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges r₂ hin
      exact absurd ha_in hnd_rev.1

private lemma cycle_split_at_edge {V : Type*} {G : SimpleGraph V} {v a b : V}
    (c : G.Walk v v) (hc : c.IsCycle) (he : s(a, b) ∈ c.edges) :
    ∃ p : G.Walk a b, p.IsPath ∧ s(a, b) ∉ p.edges ∧
      p.length + 1 = c.length ∧
      (∀ σ : Sym2 V → ℤ, walkModFourWeight σ c = modFourWeight σ s(a, b) + walkModFourWeight σ p) := by
  have ha : a ∈ c.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c he
  let c' : G.Walk a a := c.rotate ha
  have hc' : c'.IsCycle := hc.rotate ha
  have hlen' : c'.length = c.length := SimpleGraph.Walk.length_rotate c ha
  have hperm : c'.edges.Perm c.edges := SimpleGraph.Walk.edges_rotate c ha
  have he' : s(a, b) ∈ c'.edges := hperm.mem_iff.mpr he
  have hwt' : ∀ σ : Sym2 V → ℤ, walkModFourWeight σ c' = walkModFourWeight σ c :=
    fun σ => walkModFourWeight_rotate σ c ha
  cases hc'_eq : c' with
  | nil => exact absurd hc'_eq hc'.ne_nil
  | @cons _ w _ haw r =>
    have hc'_nd : (SimpleGraph.Walk.cons haw r).edges.Nodup := hc'_eq ▸ hc'.edges_nodup
    have hc'_snd : (SimpleGraph.Walk.cons haw r).support.tail.Nodup := hc'_eq ▸ hc'.support_nodup
    simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hc'_nd
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at hc'_snd
    rw [hc'_eq, SimpleGraph.Walk.edges_cons, List.mem_cons] at he'
    rcases he' with heq | hr_mem
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · refine ⟨r.reverse, (SimpleGraph.Walk.isPath_def r).mpr hc'_snd |>.reverse, ?_, ?_, ?_⟩
        · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hc'_nd.1
        · have : (SimpleGraph.Walk.cons haw r).length = c.length := hc'_eq ▸ hlen'
          simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at this ⊢
          omega
        · intro σ
          rw [← hwt' σ, hc'_eq]
          simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
            SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
      · exact absurd rfl (G.ne_of_adj haw)
    · obtain ⟨r₂, hab, hr_rev⟩ := walk_edge_incident_end_eq_last r hc'_snd hr_mem
      let c_rev : G.Walk a a := c'.reverse
      have hc_rev : c_rev.IsCycle := hc'.reverse
      have hc_rev_eq : c_rev = SimpleGraph.Walk.cons hab (r₂.append (SimpleGraph.Walk.cons haw.symm .nil)) := by
        simp only [c_rev, hc'_eq, SimpleGraph.Walk.reverse_cons, hr_rev, SimpleGraph.Walk.cons_append]
      let q : G.Walk b a := r₂.append (SimpleGraph.Walk.cons haw.symm .nil)
      have hq_nd : (SimpleGraph.Walk.cons hab q).edges.Nodup := hc_rev_eq ▸ hc_rev.edges_nodup
      have hq_snd : (SimpleGraph.Walk.cons hab q).support.tail.Nodup := hc_rev_eq ▸ hc_rev.support_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hq_nd
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at hq_snd
      refine ⟨q.reverse, (SimpleGraph.Walk.isPath_def q).mpr hq_snd |>.reverse, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hq_nd.1
      · have h1 : c_rev.length = c.length := by simp [c_rev, hlen']
        rw [hc_rev_eq, SimpleGraph.Walk.length_cons] at h1
        simp only [SimpleGraph.Walk.length_reverse]
        omega
      · intro σ
        rw [← hwt' σ, ← walkModFourWeight_reverse σ c']
        change walkModFourWeight σ c_rev = _
        rw [hc_rev_eq]
        simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
          SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]

/-- For an R-leaf `d` in a 2-connected non-bipartite NOC signed graph, its real subgraph `H`
cannot be bipartite. -/
private lemma leaf_H_nonbipartite {V : Type*} [Fintype V] [DecidableEq V]
    (S : SignedGraph V) (h2conn : ∀ v : V, (S.graph.induce ({v}ᶜ : Set V)).Preconnected)
    (hnonbip : ¬ S.graph.IsBipartite) (hnoc : IsNOC S)
    (d : RLeafDecomp S.graph) :
    let T : SimpleGraph d.VH :=
      (S.graph.induce (d.VH : Set V)) ⊔
        SimpleGraph.fromRel (fun a b : d.VH => (a.1 = d.x ∧ b.1 = d.y) ∨ (a.1 = d.y ∧ b.1 = d.x))
    let hx : d.x ∈ (d.VH : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).1
    let hy : d.y ∈ (d.VH : Set V) := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).1
    ¬ (T.deleteEdges {s(⟨d.x, hx⟩, ⟨d.y, hy⟩)}).IsBipartite := by
  classical
  have hxH : d.x ∈ d.VH := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).1
  have hyH : d.y ∈ d.VH := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).1
  have hxG₂ : d.x ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  have hyG₂ : d.y ∈ d.VG₂ := (Finset.mem_inter.mp (by rw [d.hinter]; simp)).2
  let xH : d.VH := ⟨d.x, hxH⟩
  let yH : d.VH := ⟨d.y, hyH⟩
  let x₂ : d.VG₂ := ⟨d.x, hxG₂⟩
  let y₂ : d.VG₂ := ⟨d.y, hyG₂⟩
  let T : SimpleGraph d.VH :=
    (S.graph.induce (d.VH : Set V)) ⊔
      SimpleGraph.fromRel (fun a b : d.VH => (a.1 = d.x ∧ b.1 = d.y) ∨ (a.1 = d.y ∧ b.1 = d.x))
  let H : SimpleGraph d.VH := T.deleteEdges {s(xH, yH)}
  let G₂ : SimpleGraph d.VG₂ := S.graph.induce (d.VG₂ : Set V)
  intro hHbip
  have hT_card : 4 ≤ Fintype.card d.VH := by
    rw [Fintype.card_coe]; exact d.hcardH
  have hT_conn : T.Preconnected := by
    have h0 := d.hT_3conn ∅ (by simp)
    intro a b
    have ha : a ∈ ((∅ : Finset d.VH)ᶜ : Set d.VH) := by simp
    have hb : b ∈ ((∅ : Finset d.VH)ᶜ : Set d.VH) := by simp
    obtain ⟨w⟩ := h0 ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨w.map (SimpleGraph.Embedding.induce _).toHom⟩
  have hT_xy : T.Adj xH yH := by
    right
    exact ⟨fun h => d.hxy (congrArg Subtype.val h), Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  have hH_le_G : ∀ a b : d.VH, H.Adj a b → S.graph.Adj a.1 b.1 := by
    intro a b hab
    rcases hab with ⟨hTab, hne_xy⟩
    rcases hTab with hG | hrel
    · exact hG
    · exfalso
      apply hne_xy
      rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
      · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
      · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
      · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
  let embH : H →g S.graph := ⟨Subtype.val, fun h => hH_le_G _ _ h⟩
  let embG₂ : G₂ →g S.graph := ⟨Subtype.val, fun h => h⟩
  let σH : Sym2 d.VH → ℤ := fun e => S.sign (e.map Subtype.val)
  have hσH : ∀ e ∈ H.edgeSet, σH e = 1 ∨ σH e = -1 := by
    intro e he
    rcases e with ⟨a, b⟩
    exact S.sign_pm_one s(a.1, b.1) (hH_le_G a b he)
  obtain ⟨p₁, p₂, hp₁, hp₂, hdiff2⟩ :=
    bipartite_r_leaf_path_diversity T hT_card hT_conn d.hT_3conn xH yH hT_xy H rfl hHbip σH hσH
  have hp_same_par : Even (p₁.length + p₂.length) := by
    have hcl := even_length_of_isBipartite hHbip (p₁.append p₂.reverse)
    simpa [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using hcl
  have hno_opp_parity : ∀ (q : G₂.Walk x₂ y₂), q.IsPath → Odd (q.length + p₁.length) → False := by
    intro q hq hodd1
    have hodd2 : Odd (q.length + p₂.length) := by
      rcases hp_same_par with ⟨a, ha⟩
      rcases hodd1 with ⟨b, hb⟩
      exact ⟨b + a - p₁.length, by omega⟩
    let qG : S.graph.Walk d.x d.y := q.map embG₂
    let p₁G : S.graph.Walk d.x d.y := p₁.map embH
    let p₂G : S.graph.Walk d.x d.y := p₂.map embH
    have hqG_path : qG.IsPath := hq.map Subtype.coe_injective
    have hp₁G_path : p₁G.IsPath := hp₁.map Subtype.coe_injective
    have hp₂G_path : p₂G.IsPath := hp₂.map Subtype.coe_injective
    have hdisj : ∀ (p : H.Walk xH yH),
        ∀ w ∈ qG.support, w ≠ d.x → w ≠ d.y → w ∉ (p.map embH).support := by
      intro p w hwq hwx hwy hwp
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hwq hwp
      rcases hwq with ⟨w₂, _, rfl⟩
      rcases hwp with ⟨w₁, _, heq⟩
      have hinter : w₂.1 ∈ d.VH ∩ d.VG₂ := Finset.mem_inter.mpr ⟨heq ▸ w₁.2, w₂.2⟩
      rw [d.hinter] at hinter
      simp [hwx, hwy] at hinter
    have hq_pos : 1 ≤ qG.length := by
      cases h : qG with
      | nil => exact absurd rfl d.hxy
      | cons _ _ => simp
    have hp1_pos : 1 ≤ p₁G.length := by
      cases h : p₁G with
      | nil => exact absurd rfl d.hxy
      | cons _ _ => simp
    have hp2_pos : 1 ≤ p₂G.length := by
      cases h : p₂G with
      | nil => exact absurd rfl d.hxy
      | cons _ _ => simp
    have hlen1 : 3 ≤ qG.length + p₁G.length := by
      have : Odd (qG.length + p₁G.length) := by simpa [qG, p₁G] using hodd1
      rcases this with ⟨k, hk⟩; omega
    have hlen2 : 3 ≤ qG.length + p₂G.length := by
      have : Odd (qG.length + p₂G.length) := by simpa [qG, p₂G] using hodd2
      rcases this with ⟨k, hk⟩; omega
    have hc1 : (qG.append p₁G.reverse).IsCycle :=
      isCycle_append_reverse_of_disjoint p₁G qG hp₁G_path hqG_path (hdisj p₁) hlen1
    have hc2 : (qG.append p₂G.reverse).IsCycle :=
      isCycle_append_reverse_of_disjoint p₂G qG hp₂G_path hqG_path (hdisj p₂) hlen2
    have hmod4 := (isNOC_iff_isNOCModFour S).mp hnoc
    have hw1 := hmod4 d.x (qG.append p₁G.reverse) hc1 (by simpa [qG, p₁G] using hodd1)
    have hw2 := hmod4 d.x (qG.append p₂G.reverse) hc2 (by simpa [qG, p₂G] using hodd2)
    rw [walkModFourWeight_append, walkModFourWeight_reverse] at hw1 hw2
    have hwm1 : walkModFourWeight S.sign p₁G = walkModFourWeight σH p₁ :=
      walkModFourWeight_map_of_eq embH σH S.sign (fun _ _ => rfl) p₁
    have hwm2 : walkModFourWeight S.sign p₂G = walkModFourWeight σH p₂ :=
      walkModFourWeight_map_of_eq embH σH S.sign (fun _ _ => rfl) p₂
    rw [hwm1] at hw1
    rw [hwm2] at hw2
    have hzero : walkModFourWeight σH p₁ - walkModFourWeight σH p₂ = 0 := by
      linear_combination hw1 - hw2
    rw [hdiff2] at hzero
    exact absurd hzero (by decide)
  have hG₂bip : G₂.IsBipartite := by
    by_contra hG₂nb
    obtain ⟨qe, qo, hqe, hqo, he, ho⟩ := two_parity_paths_of_nonbipartite_G₂ S.graph h2conn d hG₂nb
    by_cases hp1e : Even p₁.length
    · apply hno_opp_parity qo hqo
      rcases ho with ⟨a, ha⟩; rcases hp1e with ⟨b, hb⟩; exact ⟨a + b, by omega⟩
    · apply hno_opp_parity qe hqe
      have hp1o : Odd p₁.length := Nat.not_even_iff_odd.mp hp1e
      rcases he with ⟨a, ha⟩; rcases hp1o with ⟨b, hb⟩; exact ⟨a + b, by omega⟩
  obtain ⟨q, hq⟩ := exists_path_in_G₂ S.graph h2conn d
  have hq_same_par : Even (q.length + p₁.length) := by
    by_contra hne
    exact hno_opp_parity q hq (Nat.not_even_iff_odd.mp hne)
  rcases hHbip with ⟨fH⟩
  rcases hG₂bip with ⟨fG₂⟩
  have hcol_walk : ∀ {W : Type*} {G : SimpleGraph W} (f : G.Coloring (Fin 2)) {a b : W} (w : G.Walk a b),
      f b = f a + (w.length : Fin 2) := by
    intro W G f a b w
    induction w with
    | nil => simp
    | @cons u v z huv r ih =>
      have hne : f u ≠ f v := f.valid huv
      have hstep : f v = f u + 1 := by
        fin_cases hfu : f u <;> fin_cases hfv : f v <;> simp_all
      rw [ih, hstep, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      ring
  have hfH_xy : fH yH = fH xH + (p₁.length : Fin 2) := hcol_walk fH p₁
  have hfG₂_xy : fG₂ y₂ = fG₂ x₂ + (q.length : Fin 2) := hcol_walk fG₂ q
  have hlen_eq : (q.length : Fin 2) = (p₁.length : Fin 2) := by
    rcases hq_same_par with ⟨k, hk⟩
    have h0 : ((q.length + p₁.length : ℕ) : Fin 2) = 0 := by
      rw [hk, ← two_mul, Nat.cast_mul]; simp
    rw [Nat.cast_add] at h0
    fin_cases hq2 : (q.length : Fin 2) <;> fin_cases hp2 : (p₁.length : Fin 2) <;> simp_all
  let shift : Fin 2 := fH xH - fG₂ x₂
  let f : V → Fin 2 := fun v =>
    if hv : v ∈ d.VG₂ then fG₂ ⟨v, hv⟩ + shift
    else fH ⟨v, by
      have : v ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with h1 | h2
      · exact h1
      · exact absurd h2 hv⟩
  have hf_x : f d.x = fH xH := by
    simp only [f, hxG₂, ↓reduceDIte, shift]
    exact sub_add_cancel' (fG₂ x₂) (fH xH)
  have hf_y : f d.y = fH yH := by
    simp only [f, hyG₂, ↓reduceDIte, shift]
    change fG₂ y₂ + (fH xH - fG₂ x₂) = fH yH
    rw [hfG₂_xy, hfH_xy, hlen_eq]
    ring
  have hf_valid : ∀ {u v : V}, S.graph.Adj u v → f u ≠ f v := by
    intro u v huv
    by_cases hu : u ∈ d.VG₂ <;> by_cases hv : v ∈ d.VG₂
    · simp only [f, hu, hv, ↓reduceDIte]
      intro heq
      exact fG₂.valid (show G₂.Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv) (add_right_cancel heq)
    · have hvH : v ∈ d.VH := by
        have : v ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp this).resolve_right hv
      have hv_nxy : v ≠ d.x ∧ v ≠ d.y := ⟨fun h => hv (h ▸ hxG₂), fun h => hv (h ▸ hyG₂)⟩
      have hu_xy : u = d.x ∨ u = d.y := by
        by_contra hnot; push Not at hnot
        exact d.hno_cross v hvH u hu hv_nxy.1 hv_nxy.2 hnot.1 hnot.2 huv.symm
      have hfu : f u = fH ⟨u, by rcases hu_xy with rfl | rfl <;> assumption⟩ := by
        rcases hu_xy with rfl | rfl
        · exact hf_x
        · exact hf_y
      have hfv : f v = fH ⟨v, hvH⟩ := by simp [f, hv]
      rw [hfu, hfv]
      have hHadj : H.Adj ⟨u, by rcases hu_xy with rfl | rfl <;> assumption⟩ ⟨v, hvH⟩ := by
        refine ⟨Or.inl huv, fun hsym => ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, Subtype.ext_iff] at hsym
        rcases hsym with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hv_nxy.2 h2
        · exact hv_nxy.1 h2
      exact fH.valid hHadj
    · have huH : u ∈ d.VH := by
        have : u ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp this).resolve_right hu
      have hu_nxy : u ≠ d.x ∧ u ≠ d.y := ⟨fun h => hu (h ▸ hxG₂), fun h => hu (h ▸ hyG₂)⟩
      have hv_xy : v = d.x ∨ v = d.y := by
        by_contra hnot; push Not at hnot
        exact d.hno_cross u huH v hv hu_nxy.1 hu_nxy.2 hnot.1 hnot.2 huv
      have hfv : f v = fH ⟨v, by rcases hv_xy with rfl | rfl <;> assumption⟩ := by
        rcases hv_xy with rfl | rfl
        · exact hf_x
        · exact hf_y
      have hfu : f u = fH ⟨u, huH⟩ := by simp [f, hu]
      rw [hfu, hfv]
      have hHadj : H.Adj ⟨u, huH⟩ ⟨v, by rcases hv_xy with rfl | rfl <;> assumption⟩ := by
        refine ⟨Or.inl huv, fun hsym => ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, Subtype.ext_iff] at hsym
        rcases hsym with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hu_nxy.1 h1
        · exact hu_nxy.2 h1
      exact fH.valid hHadj
    · have huH : u ∈ d.VH := by
        have : u ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp this).resolve_right hu
      have hvH : v ∈ d.VH := by
        have : v ∈ d.VH ∪ d.VG₂ := by rw [d.hunion]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp this).resolve_right hv
      have hu_nxy : u ≠ d.x ∧ u ≠ d.y := ⟨fun h => hu (h ▸ hxG₂), fun h => hu (h ▸ hyG₂)⟩
      simp only [f, hu, hv, ↓reduceDIte]
      have hHadj : H.Adj ⟨u, huH⟩ ⟨v, hvH⟩ := by
        refine ⟨Or.inl huv, fun hsym => ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, Subtype.ext_iff] at hsym
        rcases hsym with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hu_nxy.1 h1
        · exact hu_nxy.2 h1
      exact fH.valid hHadj
  exact hnonbip ⟨SimpleGraph.Coloring.mk f hf_valid⟩

/-- Strong-induction proof of **Theorem 1.2** on arbitrary finite vertex types `V`. -/
private theorem theorem_1_2_general :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ (A : Matrix V V ℝ) (hA : A.IsHermitian),
        (∀ u, A u u = 0) → MatrixIsNOC A hA.isSymm → signature A hA ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    intro V _ _ hcardV A hA hdiag hnoc
    let G : SimpleGraph V := matrixGraph A hA.isSymm
    let S : SignedGraph V := matrixSignedGraph A hA.isSymm
    -- Step 1: Bipartite graphs have signature 0
    by_cases hbip : G.IsBipartite
    · have h0 := signature_zero_of_bipartite_local A hA hdiag hbip
      omega
    -- Step 2: Disconnected graphs split into smaller NOC blocks
    by_cases hconn : G.Preconnected
    · -- Step 3: Cut-vertex reduction (Lemma 2.1)
      by_cases h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected
      · have hn3 : 3 ≤ Fintype.card V := by
          by_contra hlt
          apply hbip
          apply isBipartite_of_no_odd_cycle
          intro v c hc
          have hlen3 : 3 ≤ c.length := hc.three_le_length
          have hle_card : c.length ≤ Fintype.card V := by
            have := c.support.tail.toFinset.card_le_univ
            rw [List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
              SimpleGraph.Walk.length_support] at this
            omega
          omega
        have hdeg2 : ∀ v : V, 2 ≤ G.degree v := by
          intro v
          by_contra hlt
          have hle1 : G.degree v ≤ 1 := by omega
          by_cases h0 : G.degree v = 0
          · have hother : ∃ w : V, w ≠ v := by
              have : 1 < Fintype.card V := by omega
              rcases Fintype.exists_pair_of_one_lt_card this with ⟨a, b, hab⟩
              by_cases hav : a = v
              · exact ⟨b, hab.symm.trans_eq hav |> fun h => h.symm⟩
              · exact ⟨a, hav⟩
            rcases hother with ⟨w, hwv⟩
            obtain ⟨p⟩ := hconn v w
            cases p with
            | nil => exact hwv rfl
            | @cons _ u _ huv _ =>
              have hu_mem : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr huv
              have : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨u, hu_mem⟩
              rw [SimpleGraph.card_neighborFinset_eq_degree] at this
              omega
          · have hd1 : (G.neighborFinset v).card = 1 := by
              rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
            rcases Finset.card_eq_one.mp hd1 with ⟨x, hx_eq⟩
            have hvx : v ≠ x := by
              have : x ∈ G.neighborFinset v := by rw [hx_eq]; simp
              exact G.ne_of_adj ((G.mem_neighborFinset v x).mp this)
            have hthird : ∃ w : V, w ≠ v ∧ w ≠ x := by
              have hcard_er : (Finset.univ \ ({v, x} : Finset V)).card ≥ 1 := by
                rw [Finset.card_sdiff]
                have hle : (({v, x} : Finset V) ∩ Finset.univ).card ≤ 2 := by
                  rw [Finset.inter_univ]; exact (Finset.card_pair hvx).le
                rw [Finset.card_univ]
                omega
              rcases Finset.card_pos.mp (by omega : 0 < (Finset.univ \ ({v, x} : Finset V)).card) with ⟨w, hw⟩
              have hns := (Finset.mem_sdiff.mp hw).2
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hns
              exact ⟨w, hns.1, hns.2⟩
            rcases hthird with ⟨w, hwv, hwx⟩
            have hv_nx : v ∈ ({x}ᶜ : Set V) := hvx
            have hw_nx : w ∈ ({x}ᶜ : Set V) := hwx
            obtain ⟨p⟩ := h2conn x ⟨v, hv_nx⟩ ⟨w, hw_nx⟩
            cases p with
            | nil => exact hwv rfl
            | @cons _ u _ hvu _ =>
              have hu_mem : u.1 ∈ G.neighborFinset v := (G.mem_neighborFinset v u.1).mpr hvu
              rw [hx_eq, Finset.mem_singleton] at hu_mem
              exact u.2 hu_mem
        -- Step 4: Degree-2 reduction (Lemma 2.2)
        by_cases hdeg3 : ∀ v : V, 3 ≤ G.degree v
        · have hn4 : 4 ≤ Fintype.card V := by
            have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
            rcases hne with ⟨v₀⟩
            have hsub : insert v₀ (G.neighborFinset v₀) ⊆ Finset.univ := Finset.subset_univ _
            have hnv : v₀ ∉ G.neighborFinset v₀ := fun hm =>
              G.ne_of_adj ((G.mem_neighborFinset v₀ v₀).mp hm) rfl
            have hcard_ins : (insert v₀ (G.neighborFinset v₀)).card = G.degree v₀ + 1 := by
              rw [Finset.card_insert_of_notMem hnv, SimpleGraph.card_neighborFinset_eq_degree]
            have hle := Finset.card_le_card hsub
            rw [Finset.card_univ, hcard_ins] at hle
            have := hdeg3 v₀
            omega
          -- Step 5: 3-connected case (Theorem 3.1 + Lemmas 5.1(1), 5.2(1))
          by_cases h3conn : ∀ C : Finset V, C.card ≤ 2 → (G.induce (Cᶜ : Set V)).Preconnected
          · rcases three_connected_non_bipartite_noc_classification S hn4 hconn h3conn hbip hnoc with
              hk4 | hpet
            · exact k4_signature_nonpos A hA hdiag hk4
            · exact petersen_signature_nonpos A hA hdiag hpet
          · -- Step 6: 2-connected, δ ≥ 3, not 3-connected → SPQR two R-leaves
            obtain ⟨d₁, d₂, _, hd₂_in_d₁⟩ :=
              two_r_leaves_of_two_connected_min_deg_three G hn4 hconn h2conn hdeg3 h3conn
            have hH₂_nb := leaf_H_nonbipartite S h2conn hbip hnoc d₂
            have hH₁_nb := leaf_H_nonbipartite S h2conn hbip hnoc d₁
            let G₂₁ : SimpleGraph d₁.VG₂ := G.induce (d₁.VG₂ : Set V)
            have hG₂₁_nb : ¬ G₂₁.IsBipartite := by
              intro hG₂₁_bip
              apply hH₂_nb
              rcases hG₂₁_bip with ⟨f₂⟩
              let hx₂ : d₂.x ∈ (d₂.VH : Set V) := (Finset.mem_inter.mp (by rw [d₂.hinter]; simp)).1
              let hy₂ : d₂.y ∈ (d₂.VH : Set V) := (Finset.mem_inter.mp (by rw [d₂.hinter]; simp)).1
              refine ⟨SimpleGraph.Coloring.mk (fun u : d₂.VH => f₂ ⟨u.1, hd₂_in_d₁ u.2⟩) ?_⟩
              intro a b hab
              rcases hab with ⟨hTab, hne_xy⟩
              have hGab : G.Adj a.1 b.1 := by
                rcases hTab with hG | hrel
                · exact hG
                · exfalso; apply hne_xy
                  rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
                  · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
                  · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
                  · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
              exact f₂.valid hGab
            obtain ⟨_, Q, _, hQ_path, _, hQ_odd⟩ :=
              two_parity_paths_of_nonbipartite_G₂ G h2conn d₁ hG₂₁_nb
            have hxH : d₁.x ∈ d₁.VH := (Finset.mem_inter.mp (by rw [d₁.hinter]; simp)).1
            have hyH : d₁.y ∈ d₁.VH := (Finset.mem_inter.mp (by rw [d₁.hinter]; simp)).1
            have hxG₂ : d₁.x ∈ d₁.VG₂ := (Finset.mem_inter.mp (by rw [d₁.hinter]; simp)).2
            have hyG₂ : d₁.y ∈ d₁.VG₂ := (Finset.mem_inter.mp (by rw [d₁.hinter]; simp)).2
            let xH : d₁.VH := ⟨d₁.x, hxH⟩
            let yH : d₁.VH := ⟨d₁.y, hyH⟩
            let T₁ : SimpleGraph d₁.VH :=
              (G.induce (d₁.VH : Set V)) ⊔
                SimpleGraph.fromRel (fun a b : d₁.VH => (a.1 = d₁.x ∧ b.1 = d₁.y) ∨ (a.1 = d₁.y ∧ b.1 = d₁.x))
            let embG₂₁ : G₂₁ →g G := ⟨Subtype.val, fun h => h⟩
            let QG : G.Walk d₁.x d₁.y := Q.map embG₂₁
            have hQG_path : QG.IsPath := hQ_path.map Subtype.coe_injective
            have hQG_odd : Odd QG.length := by simpa [QG] using hQ_odd
            let wQ : ZMod 4 := walkModFourWeight S.sign QG
            have hwQ_odd : wQ = 1 ∨ wQ = 3 := by
              have h2w : 2 * wQ = 2 * (QG.length : ZMod 4) := by
                have : ∀ {u v : V} (p : G.Walk u v), 2 * walkModFourWeight S.sign p = 2 * (p.length : ZMod 4) := by
                  intro u v p
                  induction p with
                  | nil => simp [walkModFourWeight]
                  | @cons a b c hab r ihr =>
                    simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, List.map_cons,
                      List.sum_cons, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at ihr ⊢
                    have h2e : 2 * modFourWeight S.sign s(a, b) = 2 := by
                      unfold modFourWeight; split_ifs <;> decide
                    linear_combination h2e + ihr
                exact this QG
              rcases hQG_odd with ⟨k, hk⟩
              have h2len : 2 * (QG.length : ZMod 4) = 2 := by
                rw [hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
                have h4 : (4 : ZMod 4) = 0 := rfl
                linear_combination (k : ZMod 4) * h4
              rw [h2len] at h2w
              fin_cases wQ <;> simp_all
            let sxy : ℤ := if wQ = 1 then 1 else -1
            have hsxy_pm : sxy = 1 ∨ sxy = -1 := by dsimp [sxy]; split_ifs <;> simp
            have hsxy_mod4 : modFourWeight (fun e : Sym2 d₁.VH =>
                if e = s(xH, yH) then sxy else S.sign (e.map Subtype.val)) s(xH, yH) = wQ := by
              simp only [modFourWeight, ↓reduceIte, sxy]
              rcases hwQ_odd with h1 | h3
              · simp [h1]
              · have hne : wQ ≠ 1 := by rw [h3]; decide
                simp [hne, h3]
            let ST : SignedGraph d₁.VH :=
              { graph := T₁
                sign := fun e => if e = s(xH, yH) then sxy else S.sign (e.map Subtype.val)
                sign_pm_one := fun e he => by
                  by_cases hxye : e = s(xH, yH)
                  · simp [hxye, hsxy_pm]
                  · simp only [hxye, ↓reduceIte]
                    rcases e with ⟨a, b⟩
                    have hGab : G.Adj a.1 b.1 := by
                      rcases he with hG | hrel
                      · exact hG
                      · exfalso; apply hxye
                        rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
                        · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
                        · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
                        · rw [Sym2.eq_swap]; exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h1) (Subtype.ext h2)
                        · exact congrArg₂ (fun u v => s(u, v)) (Subtype.ext h2) (Subtype.ext h1)
                    exact S.sign_pm_one s(a.1, b.1) hGab }
            have hST_noc : IsNOC ST := by
              rw [isNOC_iff_isNOCModFour]
              intro v c hc hc_odd
              have hS_mod4 := (isNOC_iff_isNOCModFour S).mp hnoc
              have hlift : ∀ {a b : d₁.VH} (w : T₁.Walk a b), s(xH, yH) ∉ w.edges →
                  ∃ wG : G.Walk a.1 b.1,
                    wG.length = w.length ∧
                    wG.support = w.support.map Subtype.val ∧
                    wG.edges = w.edges.map (Sym2.map Subtype.val) ∧
                    walkModFourWeight S.sign wG = walkModFourWeight ST.sign w := by
                intro a b w
                induction w with
                | nil =>
                  intro _
                  exact ⟨.nil, rfl, rfl, rfl, rfl⟩
                | @cons u v z huv r ihr =>
                  intro hnot
                  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hnot
                  have hGuv : G.Adj u.1 v.1 := by
                    rcases huv with hG | hrel
                    · exact hG
                    · exfalso; apply hnot.1
                      rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
                      · exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h1) (Subtype.ext h2)
                      · rw [Sym2.eq_swap]; exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h2) (Subtype.ext h1)
                      · rw [Sym2.eq_swap]; exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h1) (Subtype.ext h2)
                      · exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h2) (Subtype.ext h1)
                  obtain ⟨rG, hrlen, hrsupp, hredges, hrwt⟩ := ihr hnot.2
                  refine ⟨SimpleGraph.Walk.cons hGuv rG, by simp [hrlen], by simp [hrsupp],
                    by simp [hredges], ?_⟩
                  simp only [walkModFourWeight, SimpleGraph.Walk.edges_cons, List.map_cons,
                    List.sum_cons] at hrwt ⊢
                  have hne_uv : s(u, v) ≠ s(xH, yH) := Ne.symm hnot.1
                  have hs_eq : ST.sign s(u, v) = S.sign s(u.1, v.1) := by
                    simp [ST, hne_uv]
                  have hm_eq : modFourWeight S.sign s(u.1, v.1) = modFourWeight ST.sign s(u, v) := by
                    unfold modFourWeight; rw [hs_eq]
                  rw [hm_eq, hrwt]
              by_cases huse : s(xH, yH) ∈ c.edges
              · obtain ⟨p, hp_path, hp_noxy, hp_len, hp_wt⟩ := cycle_split_at_edge c hc huse
                obtain ⟨pG, hplen, hpsupp, _, hpwt⟩ := hlift p hp_noxy
                have hpG_path : pG.IsPath := by
                  rw [SimpleGraph.Walk.isPath_def, hpsupp]
                  exact hp_path.support_nodup.map Subtype.coe_injective
                have hdisj : ∀ w ∈ QG.support, w ≠ d₁.x → w ≠ d₁.y → w ∉ pG.support := by
                  intro w hwQ hwx hwy hwp
                  rw [SimpleGraph.Walk.support_map, List.mem_map] at hwQ
                  rw [hpsupp, List.mem_map] at hwp
                  rcases hwQ with ⟨w₂, _, rfl⟩
                  rcases hwp with ⟨w₁, _, heq⟩
                  have hinter : w₂.1 ∈ d₁.VH ∩ d₁.VG₂ := Finset.mem_inter.mpr ⟨heq ▸ w₁.2, w₂.2⟩
                  rw [d₁.hinter] at hinter
                  simp [hwx, hwy] at hinter
                have hsum_odd : Odd (QG.length + pG.length) := by
                  rcases hQG_odd with ⟨a, ha⟩
                  rcases hc_odd with ⟨b, hb⟩
                  have : pG.length + 1 = c.length := by omega
                  exact ⟨a + b, by omega⟩
                have hlen3 : 3 ≤ QG.length + pG.length := by
                  have h1 : 1 ≤ QG.length := by
                    cases h : QG with | nil => exact absurd rfl d₁.hxy | cons _ _ => simp
                  have h2 : 1 ≤ pG.length := by
                    cases h : pG with | nil => exact absurd rfl d₁.hxy | cons _ _ => simp
                  rcases hsum_odd with ⟨k, hk⟩; omega
                have hcycG : (QG.append pG.reverse).IsCycle :=
                  isCycle_append_reverse_of_disjoint pG QG hpG_path hQG_path hdisj hlen3
                have hnocG := hS_mod4 d₁.x (QG.append pG.reverse) hcycG
                  (by simpa [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using hsum_odd)
                rw [walkModFourWeight_append, walkModFourWeight_reverse, hpwt] at hnocG
                rw [hp_wt ST.sign]
                have h1 : modFourWeight ST.sign s(xH, yH) = wQ := hsxy_mod4
                rw [h1]
                exact hnocG
              · obtain ⟨cG, hclen, hcsupp, hcedges, hcwt⟩ := hlift c huse
                have hcG_cyc : cG.IsCycle := by
                  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
                  · rw [hcedges]; exact hc.edges_nodup.map (Sym2.map.injective Subtype.coe_injective)
                  · intro hnil
                    have : c.length = 0 := by rw [← hclen, hnil]; rfl
                    exact hc.ne_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr this)
                  · rw [hcsupp, ← List.map_tail]
                    exact hc.support_nodup.map Subtype.coe_injective
                rw [← hcwt]
                exact hS_mod4 v.1 cG hcG_cyc (hclen.symm ▸ hc_odd)
            have hT₁_card : 4 ≤ Fintype.card d₁.VH := by rw [Fintype.card_coe]; exact d₁.hcardH
            have hT₁_conn : T₁.Preconnected := by
              have h0 := d₁.hT_3conn ∅ (by simp)
              intro a b
              have ha : a ∈ ((∅ : Finset d₁.VH)ᶜ : Set d₁.VH) := by simp
              have hb : b ∈ ((∅ : Finset d₁.VH)ᶜ : Set d₁.VH) := by simp
              obtain ⟨w⟩ := h0 ⟨a, ha⟩ ⟨b, hb⟩
              exact ⟨w.map (SimpleGraph.Embedding.induce _).toHom⟩
            have hT₁_nb : ¬ T₁.IsBipartite := by
              intro hTbip
              apply hH₁_nb
              rcases hTbip with ⟨f⟩
              exact ⟨SimpleGraph.Coloring.mk f (fun h => f.valid h.1)⟩
            have hxyH : xH ≠ yH := fun h => d₁.hxy (congrArg Subtype.val h)
            have hT₁_xy : T₁.Adj xH yH := by
              right; exact ⟨hxyH, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
            have hno_cross_A : ∀ u ∈ d₁.VH, ∀ w ∈ d₁.VG₂, u ≠ d₁.x → u ≠ d₁.y →
                w ≠ d₁.x → w ≠ d₁.y → A u w = 0 := by
              intro u hu w hw hux huy hwx hwy
              by_contra hne
              have huw : u ≠ w := by
                intro heq; subst heq
                have : u ∈ d₁.VH ∩ d₁.VG₂ := Finset.mem_inter.mpr ⟨hu, hw⟩
                rw [d₁.hinter] at this; simp [hux, huy] at this
              exact d₁.hno_cross u hu w hw hux huy hwx hwy ⟨huw, hne⟩
            rcases three_connected_non_bipartite_noc_classification ST hT₁_card hT₁_conn
                d₁.hT_3conn hT₁_nb hST_noc with hk4 | hpet
            · -- Case K₄ leaf → k4_leaf_reduction (Lemma 5.1(2))
              rcases hk4 with ⟨e, _, _⟩
              have hcardH : d₁.VH.card = 4 := by
                rw [← Fintype.card_coe]
                exact (Fintype.card_congr e.toEquiv).trans (Fintype.card_fin 4)
              obtain ⟨φ, hφ0, hφ1⟩ := k4_pair_equiv (e xH) (e yH) (e.injective.ne hxyH)
              let eH : Fin 4 ≃ d₁.VH := (e.toEquiv.trans φ).symm
              have he0 : (eH 0).1 = d₁.x := by
                have : eH 0 = xH := by
                  apply (e.toEquiv.trans φ).injective
                  simp [eH, hφ0]
                exact congrArg Subtype.val this
              have he1 : (eH 1).1 = d₁.y := by
                have : eH 1 = yH := by
                  apply (e.toEquiv.trans φ).injective
                  simp [eH, hφ1]
                exact congrArg Subtype.val this
              have hA_ne : ∀ i j : Fin 4, i ≠ j → ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
                  A (eH i).1 (eH j).1 ≠ 0 := by
                intro i j hij hnot01
                have hTadj : T₁.Adj (eH i) (eH j) := by
                  rw [← e.map_rel_iff]
                  show (⊤ : SimpleGraph (Fin 4)).Adj (e (eH i)) (e (eH j))
                  exact e.injective.ne (eH.injective.ne hij)
                have hGadj : G.Adj (eH i).1 (eH j).1 := by
                  rcases hTadj with hG | hrel
                  · exact hG
                  · exfalso; apply hnot01
                    rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
                    · left; exact ⟨eH.injective (Subtype.ext (h1.trans he0.symm)),
                        eH.injective (Subtype.ext (h2.trans he1.symm))⟩
                    · right; exact ⟨eH.injective (Subtype.ext (h1.trans he1.symm)),
                        eH.injective (Subtype.ext (h2.trans he0.symm))⟩
                    · right; exact ⟨eH.injective (Subtype.ext (h2.trans he1.symm)),
                        eH.injective (Subtype.ext (h1.trans he0.symm))⟩
                    · left; exact ⟨eH.injective (Subtype.ext (h2.trans he0.symm)),
                        eH.injective (Subtype.ext (h1.trans he1.symm))⟩
                exact hGadj.2
              exact k4_leaf_reduction A hA hdiag hnoc d₁.x d₁.y d₁.hxy d₁.VH d₁.VG₂
                d₁.hunion d₁.hinter hcardH hno_cross_A
                ⟨eH, he0, he1,
                  hA_ne 2 3 (by decide) (by decide),
                  hA_ne 0 2 (by decide) (by decide),
                  hA_ne 0 3 (by decide) (by decide),
                  hA_ne 1 2 (by decide) (by decide),
                  hA_ne 1 3 (by decide) (by decide)⟩
                (fun W _ _ hWcard B hB hBdiag hBnoc =>
                  ih (Fintype.card W) (by omega) W rfl B hB hBdiag hBnoc)
            · -- Case Petersen leaf → petersen_leaf_reduction (Lemma 5.2(2))
              rcases hpet with ⟨e, T_sw, hT_sw⟩
              have hcardH : d₁.VH.card = 10 := by
                rw [← Fintype.card_coe]
                exact (Fintype.card_congr e.toEquiv).trans (Fintype.card_fin 10)
              have hpet_xy : petersenGraph.Adj (e xH) (e yH) := e.map_rel_iff.mpr hT₁_xy
              obtain ⟨φ, hφ0, hφ1⟩ := petersenGraph_edge_transitive (e xH) (e yH) hpet_xy
              let eIso : T₁ ≃g petersenGraph := e.trans φ
              let eH : Fin 10 ≃ d₁.VH := eIso.toEquiv.symm
              have he0 : (eH 0).1 = d₁.x := by
                have : eH 0 = xH := by
                  apply eIso.injective
                  simp [eH, eIso, hφ0]
                exact congrArg Subtype.val this
              have he1 : (eH 1).1 = d₁.y := by
                have : eH 1 = yH := by
                  apply eIso.injective
                  simp [eH, eIso, hφ1]
                exact congrArg Subtype.val this
              let T_V : Finset V := T_sw.map ⟨Subtype.val, Subtype.coe_injective⟩
              have hTV_mem : ∀ u : d₁.VH, u.1 ∈ T_V ↔ u ∈ T_sw := by
                intro u; simp [T_V]
              have hH_edges : ∀ (i j : Fin 10), i ≠ j → ¬((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
                  if petersenGraph.Adj i j then
                    (if (eH i).1 ∈ T_V then (-1 : ℝ) else 1) *
                    (if (eH j).1 ∈ T_V then -1 else 1) * A (eH i).1 (eH j).1 < 0
                  else A (eH i).1 (eH j).1 = 0 := by
                intro i j hij hnot01
                have hne_xy : s(eH i, eH j) ≠ s(xH, yH) := by
                  intro hsym
                  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hsym
                  apply hnot01
                  rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · left; exact ⟨eH.injective (Subtype.ext ((congrArg Subtype.val h1).trans he0.symm)),
                      eH.injective (Subtype.ext ((congrArg Subtype.val h2).trans he1.symm))⟩
                  · right; exact ⟨eH.injective (Subtype.ext ((congrArg Subtype.val h1).trans he1.symm)),
                      eH.injective (Subtype.ext ((congrArg Subtype.val h2).trans he0.symm))⟩
                split_ifs with hp_adj
                · have hTadj : T₁.Adj (eH i) (eH j) := by
                    rw [← eIso.map_rel_iff]
                    simpa [eH] using hp_adj
                  have hGadj : G.Adj (eH i).1 (eH j).1 := by
                    rcases hTadj with hG | hrel
                    · exact hG
                    · exfalso; apply hne_xy
                      rcases hrel.2 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
                      · exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h1) (Subtype.ext h2)
                      · rw [Sym2.eq_swap]; exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h2) (Subtype.ext h1)
                      · rw [Sym2.eq_swap]; exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h1) (Subtype.ext h2)
                      · exact congrArg₂ (fun p q => s(p, q)) (Subtype.ext h2) (Subtype.ext h1)
                  have hsw := hT_sw (eH i) (eH j) hTadj
                  simp only [ST, hne_xy, ↓reduceIte, petersenSignedGraph] at hsw
                  have hsign_eq : S.sign s((eH i).1, (eH j).1) =
                      if 0 < A (eH i).1 (eH j).1 then 1 else -1 := rfl
                  rw [hsign_eq] at hsw
                  rw [hTV_mem (eH i), hTV_mem (eH j)]
                  have hAne : A (eH i).1 (eH j).1 ≠ 0 := hGadj.2
                  by_cases hi : eH i ∈ T_sw <;> by_cases hj : eH j ∈ T_sw <;>
                    by_cases hpos : 0 < A (eH i).1 (eH j).1 <;>
                    simp_all <;> linarith [lt_or_gt_of_ne hAne]
                · by_contra hAne
                  have hGadj : G.Adj (eH i).1 (eH j).1 :=
                    ⟨fun heq => hij (eH.injective (Subtype.ext heq)), hAne⟩
                  have hTadj : T₁.Adj (eH i) (eH j) := Or.inl hGadj
                  exact hp_adj (by simpa [eH] using eIso.map_rel_iff.mpr hTadj)
              exact petersen_leaf_reduction A hA hdiag hnoc d₁.x d₁.y d₁.hxy d₁.VH d₁.VG₂
                d₁.hunion d₁.hinter hcardH hno_cross_A
                ⟨eH, T_V, he0, he1, hH_edges⟩
                (fun W _ _ hWcard B hB hBdiag hBnoc =>
                  ih (Fintype.card W) (by omega) W rfl B hB hBdiag hBnoc)
        · -- Step 4b: There is a vertex v with degree 2 → degree_two_reduction
          push Not at hdeg3
          rcases hdeg3 with ⟨v, hv_lt3⟩
          have hv2 : (G.neighborFinset v).card = 2 := by
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            have := hdeg2 v; omega
          rcases Finset.card_eq_two.mp hv2 with ⟨x, y, hxy, hNxy⟩
          have hvx : v ≠ x := G.ne_of_adj ((G.mem_neighborFinset v x).mp (by rw [hNxy]; simp))
          have hvy : v ≠ y := G.ne_of_adj ((G.mem_neighborFinset v y).mp (by rw [hNxy]; simp))
          have hN : ∀ w, G.Adj v w ↔ w = x ∨ w = y := by
            intro w
            rw [← G.mem_neighborFinset v w, hNxy, Finset.mem_insert, Finset.mem_singleton]
          exact degree_two_reduction A hA hdiag hnoc hn3 v x y hxy hvx hvy hN
            (fun W _ _ hWcard B hB hBdiag hBnoc =>
              ih (Fintype.card W) (by omega) W rfl B hB hBdiag hBnoc)
      · -- Step 3b: There is a cut-vertex v → cut_vertex_reduction
        push Not at h2conn
        rcases h2conn with ⟨v, hv_disc⟩
        unfold SimpleGraph.Preconnected at hv_disc
        push Not at hv_disc
        rcases hv_disc with ⟨u₀, v₀, huv₀⟩
        let Gv := G.induce ({v}ᶜ : Set V)
        let C₁ : Finset V :=
          Finset.univ.filter fun w => ∃ hw : w ∈ ({v}ᶜ : Set V), Gv.Reachable u₀ ⟨w, hw⟩
        let V₁ : Finset V := insert v C₁
        let V₂ : Finset V := insert v ((Finset.univ.erase v) \ C₁)
        have hv_nC₁ : v ∉ C₁ := by
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
          intro hw; exact absurd rfl hw
        have hu₀_C₁ : u₀.1 ∈ C₁ := by
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨u₀.2, SimpleGraph.Reachable.refl _⟩
        have hv₀_nC₁ : v₀.1 ∉ C₁ := by
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
          intro hw hreach; exact huv₀ hreach
        have hunion : V₁ ∪ V₂ = Finset.univ := by
          ext w; simp only [V₁, V₂, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff,
            Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
          by_cases hwv : w = v
          · exact Or.inl (Or.inl hwv)
          · by_cases hwC : w ∈ C₁
            · exact Or.inl (Or.inr hwC)
            · exact Or.inr (Or.inr ⟨hwv, hwC⟩)
        have hinter : V₁ ∩ V₂ = {v} := by
          ext w; simp only [V₁, V₂, Finset.mem_inter, Finset.mem_insert, Finset.mem_sdiff,
            Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | h1, rfl | ⟨_, h2⟩⟩ <;> tauto
          · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
        have hcard₁ : V₁.card < Fintype.card V := by
          rw [← Finset.card_univ]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
          refine ⟨v₀.1, Finset.mem_univ _, ?_⟩
          simp only [V₁, Finset.mem_insert, not_or]
          exact ⟨v₀.2, hv₀_nC₁⟩
        have hcard₂ : V₂.card < Fintype.card V := by
          rw [← Finset.card_univ]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
          refine ⟨u₀.1, Finset.mem_univ _, ?_⟩
          simp only [V₂, Finset.mem_insert, Finset.mem_sdiff, not_or]
          exact ⟨u₀.2, fun h => h.2 hu₀_C₁⟩
        have hno_cross : ∀ u ∈ V₁, ∀ w ∈ V₂, u ≠ v → w ≠ v → A u w = 0 := by
          intro u hu w hw huv hwv
          by_contra hne
          have hadj : G.Adj u w := ⟨fun heq => by
            subst heq
            have : u ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hu, hw⟩
            rw [hinter, Finset.mem_singleton] at this
            exact huv this, hne⟩
          have huC₁ : u ∈ C₁ := by
            simp only [V₁, Finset.mem_insert] at hu
            exact hu.resolve_left huv
          have hw_nC₁ : w ∉ C₁ := by
            simp only [V₂, Finset.mem_insert, Finset.mem_sdiff] at hw
            exact (hw.resolve_left hwv).2
          simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and] at huC₁
          rcases huC₁ with ⟨hu_nv, hru⟩
          have hstep : Gv.Adj ⟨u, hu_nv⟩ ⟨w, hwv⟩ := hadj
          exact hw_nC₁ (by
            simp only [C₁, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hwv, hru.trans hstep.reachable⟩)
        exact cut_vertex_reduction A hA hdiag hnoc v V₁ V₂ hunion hinter hcard₁ hcard₂ hno_cross
          (fun W _ _ hWcard B hB hBdiag hBnoc =>
            ih (Fintype.card W) (by omega) W rfl B hB hBdiag hBnoc)
    · -- Step 2b: G is disconnected → block diagonal split
      unfold SimpleGraph.Preconnected at hconn
      push Not at hconn
      rcases hconn with ⟨u₀, v₀, huv₀⟩
      let C₁ : Finset V := Finset.univ.filter fun w => G.Reachable u₀ w
      let C₂ : Finset V := Finset.univ \ C₁
      have hu₀_C₁ : u₀ ∈ C₁ := by simp [C₁]
      have hv₀_C₂ : v₀ ∈ C₂ := by simp [C₂, C₁, huv₀]
      have hcard₁ : Fintype.card C₁ < Fintype.card V := by
        rw [Fintype.card_coe, ← Finset.card_univ]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨v₀, Finset.mem_univ _, by simp [C₁, huv₀]⟩
      have hcard₂ : Fintype.card C₂ < Fintype.card V := by
        rw [Fintype.card_coe, ← Finset.card_univ]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨u₀, Finset.mem_univ _, by simp [C₂, hu₀_C₁]⟩
      let e : C₁ ⊕ C₂ ≃ V :=
        { toFun := fun s => match s with | Sum.inl a => a.1 | Sum.inr b => b.1
          invFun := fun v => if hv : v ∈ C₁ then Sum.inl ⟨v, hv⟩
            else Sum.inr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩⟩
          left_inv := fun s => by
            cases s with
            | inl a => simp [a.2]
            | inr b =>
              have hb : b.1 ∉ C₁ := (Finset.mem_sdiff.mp b.2).2
              simp [hb]
          right_inv := fun v => by by_cases hv : v ∈ C₁ <;> simp [hv] }
      let A₁ : Matrix C₁ C₁ ℝ := A.submatrix Subtype.val Subtype.val
      let A₂ : Matrix C₂ C₂ ℝ := A.submatrix Subtype.val Subtype.val
      have hA₁ : A₁.IsHermitian := isHermitian_submatrix A hA Subtype.val
      have hA₂ : A₂.IsHermitian := isHermitian_submatrix A hA Subtype.val
      have hblk : A.submatrix e e = Matrix.fromBlocks A₁ 0 0 A₂ := by
        ext x y
        cases x with
        | inl a =>
          cases y with
          | inl b => rfl
          | inr b =>
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, e]
            by_contra hne
            have hadj : G.Adj a.1 b.1 := ⟨fun heq => (Finset.mem_sdiff.mp b.2).2 (heq ▸ a.2), hne⟩
            have hreach : G.Reachable u₀ b.1 :=
              ((Finset.mem_filter.mp a.2).2).trans hadj.reachable
            exact (Finset.mem_sdiff.mp b.2).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach⟩)
        | inr a =>
          cases y with
          | inl b =>
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, e]
            by_contra hne
            have hadj : G.Adj b.1 a.1 := ⟨fun heq => (Finset.mem_sdiff.mp a.2).2 (heq ▸ b.2),
              by rw [hA.isSymm.apply]; exact hne⟩
            have hreach : G.Reachable u₀ a.1 :=
              ((Finset.mem_filter.mp b.2).2).trans hadj.reachable
            exact (Finset.mem_sdiff.mp a.2).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach⟩)
          | inr b => rfl
      have hs1 : signature A₁ hA₁ ≤ 0 :=
        ih (Fintype.card C₁) (by omega) C₁ rfl A₁ hA₁ (fun a => hdiag a.1)
          (matrixIsNOC_submatrix_injective A hA.isSymm hnoc Subtype.val Subtype.coe_injective hA₁.isSymm)
      have hs2 : signature A₂ hA₂ ≤ 0 :=
        ih (Fintype.card C₂) (by omega) C₂ rfl A₂ hA₂ (fun b => hdiag b.1)
          (matrixIsNOC_submatrix_injective A hA.isSymm hnoc Subtype.val Subtype.coe_injective hA₂.isSymm)
      rw [← signature_reindex e A hA,
          signature_eq_of_eq_mat _ (isHermitian_fromBlocks A₁ hA₁ A₂ hA₂) hblk,
          signature_fromBlocks A₁ hA₁ A₂ hA₂]
      omega

end Theorem12Helpers

/-- **Theorem 1.2**: Every real symmetric zero-diagonal NOC matrix `A` satisfies `s(A) ≤ 0`. -/
theorem theorem_1_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0) (hnoc : MatrixIsNOC A hA.isSymm) :
    signature A hA ≤ 0 :=
  theorem_1_2_general n (Fin n) (Fintype.card_fin n) A hA hdiag hnoc

section Corollary13

private lemma matSig_eq_signature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Challenge.matSig A hA = signature A hA := by
  unfold Challenge.matSig signature posInertia negInertia
  have h1 : (Finset.univ.filter fun i : Fin n => 0 < hA.eigenvalues i) =
      @Finset.filter (Fin n) (fun i => 0 < hA.eigenvalues i) (Classical.decPred _) Finset.univ := by
    ext i; simp
  have h2 : (Finset.univ.filter fun i : Fin n => hA.eigenvalues i < 0) =
      @Finset.filter (Fin n) (fun i => hA.eigenvalues i < 0) (Classical.decPred _) Finset.univ := by
    ext i; simp
  congr 1 <;> congr 1 <;> ext i <;> simp

private lemma cycle_of_eq_graph {V : Type*} {G₁ G₂ : SimpleGraph V} (h : G₁ = G₂)
    {v : V} (c : G₁.Walk v v) (hc : c.IsCycle) :
    ∃ c' : G₂.Walk v v, c'.IsCycle ∧ c'.length = c.length ∧ c'.edges = c.edges := by
  subst h; exact ⟨c, hc, rfl, rfl⟩

private lemma matrixGraph_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    matrixGraph (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) = G := by
  ext i j
  simp only [matrixGraph, SimpleGraph.adjMatrix_apply]
  constructor
  · rintro ⟨_, hne⟩
    by_contra h
    simp [h] at hne
  · intro h
    exact ⟨G.ne_of_adj h, by simp [h]⟩

private lemma matrixGraph_neg_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    matrixGraph (-(G.adjMatrix ℝ))
      (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm = G := by
  ext i j
  simp only [matrixGraph, Matrix.neg_apply, SimpleGraph.adjMatrix_apply]
  constructor
  · rintro ⟨_, hne⟩
    by_contra h
    simp [h] at hne
  · intro h
    exact ⟨G.ne_of_adj h, by simp [h]⟩

private lemma walk_map_isCycle {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (hφ : Function.Injective φ) {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    (c.map φ).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_map]
    exact hc.edges_nodup.map (Sym2.map.injective hφ)
  · intro hnil
    have hlen : (c.map φ).length = 0 := by rw [hnil]; rfl
    rw [SimpleGraph.Walk.length_map] at hlen
    exact hc.ne_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hlen)
  · rw [SimpleGraph.Walk.support_map, List.map_tail]
    exact hc.support_nodup.map hφ

private lemma cycleCountMod4_comap_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (r : ℕ) (v₀ : Fin n) (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle) (hr₀ : c₀.length % 4 = r)
    (e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀}) :
    Challenge.cycleCountMod4 (G.comap (fun i => (e i).1)) r + 1 ≤
      Challenge.cycleCountMod4 G r := by
  classical
  let f : Fin (n - 1) → Fin n := fun i => (e i).1
  have hf : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
  have hf_ne : ∀ i, f i ≠ v₀ := fun i => (e i).2
  let G' : SimpleGraph (Fin (n - 1)) := G.comap f
  let φ : G' →g G := ⟨f, fun h => h⟩
  let s' : Finset (Finset (Sym2 (Fin (n - 1)))) :=
    Finset.univ.filter fun S =>
      ∃ (v : Fin (n - 1)) (c : G'.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r
  let s : Finset (Finset (Sym2 (Fin n))) :=
    Finset.univ.filter fun S =>
      ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ c.length % 4 = r
  let F : Finset (Sym2 (Fin (n - 1))) → Finset (Sym2 (Fin n)) :=
    fun S => S.image (Sym2.map f)
  have hF_inj : Function.Injective F :=
    Finset.image_injective (Sym2.map.injective hf)
  have hc₀_mem : c₀.edges.toFinset ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v₀, c₀, hc₀, rfl, hr₀⟩
  have hF_sub : s'.image F ⊆ s.erase c₀.edges.toFinset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨S', hS', rfl⟩
    simp only [s', Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    rcases hS' with ⟨u', c', hc', hS'_eq, hr'⟩
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      cases c₀ with
      | nil => exact hc₀.ne_nil rfl
      | @cons _ w _ hadj p =>
        have hmem : s(v₀, w) ∈ (SimpleGraph.Walk.cons hadj p).edges.toFinset := by
          simp [SimpleGraph.Walk.edges_cons]
        rw [← heq] at hmem
        rcases Finset.mem_image.mp hmem with ⟨e', _, he'⟩
        rcases e' with ⟨a, b⟩
        simp only [Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he'
        rcases he' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hf_ne a h1
        · exact hf_ne b h2
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨f u', c'.map φ, walk_map_isCycle φ hf c' hc', ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_map, List.toFinset_map, hS'_eq]
        rfl
      · simpa [SimpleGraph.Walk.length_map] using hr'
  have hcard_le : s'.card ≤ (s.erase c₀.edges.toFinset).card := by
    rw [← Finset.card_image_of_injective s' hF_inj]
    exact Finset.card_le_card hF_sub
  have herase : (s.erase c₀.edges.toFinset).card + 1 = s.card :=
    Finset.card_erase_add_one hc₀_mem
  change s'.card + 1 ≤ s.card
  omega

private lemma signature_adjMatrix_le_cycleCountMod4_one :
    ∀ (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Challenge.cycleCountMod4 G 1 ≤ k →
      signature (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤ (k : ℤ)
  | 0, n, G, _, hk => by
    have hk0 : Challenge.cycleCountMod4 G 1 = 0 := Nat.le_zero.mp hk
    apply theorem_1_2 (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)
    · intro i; simp [SimpleGraph.adjMatrix_apply, G.loopless i]
    · intro v c hc hodd
      have hG := matrixGraph_adjMatrix G
      obtain ⟨c', hc', hlen', _⟩ := cycle_of_eq_graph hG c hc
      have hne1 : c.length % 4 ≠ 1 := by
        intro h1
        have hmem : c'.edges.toFinset ∈
            (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
              ∃ (u : Fin n) (c'' : G.Walk u u), c''.IsCycle ∧ c''.edges.toFinset = S ∧
                c''.length % 4 = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, c', hc', rfl, by rw [hlen']; exact h1⟩
        have hpos : 0 < Challenge.cycleCountMod4 G 1 := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hprod1 : walkSignProd (matrixSignedGraph (G.adjMatrix ℝ)
          (SimpleGraph.isSymm_adjMatrix G)).sign c = 1 := by
        unfold walkSignProd
        apply List.prod_eq_one
        intro x hx
        rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
        have hedge : e ∈ (matrixGraph (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).edgeSet :=
          c.edges_subset_edgeSet he
        rcases e with ⟨a, b⟩
        simp only [matrixSignedGraph, Sym2.lift_mk]
        have hadj : G.Adj a b := by
          rw [hG] at hedge
          exact hedge
        simp [SimpleGraph.adjMatrix_apply, hadj]
      rcases hodd with ⟨m, hm⟩
      have hmod3 : c.length % 4 = 3 := by omega
      have hm_odd : Odd m := by
        refine ⟨m / 2, ?_⟩
        omega
      unfold signedCycleType
      rw [hprod1, mul_one, show c.length / 2 = m by omega]
      exact Odd.neg_one_pow hm_odd
  | k + 1, n, G, _, hk => by
    classical
    by_cases h0 : Challenge.cycleCountMod4 G 1 = 0
    · have hle := signature_adjMatrix_le_cycleCountMod4_one 0 G (le_of_eq h0)
      omega
    · have hpos : 0 < Challenge.cycleCountMod4 G 1 := Nat.pos_of_ne_zero h0
      obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₀
      rcases hS₀ with ⟨v₀, c₀, hc₀, _, hlen₀⟩
      have hcard_sub : Fintype.card {x : Fin n // x ≠ v₀} = n - 1 := by
        have hv : 0 < n := Fin.pos v₀
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        simp
      let e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀} :=
        (Fintype.equivFinOfCardEq hcard_sub).symm
      let G' : SimpleGraph (Fin (n - 1)) := G.comap (fun i => (e i).1)
      have hlt : Challenge.cycleCountMod4 G' 1 ≤ k := by
        have h := cycleCountMod4_comap_lt G 1 v₀ c₀ hc₀ hlen₀ e
        omega
      have hIH := signature_adjMatrix_le_cycleCountMod4_one k G' hlt
      have hinter := signature_interlacing_delete_vertex (G.adjMatrix ℝ)
        (SimpleGraph.isSymm_adjMatrix G) v₀
      have hsub_eq : ((G.adjMatrix ℝ).submatrix (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1)).submatrix e e = G'.adjMatrix ℝ := by
        ext i j
        simp [G', SimpleGraph.adjMatrix_apply]
      have hsig_sub : signature ((G.adjMatrix ℝ).submatrix
          (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1))
          (isHermitian_submatrix (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) _) =
          signature (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G') := by
        rw [← signature_reindex e _ (isHermitian_submatrix (G.adjMatrix ℝ)
          (SimpleGraph.isSymm_adjMatrix G) _)]
        have hEq : ∀ (M₁ M₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
            (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian), M₁ = M₂ →
            signature M₁ h₁ = signature M₂ h₂ := by
          intro M₁ M₂ h₁ h₂ h; subst h; rfl
        exact hEq _ _ _ _ hsub_eq
      have hle1 : signature (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) -
          signature (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G') ≤ 1 := by
        rw [← hsig_sub]
        exact (abs_le.mp hinter).2
      omega

private lemma signature_neg_adjMatrix_le_cycleCountMod4_three :
    ∀ (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Challenge.cycleCountMod4 G 3 ≤ k →
      signature (-(G.adjMatrix ℝ))
        (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)) ≤ (k : ℤ)
  | 0, n, G, _, hk => by
    have hk0 : Challenge.cycleCountMod4 G 3 = 0 := Nat.le_zero.mp hk
    apply theorem_1_2 (-(G.adjMatrix ℝ))
      (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G))
    · intro i; simp [SimpleGraph.adjMatrix_apply, G.loopless i]
    · intro v c hc hodd
      have hG := matrixGraph_neg_adjMatrix G
      obtain ⟨c', hc', hlen', _⟩ := cycle_of_eq_graph hG c hc
      have hne3 : c.length % 4 ≠ 3 := by
        intro h3
        have hmem : c'.edges.toFinset ∈
            (Finset.univ.filter fun S : Finset (Sym2 (Fin n)) =>
              ∃ (u : Fin n) (c'' : G.Walk u u), c''.IsCycle ∧ c''.edges.toFinset = S ∧
                c''.length % 4 = 3) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, c', hc', rfl, by rw [hlen']; exact h3⟩
        have hpos : 0 < Challenge.cycleCountMod4 G 3 := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hprod_neg : walkSignProd (matrixSignedGraph (-(G.adjMatrix ℝ))
          (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign c = -1 := by
        unfold walkSignProd
        have hall : ∀ x ∈ c.edges.map (matrixSignedGraph (-(G.adjMatrix ℝ))
            (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign,
            x = (-1 : ℤ) := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
          have hedge : e ∈ (matrixGraph (-(G.adjMatrix ℝ))
              (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).edgeSet :=
            c.edges_subset_edgeSet he
          rcases e with ⟨a, b⟩
          simp only [matrixSignedGraph, Sym2.lift_mk]
          have hadj : G.Adj a b := by
            rw [hG] at hedge
            exact hedge
          simp [SimpleGraph.adjMatrix_apply, hadj]
        have hmap_eq : c.edges.map (matrixSignedGraph (-(G.adjMatrix ℝ))
            (isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)).isSymm).sign =
            List.replicate c.length (-1 : ℤ) := by
          apply List.eq_replicate_iff.mpr
          exact ⟨by simp [SimpleGraph.Walk.length_edges], hall⟩
        rw [hmap_eq, List.prod_replicate]
        exact Odd.neg_one_pow hodd
      rcases hodd with ⟨m, hm⟩
      have hmod1 : c.length % 4 = 1 := by omega
      have hm_even : Even m := ⟨m / 2, by omega⟩
      unfold signedCycleType
      rw [hprod_neg, show c.length / 2 = m by omega, Even.neg_one_pow hm_even, one_mul]
  | k + 1, n, G, _, hk => by
    classical
    by_cases h0 : Challenge.cycleCountMod4 G 3 = 0
    · have hle := signature_neg_adjMatrix_le_cycleCountMod4_three 0 G (le_of_eq h0)
      omega
    · have hpos : 0 < Challenge.cycleCountMod4 G 3 := Nat.pos_of_ne_zero h0
      obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₀
      rcases hS₀ with ⟨v₀, c₀, hc₀, _, hlen₀⟩
      have hcard_sub : Fintype.card {x : Fin n // x ≠ v₀} = n - 1 := by
        have hv : 0 < n := Fin.pos v₀
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        simp
      let e : Fin (n - 1) ≃ {x : Fin n // x ≠ v₀} :=
        (Fintype.equivFinOfCardEq hcard_sub).symm
      let G' : SimpleGraph (Fin (n - 1)) := G.comap (fun i => (e i).1)
      have hlt : Challenge.cycleCountMod4 G' 3 ≤ k := by
        have h := cycleCountMod4_comap_lt G 3 v₀ c₀ hc₀ hlen₀ e
        omega
      have hIH := signature_neg_adjMatrix_le_cycleCountMod4_three k G' hlt
      have hNegH := isHermitian_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)
      have hinter := signature_interlacing_delete_vertex (-(G.adjMatrix ℝ)) hNegH v₀
      have hsub_eq : ((-(G.adjMatrix ℝ)).submatrix (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1)).submatrix e e = -(G'.adjMatrix ℝ) := by
        ext i j
        simp [G', SimpleGraph.adjMatrix_apply]
      have hsig_sub : signature ((-(G.adjMatrix ℝ)).submatrix
          (fun x : {x : Fin n // x ≠ v₀} => x.1)
          (fun x : {x : Fin n // x ≠ v₀} => x.1))
          (isHermitian_submatrix (-(G.adjMatrix ℝ)) hNegH _) =
          signature (-(G'.adjMatrix ℝ))
            (isHermitian_neg (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G')) := by
        rw [← signature_reindex e _ (isHermitian_submatrix (-(G.adjMatrix ℝ)) hNegH _)]
        have hEq : ∀ (M₁ M₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
            (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian), M₁ = M₂ →
            signature M₁ h₁ = signature M₂ h₂ := by
          intro M₁ M₂ h₁ h₂ h; subst h; rfl
        exact hEq _ _ _ _ hsub_eq
      have hle1 : signature (-(G.adjMatrix ℝ)) hNegH -
          signature (-(G'.adjMatrix ℝ))
            (isHermitian_neg (G'.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G')) ≤ 1 := by
        rw [← hsig_sub]
        exact (abs_le.mp hinter).2
      omega

end Corollary13

/-- **Corollary 1.3 (Ma–Yang–Li Conjecture)**: Every finite simple graph `G` satisfies
`-c₃(G) ≤ s(G) ≤ c₅(G)`. -/
theorem corollary_1_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    -(Challenge.cycleCountMod4 G 3 : ℤ) ≤
      Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ∧
    Challenge.matSig (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G) ≤
      (Challenge.cycleCountMod4 G 1 : ℤ) := by
  rw [matSig_eq_signature]
  constructor
  · have hneg := signature_neg_adjMatrix_le_cycleCountMod4_three (Challenge.cycleCountMod4 G 3) G le_rfl
    rw [signature_neg (G.adjMatrix ℝ) (SimpleGraph.isSymm_adjMatrix G)] at hneg
    omega
  · exact signature_adjMatrix_le_cycleCountMod4_one (Challenge.cycleCountMod4 G 1) G le_rfl

end SignedGraphs
