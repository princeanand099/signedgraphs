import Mathlib

/-!
# Signed Graphs, NOC Condition, and Matrix Signature

Foundational definitions for the Ma–Yang–Li signature conjecture via weighted signed graphs
(Definition 1.1, mod-4 weight interpretation, inertia, and signature).
-/

open Matrix SimpleGraph

namespace SignedGraphs

section MatrixSignature

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of strictly positive eigenvalues of a real symmetric matrix `A`,
counted with multiplicity. -/
noncomputable def posInertia (A : Matrix V V ℝ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i : V => 0 < hA.eigenvalues i).card

/-- Number of zero eigenvalues of a real symmetric matrix `A`,
counted with multiplicity. -/
noncomputable def zeroInertia (A : Matrix V V ℝ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i : V => hA.eigenvalues i = 0).card

/-- Number of strictly negative eigenvalues of a real symmetric matrix `A`,
counted with multiplicity. -/
noncomputable def negInertia (A : Matrix V V ℝ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i : V => hA.eigenvalues i < 0).card

/-- The signature `s(A) = n₊(A) - n₋(A)` of a real symmetric matrix `A`. -/
noncomputable def signature (A : Matrix V V ℝ) (hA : A.IsHermitian) : ℤ :=
  (posInertia A hA : ℤ) - (negInertia A hA : ℤ)

/-- Inertia partition: `n₊(A) + n₀(A) + n₋(A) = |V|`. -/
theorem inertia_sum (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    posInertia A hA + zeroInertia A hA + negInertia A hA = Fintype.card V := by
  classical
  unfold posInertia zeroInertia negInertia
  have h1 : Disjoint
      (Finset.univ.filter fun i : V => 0 < hA.eigenvalues i)
      (Finset.univ.filter fun i : V => hA.eigenvalues i = 0) := by
    rw [Finset.disjoint_filter]
    intro i _ hpos hzero
    linarith
  have h2 : Disjoint
      ((Finset.univ.filter fun i : V => 0 < hA.eigenvalues i) ∪
        (Finset.univ.filter fun i : V => hA.eigenvalues i = 0))
      (Finset.univ.filter fun i : V => hA.eigenvalues i < 0) := by
    rw [Finset.disjoint_left]
    intro i hi hneg
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi hneg
    rcases hi with hpos | hzero <;> linarith
  rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rcases lt_trichotomy 0 (hA.eigenvalues i) with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h.symm)
  · exact Or.inr h

end MatrixSignature

section SignedGraphDefs

variable {V : Type*}

/-- A signed graph `(G, σ)` consists of a simple graph `G` together with a sign assignment
`σ : Sym2 V → ℤ` taking values in `{+1, -1}` on edges of `G`. -/
structure SignedGraph (V : Type*) where
  graph : SimpleGraph V
  sign : Sym2 V → ℤ
  sign_pm_one : ∀ e ∈ graph.edgeSet, sign e = 1 ∨ sign e = -1

/-- The mod-4 edge weight `w_σ(e) ∈ ZMod 4`: `1` if `σ(e) = +1`, `3` if `σ(e) = -1`. -/
def modFourWeight (σ : Sym2 V → ℤ) (e : Sym2 V) : ZMod 4 :=
  if σ e = 1 then 1 else 3

/-- The mod-4 weight of a walk `p` in `G`. -/
def walkModFourWeight {G : SimpleGraph V} (σ : Sym2 V → ℤ) {u v : V} (p : G.Walk u v) : ZMod 4 :=
  (p.edges.map (modFourWeight σ)).sum

/-- The sign product of a walk `p` in `G`. -/
def walkSignProd {G : SimpleGraph V} (σ : Sym2 V → ℤ) {u v : V} (p : G.Walk u v) : ℤ :=
  (p.edges.map σ).prod

/-- Signed cycle type `ϵ(C) = (-1)^k ∏_{e ∈ C} σ(e)` for an odd cycle of length `2k + 1`. -/
def signedCycleType {G : SimpleGraph V} (σ : Sym2 V → ℤ) {v : V} (c : G.Walk v v) : ℤ :=
  (-1) ^ (c.length / 2) * walkSignProd σ c

/-- Definition 1.1 (NOC): `(G, σ)` is negative-odd-cycle if every odd cycle `C` has `ϵ(C) = -1`. -/
def IsNOC (S : SignedGraph V) : Prop :=
  ∀ (v : V) (c : S.graph.Walk v v), c.IsCycle → Odd c.length →
    signedCycleType S.sign c = -1

/-- Equivalent mod-4 characterization of NOC: every odd cycle has mod-4 weight `3`. -/
def IsNOCModFour (S : SignedGraph V) : Prop :=
  ∀ (v : V) (c : S.graph.Walk v v), c.IsCycle → Odd c.length →
    walkModFourWeight S.sign c = 3

private lemma list_modFourWeight_and_prod (σ : Sym2 V → ℤ) :
    ∀ (l : List (Sym2 V)), (∀ e ∈ l, σ e = 1 ∨ σ e = -1) →
      (l.map (modFourWeight σ)).sum =
        (l.length : ZMod 4) + 2 * ((l.countP (fun e => decide (σ e = -1)) : ℕ) : ZMod 4) ∧
      (l.map σ).prod = (-1 : ℤ) ^ (l.countP (fun e => decide (σ e = -1)))
  | [], _ => by simp
  | e :: l, hl => by
    have he : σ e = 1 ∨ σ e = -1 := hl e (by simp)
    have hl' : ∀ x ∈ l, σ x = 1 ∨ σ x = -1 := fun x hx => hl x (by simp [hx])
    obtain ⟨ih1, ih2⟩ := list_modFourWeight_and_prod σ l hl'
    simp only [List.map_cons, List.sum_cons, List.prod_cons, List.length_cons,
      List.countP_cons, Nat.cast_add, Nat.cast_one]
    rw [ih1, ih2]
    rcases he with h1 | hneg
    · have hif : (if decide (σ e = -1) = true then (1 : ℕ) else 0) = 0 := by
        simp [h1]
      have hw : modFourWeight σ e = 1 := by simp [modFourWeight, h1]
      rw [hw, hif, h1]
      refine ⟨by push_cast; ring, by simp⟩
    · have hif : (if decide (σ e = -1) = true then (1 : ℕ) else 0) = 1 := by
        simp [hneg]
      have hw : modFourWeight σ e = 3 := by simp [modFourWeight, hneg]
      rw [hw, hif, hneg]
      refine ⟨by push_cast; ring, by rw [pow_succ']⟩

private lemma neg_one_pow_eq_neg_one_iff' (n : ℕ) : (-1 : ℤ) ^ n = -1 ↔ Odd n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have : (-1 : ℤ) ^ (m + m) = 1 := by rw [← two_mul, pow_mul]; norm_num
    rw [this]
    constructor
    · intro h; contradiction
    · intro h; exfalso; exact (Nat.not_odd_iff_even.mpr ⟨m, rfl⟩) h
  · subst hm
    have : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
    rw [this]
    exact ⟨fun _ => ⟨m, rfl⟩, fun _ => rfl⟩

/-- An odd cycle `C` has `ϵ(C) = -1` if and only if `w_σ(C) = 3` in `ZMod 4`. -/
theorem signedCycleType_eq_neg_one_iff_modFourWeight_eq_three (S : SignedGraph V)
    {v : V} (c : S.graph.Walk v v) (hodd : Odd c.length) :
    signedCycleType S.sign c = -1 ↔ walkModFourWeight S.sign c = 3 := by
  have hl : ∀ e ∈ c.edges, S.sign e = 1 ∨ S.sign e = -1 := fun e he =>
    S.sign_pm_one e (c.edges_subset_edgeSet he)
  obtain ⟨hw, hp⟩ := list_modFourWeight_and_prod S.sign c.edges hl
  have hlen : c.edges.length = c.length := SimpleGraph.Walk.length_edges c
  rcases hodd with ⟨k, hk⟩
  have hdiv : c.length / 2 = k := by omega
  unfold signedCycleType walkModFourWeight walkSignProd
  rw [hw, hp, hlen, hdiv, hk]
  set r := c.edges.countP (fun e => decide (S.sign e = -1))
  have hpow : (-1 : ℤ) ^ k * (-1 : ℤ) ^ r = (-1 : ℤ) ^ (k + r) := by rw [← pow_add]
  rw [hpow, neg_one_pow_eq_neg_one_iff']
  constructor
  · intro hkr
    rcases hkr with ⟨m, hm⟩
    have : ((2 * k + 1 : ℕ) : ZMod 4) + 2 * (r : ZMod 4) =
        ((2 * (k + r) + 1 : ℕ) : ZMod 4) := by push_cast; ring
    rw [this, hm]
    have h4 : ((2 * (2 * m + 1) + 1 : ℕ) : ZMod 4) = 4 * (m : ZMod 4) + 3 := by
      push_cast; ring
    rw [h4]
    have h4z : (4 : ZMod 4) = 0 := rfl
    rw [h4z, zero_mul, zero_add]
  · intro hmod
    by_cases hev : Even (k + r)
    · rcases hev with ⟨m, hm⟩
      have hkr2 : k + r = 2 * m := by omega
      have h4 : ((2 * k + 1 : ℕ) : ZMod 4) + 2 * (r : ZMod 4) =
          ((2 * (k + r) + 1 : ℕ) : ZMod 4) := by push_cast; ring
      rw [h4, hkr2] at hmod
      have h4m : ((2 * (2 * m) + 1 : ℕ) : ZMod 4) = 4 * (m : ZMod 4) + 1 := by
        push_cast; ring
      rw [h4m] at hmod
      have h4z : (4 : ZMod 4) = 0 := rfl
      rw [h4z, zero_mul, zero_add] at hmod
      exfalso
      revert hmod
      decide
    · exact Nat.not_even_iff_odd.mp hev

/-- Equivalence between `IsNOC` and `IsNOCModFour` (Section 1, p. 2). -/
theorem isNOC_iff_isNOCModFour (S : SignedGraph V) : IsNOC S ↔ IsNOCModFour S := by
  constructor
  · intro h v c hc hodd
    exact (signedCycleType_eq_neg_one_iff_modFourWeight_eq_three S c hodd).mp (h v c hc hodd)
  · intro h v c hc hodd
    exact (signedCycleType_eq_neg_one_iff_modFourWeight_eq_three S c hodd).mpr (h v c hc hodd)

/-- Underlying simple graph of a real symmetric matrix `A`. -/
def matrixGraph (A : Matrix V V ℝ) (hA : A.IsSymm) : SimpleGraph V where
  Adj u v := u ≠ v ∧ A u v ≠ 0
  symm := ⟨fun u v h => by
    have hsym : A v u = A u v := congrFun (congrFun hA u) v
    exact ⟨h.1.symm, by rw [hsym]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Underlying signed graph `(G(A), σ_A)` of a real symmetric matrix `A`. -/
noncomputable def matrixSignedGraph (A : Matrix V V ℝ) (hA : A.IsSymm) : SignedGraph V where
  graph := matrixGraph A hA
  sign := Sym2.lift ⟨fun u v => if 0 < A u v then 1 else -1, by
    intro u v
    have hsym : A u v = A v u := congrFun (congrFun hA v) u
    simp [hsym]⟩
  sign_pm_one := by
    intro e _
    rcases e with ⟨u, v⟩
    simp only [Sym2.lift_mk]
    split_ifs <;> simp

/-- A real symmetric matrix `A` is NOC if its underlying signed graph is NOC. -/
def MatrixIsNOC (A : Matrix V V ℝ) (hA : A.IsSymm) : Prop :=
  IsNOC (matrixSignedGraph A hA)

/-- Count of simple cycle edge-sets of length congruent to `r (mod 4)`. -/
noncomputable def cycleCountModFour [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ZMod 4) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset (Sym2 V) =>
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S ∧ (c.length : ZMod 4) = r).card

end SignedGraphDefs

end SignedGraphs
