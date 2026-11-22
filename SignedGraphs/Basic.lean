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
  exact ⟨fun _ => trivial, fun _ => lt_trichotomy 0 (hA.eigenvalues i) |>.imp_right
    (fun h => h.elim (fun heq => heq.symm) id) |>.assoc.mp |> fun _ => by
      rcases lt_trichotomy 0 (hA.eigenvalues i) with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h⟩

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

/-- Underlying simple graph of a real symmetric zero-diagonal matrix `A`. -/
def matrixGraph (A : Matrix V V ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ A u v ≠ 0
  symm u v h := ⟨h.1.symm, by sorry⟩
  loopless u h := h.1 rfl

/-- Underlying signed graph `(G(A), σ_A)` of a real symmetric zero-diagonal matrix `A`. -/
noncomputable def matrixSignedGraph (A : Matrix V V ℝ) (hA : A.IsSymm) : SignedGraph V where
  graph := matrixGraph A
  sign := Sym2.lift ⟨fun u v => if 0 < A u v then 1 else -1, by
    intro u v
    have hsym : A u v = A v u := congrFun (congrFun hA v) u
    simp [hsym]⟩
  sign_pm_one := by
    intro e _
    rcases e with ⟨u, v⟩
    simp only [Sym2.lift_mk]
    split_ifs <;> simp

/-- A real symmetric zero-diagonal matrix `A` is NOC if its underlying signed graph is NOC. -/
def MatrixIsNOC (A : Matrix V V ℝ) (hA : A.IsSymm) : Prop :=
  IsNOC (matrixSignedGraph A hA)

/-- Count of simple cycles of length congruent to `r (mod 4)` (represented as unordered cycles). -/
noncomputable def cycleCountModFour [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ZMod 4) : ℕ :=
  (Finset.univ.filter fun p : Σ v : V, {c : G.Walk v v // c.IsCycle ∧ (c.length : ZMod 4) = r}).card / 2
  -- Note: canonical unoriented cycle count is handled cleanly in Challenge.lean via Sym2 edge sets.

end SignedGraphDefs

end SignedGraphs
