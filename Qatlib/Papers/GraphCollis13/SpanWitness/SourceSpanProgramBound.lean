/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm.SourceTreewidthAlgorithm
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4 — span-program bound for graph collision

Fixed arXiv:1305.1021v1, §3.2, Theorem 4, page 5:

`Q(COL(G)) = O(√|V(G)| + √α**(G))`, where

`α**(G) := min over vertex covers VC of max over independent I ⊆ VC of Σ_{v ∈ I} deg v`.

Source route (§3.2, pages 4-5): for a vertex cover `VC`, use the span program with
Hilbert space `span{|0⟩} ∪ {|v⟩ : v ∈ VC}`, target `|0⟩`, available vectors
`|0⟩ - |v⟩` (when `x_v = 1`) and `|v⟩` (when `x_v = 1` for some neighbour of `v`).
A positive witness on a collision edge `(v, v')` with `v ∈ VC` is
`1·(|0⟩ - |v⟩) + 1·|v⟩ = |0⟩`, of squared norm `2`, so `wsize1(P) ≤ 2`.
The negative witness is `w = |0⟩ + Σ_{v ∈ VC, x_v = 1} |v⟩`; in the negative
instance the vertices of `VC` with `x_v = 1` form an independent set, which gives
`wsize0(P) ≤ |V(G)| + α**(G)`.  Hence
`wsize(P) = √(wsize0·wsize1) ≤ √(2(|V| + α**))`, and Reichardt's Theorem 3
(`Q(f) ≤ c·wsize(f)`) yields Theorem 4.

Formalized here: the vertex-cover / independent-set combinatorics (the step that
bounds the negative-witness count by `α**`), the `α** ≤ α*` remark of the paper,
and the real-arithmetic step `√(2(n + α**)) ≤ 2√2(√n + √α**)`.  The span
program itself, its witness sizes, and the constant of Reichardt's Theorem 3 are
outside the scope of this file.  The final statement is a `Prop`-valued
definition whose proof is not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphCollis13.SpanWitness.SpanProgramBound

open scoped BigOperators
open Qatlib.Papers.GraphCollis13.QueryBound.Model
open Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm

variable {n : ℕ}

/-- A finite vertex cover: every edge has at least one endpoint in `C`. -/
def IsCover (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : Prop :=
  ∀ ⦃v w : Fin n⦄, G.Adj v w → v ∈ C ∨ w ∈ C

/-- The whole vertex set is a vertex cover. -/
theorem isCover_univ (G : SimpleGraph (Fin n)) : IsCover G Finset.univ := by
  intro v w _
  exact Or.inl (Finset.mem_univ v)

/-- The degree of `v`, as the number of neighbours in `G`. -/
def deg (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The paper's `D` for a fixed vertex cover: the maximum of `Σ_{v∈I} deg v` over
independent subsets `I ⊆ C`.  With `C = univ` this is the paper's `α*(G)`. -/
def coverWitnessBound (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter
      (fun I : Finset (Fin n) => I ⊆ C ∧ G.IsIndepSet I)).sup (fun I => ∑ v ∈ I, deg G v)

/-- The set of values `D(VC)` over all vertex covers `VC`. -/
def coverValueSet (G : SimpleGraph (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun C : Finset (Fin n) => IsCover G C)).image
    (coverWitnessBound G)

/-- The value set of `D(VC)` is nonempty because the whole vertex set is a cover. -/
theorem coverValueSet_nonempty (G : SimpleGraph (Fin n)) : (coverValueSet G).Nonempty := by
  classical
  refine ⟨coverWitnessBound G Finset.univ, ?_⟩
  exact Finset.mem_image.mpr
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isCover_univ G⟩, rfl⟩

/-- `α**(G)`: the minimum of `D(VC)` over vertex covers (arXiv:1305.1021v1, §3.2,
page 5). -/
def alphaStarStar (G : SimpleGraph (Fin n)) : ℕ :=
  (coverValueSet G).min' (coverValueSet_nonempty G)

/-- `α**(G)` is at most `D(VC)` for every vertex cover `VC`. -/
theorem alphaStarStar_le (G : SimpleGraph (Fin n)) (C : Finset (Fin n))
    (hC : IsCover G C) : alphaStarStar G ≤ coverWitnessBound G C := by
  classical
  unfold alphaStarStar
  have hmem : coverWitnessBound G C ∈ coverValueSet G :=
    Finset.mem_image.mpr
      ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ C, hC⟩, rfl⟩
  exact (Finset.isLeast_min' (coverValueSet G) (coverValueSet_nonempty G)).2 hmem

/-- The paper's remark (page 5): `α**(G) ≤ α*(G)`, obtained by taking the whole
vertex set as the cover. -/
theorem alphaStarStar_le_alphaStar (G : SimpleGraph (Fin n)) :
    alphaStarStar G ≤ coverWitnessBound G Finset.univ :=
  alphaStarStar_le G Finset.univ (isCover_univ G)

/-- In a negative instance (no collision), the `x_v = 1` vertices inside a vertex
cover form an independent set.  This is the combinatorial fact behind the bound
`wsize0 ≤ |V| + α**`. -/
theorem filter_true_indep (G : SimpleGraph (Fin n)) (x : Fin n → Bool)
    (C : Finset (Fin n))
    (hno : ¬ ∃ v w : Fin n, G.Adj v w ∧ x v = true ∧ x w = true) :
    G.IsIndepSet (C.filter (fun v => x v = true)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw _ hAdj
  exact hno ⟨v, w, hAdj, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hw).2⟩

/-- The degree sum over the `x_v = 1` vertices of a vertex cover is bounded by
`D(VC)`.  This is the counting step of the negative-witness estimate. -/
theorem sum_deg_le_coverWitnessBound (G : SimpleGraph (Fin n)) (x : Fin n → Bool)
    (C : Finset (Fin n)) (hC : IsCover G C)
    (hno : ¬ ∃ v w : Fin n, G.Adj v w ∧ x v = true ∧ x w = true) :
    ∑ v ∈ C.filter (fun v => x v = true), deg G v ≤ coverWitnessBound G C := by
  classical
  unfold coverWitnessBound
  refine Finset.le_sup (f := fun I => ∑ v ∈ I, deg G v) ?_
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Finset.filter_subset _ _, filter_true_indep G x C hno⟩

/-- `√(x + y) ≤ √x + √y` for nonnegative reals. -/
theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- The real-arithmetic step of Theorem 4:
`√(2(n + α**)) ≤ 2√2 (√n + √α**)`. -/
theorem witness_arith (n D : ℕ) :
    Real.sqrt (2 * ((n : ℝ) + (D : ℝ))) ≤
      2 * Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have h1 : Real.sqrt (2 * ((n : ℝ) + (D : ℝ))) =
      Real.sqrt 2 * Real.sqrt ((n : ℝ) + (D : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt ((n : ℝ) + (D : ℝ)) ≤ Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ) :=
    sqrt_add_le hn hD
  have hs : 0 ≤ Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ) := by positivity
  have hstep : Real.sqrt 2 * Real.sqrt ((n : ℝ) + (D : ℝ)) ≤
      Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
  have hstep2 : Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ)) ≤
      2 * Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (D : ℝ)) := by
    have hle : Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    exact mul_le_mul_of_nonneg_right hle hs
  exact h1.le.trans (hstep.trans hstep2)

/-- The witness-size bound obtained for a fixed vertex cover: the paper's
`wsize(P) ≤ √(2(|V| + D(VC)))` implies the query bound with the constant `2√2`
(absorbing Reichardt's constant into the `O`). -/
theorem span_program_witness_bound (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) :
    Real.sqrt (2 * ((n : ℝ) + (coverWitnessBound G C : ℝ))) ≤
      2 * Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (coverWitnessBound G C)) :=
  witness_arith n (coverWitnessBound G C)

/-- **Statement only — not proved in Qatlib.** **Theorem 4 (arXiv:1305.1021v1, page 5).**  There is a universal constant `C`
such that graph collision on any graph satisfies
`Q(COL(G)) ≤ C·(√|V(G)| + √α**(G))`.

The constant is uniform in the graph, which is the content of the paper's `O(·)`.
The proof combines the span program of §3.2 (`wsize1 ≤ 2`, `wsize0 ≤ |V| + α**`,
the latter via `sum_deg_le_coverWitnessBound`) with Reichardt's Theorem 3.

Scope note: this file formalizes the combinatorial and real-arithmetic estimates.
The span-program construction, its witness-size estimates, and Reichardt's
span-program-to-query-complexity reduction are outside its scope.
The span program can be represented over `EuclideanSpace ℂ (Option (Fin n))`
with availability sets as in §3.1.  The positive witness `|0⟩` gives
`wsize1 ≤ 2`, and `sum_deg_le_coverWitnessBound` supplies the combinatorial
estimate for `wsize0 ≤ n + α**`. -/
def theorem4_span_program_bound_statement : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      ∃ q : ℕ, GraphCollisionQueryUpperBound adj q ∧
        (q : ℝ) ≤ C * (Real.sqrt (n : ℝ) + Real.sqrt (alphaStarStar (adjGraph adj)))

end Qatlib.Papers.GraphCollis13.SpanWitness.SpanProgramBound
