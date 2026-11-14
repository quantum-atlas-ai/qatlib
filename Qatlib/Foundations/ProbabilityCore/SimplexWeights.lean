/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Convex.Basic

/-!
# Finite probability weights in a function space

`weights` is the set of coordinate functions that are nonnegative and sum to
one. This presentation supports pointwise linear maps and minimax arguments.
`weights_eq_range` identifies the real domain with the weight vectors of
Mathlib's `Convexity.StdSimplex`; the remaining lemmas establish compactness,
convexity, and membership of point masses under their stated assumptions.
-/

@[expose] public section

open scoped BigOperators

namespace Qatlib.Foundations.ProbabilityCore.SimplexWeights

/-- Nonnegative coordinate functions on a finite index type whose sum is one. -/
def weights (R : Type*) (ι : Type*) [Semiring R] [PartialOrder R] [Fintype ι] : Set (ι → R) :=
  { f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 }

/-- Real probability vectors are exactly the weight vectors of Mathlib's
standard simplex. -/
theorem weights_eq_range (ι : Type*) [Fintype ι] :
    weights ℝ ι = Set.range (fun p : Convexity.StdSimplex ℝ ι => (p.weights : ι → ℝ)) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext f
  simp [weights]

/-- Finite probability vectors form a compact subset of their coordinate space
under the stated ordered topological ring assumptions. -/
theorem weights_compact (R : Type*) (ι : Type*) [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R]
    [OrderClosedTopology R] [Fintype ι] : IsCompact (weights R ι) := by
  have hrange : weights R ι = Set.range
      (fun p : Convexity.StdSimplex R ι => (p.weights : ι → R)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext f
    simp [weights]
  rw [hrange]
  exact isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights R ι).continuous

/-- Convex combinations preserve nonnegative coordinates and total weight one. -/
theorem weights_convex (R : Type*) (ι : Type*) [CommRing R] [PartialOrder R]
    [IsOrderedRing R] [Fintype ι] : Convex R (weights R ι) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i)), ?_⟩
  change ∑ i, (a * f i + b * g i) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2]
  simpa using hab

/-- Concentrating all weight at one index gives a probability vector. -/
theorem single_mem_weights (R : Type*) {ι : Type*} [Semiring R] [PartialOrder R]
    [ZeroLEOneClass R] [Fintype ι] [DecidableEq ι] (i : ι) :
    Pi.single i 1 ∈ weights R ι := by
  constructor
  · intro j
    by_cases h : j = i <;> simp [h]
  · simp

end Qatlib.Foundations.ProbabilityCore.SimplexWeights
