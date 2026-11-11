/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphStationary.StationaryLaw
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The stationary weighted graph Laplacian

This module identifies `weightedLaplacian` with the combinatorial Laplacian scaled by the
reciprocal of twice the graph volume, and with zero when the volume vanishes. It proves
symmetry, positive semidefiniteness, and zero row sums. Matrix positivity is treated in
[Bhatia1997].

## Main statements

* `weightedLaplacian_eq_smul`: the scaling identity for nonzero volume.
* `g1`: symmetry, positive semidefiniteness, and zero row sums.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
open Qatlib.Concepts.GraphStationary.StationaryLaw

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open Qatlib.Concepts.GraphEnergy.ZeroEnergy Qatlib.Concepts.GraphStationary.StationaryLaw
open Matrix
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in

/-- The real degree used for lazy graph kernels is the real coercion of Mathlib's graph degree. -/
lemma degree_eq_mathlib (x : V) : degree G x = (G.degree x : ℝ) :=
  (G.degree_eq_sum_if_adj (R := ℝ) x).symm

/-- A real combinatorial Laplacian entry is the degree on the diagonal, minus one on an edge,
and zero elsewhere. -/
lemma lapMatrix_apply (x y : V) :
    G.lapMatrix ℝ x y = if x = y then (G.degree x : ℝ) else if G.Adj x y then -1 else 0 := by
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply, diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · by_cases hadj : G.Adj x y
    · simp [hxy, hadj]
    · simp [hxy, hadj]

/-- The stationary weighted Laplacian is zero when graph volume is zero. -/
lemma weightedLaplacian_of_volume_zero (hv : volume G = 0) : weightedLaplacian G = 0 := by
  ext x y
  have hx : degree G x = 0 := degree_eq_zero_of_volume_eq_zero G hv x
  simp [weightedLaplacian, kernel, hx]

/-- For nonzero graph volume, the stationary weighted Laplacian is the combinatorial Laplacian
scaled by `1 / (2 * volume G)`. -/
lemma weightedLaplacian_eq_smul (hv : volume G ≠ 0) :
    weightedLaplacian G = (1 / (2 * volume G)) • G.lapMatrix ℝ := by
  ext x y
  rw [Matrix.smul_apply, smul_eq_mul, lapMatrix_apply]
  by_cases hx : degree G x = 0
  · have hnx : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hx y
    have hdeg : (G.degree x : ℝ) = 0 := by rw [← degree_eq_mathlib, hx]
    by_cases hxy : x = y
    · subst hxy
      simp [weightedLaplacian, stationary, kernel, hv, hx, hdeg]
    · simp [weightedLaplacian, stationary, kernel, hv, hx, hxy, hnx]
  · have hdeg : (G.degree x : ℝ) = degree G x := (degree_eq_mathlib G x).symm
    have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    have hxpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
    by_cases hxy : x = y
    · subst hxy
      simp [weightedLaplacian, stationary, kernel, hv, hx, hdeg]
      field_simp [hvpos.ne', hxpos.ne']
      ring
    · by_cases hadj : G.Adj x y
      · simp [weightedLaplacian, stationary, kernel, hv, hx, hxy, hadj]
        field_simp [hvpos.ne', hxpos.ne']
      · simp [weightedLaplacian, stationary, kernel, hv, hx, hxy, hadj]

/-- Each row of the real combinatorial Laplacian sums to zero. -/
lemma row_of_lap (x : V) : ∑ y, G.lapMatrix ℝ x y = 0 := by
  have h := congr_fun (G.lapMatrix_mulVec_one_eq_zero ℝ) x
  simpa [mulVec, dotProduct, Finset.sum_mul, mul_one] using h

/-- Each row of the stationary weighted Laplacian sums to zero. -/
lemma row_of_weighted [Nonempty V] (x : V) : ∑ y, weightedLaplacian G x y = 0 := by
  by_cases hv : volume G = 0
  · simp [weightedLaplacian_of_volume_zero G hv]
  · rw [weightedLaplacian_eq_smul G hv]
    (try simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, row_of_lap, mul_zero])

/-- The stationary weighted Laplacian is symmetric. -/
lemma symm_weighted [Nonempty V] : (weightedLaplacian G).IsSymm := by
  by_cases hv : volume G = 0
  · rw [weightedLaplacian_of_volume_zero G hv]
    exact isSymm_zero
  · rw [weightedLaplacian_eq_smul G hv]
    exact (G.isSymm_lapMatrix ℝ).smul _

/-- The stationary weighted Laplacian is positive semidefinite. -/
lemma posSemidef_weighted [Nonempty V] : (weightedLaplacian G).PosSemidef := by
  by_cases hv : volume G = 0
  · rw [weightedLaplacian_of_volume_zero G hv]
    exact PosSemidef.zero
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    rw [weightedLaplacian_eq_smul G hv]
    exact (G.posSemidef_lapMatrix ℝ).smul (by positivity : 0 ≤ 1 / (2 * volume G))

/-- For a finite graph with nonempty vertex type, the stationary weighted Laplacian is symmetric
and positive semidefinite, and each row sums to zero. -/
theorem g1 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (weightedLaplacian G).IsSymm ∧ (weightedLaplacian G).PosSemidef ∧
      (∀ x, ∑ y, weightedLaplacian G x y = 0) := by
  intro V _ _ _ G _
  exact ⟨symm_weighted G, posSemidef_weighted G, row_of_weighted G⟩

end Qatlib.Concepts.GraphLaplacian.LaplacianPsd
