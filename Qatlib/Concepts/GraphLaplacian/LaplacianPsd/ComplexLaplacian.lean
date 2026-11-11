/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Positive semidefiniteness of the complex graph Laplacian

This module compares the complex and real combinatorial Laplacians. Splitting a complex vector
into real and imaginary parts expresses the real part of its Laplacian energy as a sum of real
energies and proves `complex_laplacian_posSemidef`. The matrix positivity background is given in
[Bhatia1997].

## Main statements

* `complex_laplacian_energy_re`: the real and imaginary energy decomposition.
* `complex_laplacian_posSemidef`: positivity of the complex Laplacian.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Qatlib.Concepts.GraphLaplacian.LaplacianPsd

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every entry of the complex graph Laplacian is the complex coercion of the corresponding real
Laplacian entry. -/
theorem complex_laplacian_entry (i j : V) :
    G.lapMatrix ℂ i j = ((G.lapMatrix ℝ i j : ℝ) : ℂ) := by
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- The real part of the complex Laplacian quadratic form is the sum of the real Laplacian
quadratic forms of the real and imaginary parts. -/
theorem complex_laplacian_energy_re (z : V → ℂ) :
    (star z ⬝ᵥ (G.lapMatrix ℂ *ᵥ z)).re =
      (fun i => (z i).re) ⬝ᵥ (G.lapMatrix ℝ *ᵥ (fun i => (z i).re)) +
      (fun i => (z i).im) ⬝ᵥ (G.lapMatrix ℝ *ᵥ (fun i => (z i).im)) := by
  have hre (f : V → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  have him (f : V → ℂ) : (∑ i, f i).im = ∑ i, (f i).im :=
    map_sum Complex.imAddGroupHom f Finset.univ
  simp only [dotProduct, Matrix.mulVec]
  rw [hre, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.star_apply, complex_laplacian_entry, hre, him, Complex.mul_re, Complex.mul_im]

/-- The combinatorial Laplacian over the complex numbers is positive semidefinite. -/
theorem complex_laplacian_posSemidef : (G.lapMatrix ℂ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (G.isHermitian_lapMatrix ℂ)
  intro z
  apply RCLike.nonneg_iff.mpr
  constructor
  · rw [show RCLike.re (star z ⬝ᵥ (G.lapMatrix ℂ *ᵥ z)) =
      (star z ⬝ᵥ (G.lapMatrix ℂ *ᵥ z)).re from rfl, complex_laplacian_energy_re]
    have hr := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (fun i => (z i).re)
    have hi := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (fun i => (z i).im)
    simpa only [star_trivial] using add_nonneg hr hi
  · exact (G.isHermitian_lapMatrix ℂ).im_star_dotProduct_mulVec_self z

end Qatlib.Concepts.GraphLaplacian.LaplacianPsd
