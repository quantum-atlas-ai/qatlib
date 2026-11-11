/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceDefs
import Qatlib.Papers.QConvexOpt18.MainResults.FiniteDiff.SourceFiniteDiff

set_option backward.isDefEq.respectTransparency false

/-!
# QConvexOpt18 Definition 8 as the `m = 1` central difference of `GradientOracle.CentralDiff`

van Apeldoorn--Gilyén--Gribling--de Wolf, fixed arXiv:1809.00643v4
(accepted in Quantum 2019-12-03), Definition 8.

The Frozen block `QuantumAlgorithm.Concepts.GradientOracle.CentralDiff` carries the degree-`2m`
central-difference stencil `centralDiffApply m` of arXiv:1711.00465v3 Definition 7, which the paper
under review cites as `[GAW19]`. At `m = 1` that stencil is exactly the paper's two-point
difference, so Definition 8 is not new mathematics:

* `centralDiffApply_one_eq` evaluates the Frozen stencil at `m = 1` as `(F y - F (-y)) / 2`;
* `finDiffGradCoord_eq_centralDiff` transports the paper's coordinate `∇ᵢ^(r) f (z)` into it across
  the linear isometry `EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ)`,
  recovering `∇ᵢ^(r) f (z) = centralDiffApply 1 F (r • eᵢ) / r`.

This is the representation bridge that lets this Paper block consume the already built stencil
instead of restating it.

Boundary: only the identification of the two definitions. It adds no bound on the stencil and no
statement about the higher-`m` members, which belong to `QGradient17`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QConvexOpt18.MainResults

open Qatlib.Concepts.GradientOracle.CentralDiff

/-- The degree-`2m` central-difference stencil `centralDiffApply` of the Frozen
`GradientOracle.CentralDiff` block at `m = 1` is the paper's two-point difference
`(F y - F (-y)) / 2`. -/
theorem centralDiffApply_one_eq {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    centralDiffApply 1 F y = (F y - F (-y)) / 2 := by
  have hset : Finset.Ico (-↑(1 : ℕ) : ℤ) (↑(1 : ℕ) + 1) = ({-1, 0, 1} : Finset ℤ) := by decide
  simp only [centralDiffApply, hset]
  norm_num [centralDiffCoeff]
  ring

/-- Definition 8 of arXiv:1809.00643v4 in a general direction `y`: the Frozen degree-`2m`
central-difference stencil at `m = 1`, divided by `r`, is the paper's two-point finite difference
`(F (w + r y) - F (w - r y)) / (2 r)`. Taking `y = eᵢ` recovers `∇ᵢ^(r) f (w)`. -/
theorem centralDiff_stencil_div_eq_finDiff {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (w y : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    centralDiffApply 1 (fun u => F (w + u)) (r • y) / r =
      (F (w + r • y) - F (w - r • y)) / (2 * r) := by
  rw [centralDiffApply_one_eq]
  have h : w + -(r • y) = w - r • y := by abel
  rw [h]
  field_simp

end Qatlib.Papers.QConvexOpt18.MainResults
